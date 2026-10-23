#!/usr/bin/env python3
"""Build all nine independent statement modules with a bounded process group."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

from check import ROOT, free_percent, lean_pids


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=ROOT / ".build/lake-check")
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    before = {}
    for entry in manifest["packages"]:
        package = ROOT / ".lake/packages" / entry["name"]
        if not package.is_dir():
            raise RuntimeError("Missing prebuilt dependency: " + str(package))
        rev = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        assert rev == entry["rev"], entry["name"]
        before[entry["name"]] = rev
    report = {"result": "RUNNING", "constraints": {"lean_processes": 1, "nice": 10,
              "lean_threads": 1, "lean_memory_mib": 3072, "rss_limit_mib": 4096,
              "timeout_seconds_per_invocation": 900}, "packages": before, "runs": []}

    def persist() -> None:
        (evidence / "lake-build.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, command: list[str]) -> None:
        assert not lean_pids(), "Another Lean process is running"
        free = free_percent()
        assert free >= 30, f"System free memory {free}% is below 30%"
        log = evidence / (label + ".log")
        record = {"command": command, "cwd": str(ROOT), "free_percent_before": free,
                  "started_unix": time.time(), "peak_group_rss_kib": 0,
                  "peak_lean_processes": 0, "log": log.name}
        report["runs"].append(record)
        env = os.environ.copy()
        env.update(LEAN_NUM_THREADS="1", ELAN_TOOLCHAIN=(ROOT / "lean-toolchain").read_text().strip())
        start = time.monotonic()
        stopped = None
        with log.open("w") as handle:
            proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=handle,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            record["pid"] = proc.pid
            last_pressure = start
            try:
                while proc.poll() is None:
                    rows = subprocess.check_output(["ps", "-axo", "pid=,pgid=,rss=,comm="], text=True)
                    parsed = [r.split(None, 3) for r in rows.splitlines()]
                    own = [r for r in parsed if int(r[1]) == proc.pid]
                    leans = [r for r in parsed if Path(r[3]).name == "lean"]
                    rss = sum(int(r[2]) for r in own)
                    record["peak_group_rss_kib"] = max(record["peak_group_rss_kib"], rss)
                    record["peak_lean_processes"] = max(record["peak_lean_processes"], len(leans))
                    if len(leans) > 1 or any(int(r[1]) != proc.pid for r in leans):
                        stopped = "Concurrent or foreign Lean process observed"
                    if rss > 4096 * 1024:
                        stopped = "Own process group exceeded 4 GiB RSS"
                    if time.monotonic() - start > 900:
                        stopped = "Fifteen-minute invocation timeout"
                    if time.monotonic() - last_pressure > 5:
                        last_pressure = time.monotonic()
                        if free_percent() < 10:
                            stopped = "System free memory below 10%"
                    if stopped:
                        os.killpg(proc.pid, signal.SIGTERM)
                        try:
                            proc.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL)
                        break
                    time.sleep(0.1)
            except BaseException:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGTERM)
                    proc.wait(timeout=5)
                raise
            record.update(exit_code=proc.wait(), seconds=round(time.monotonic() - start, 3), stopped=stopped)
        record["log_sha256"] = hashlib.sha256(log.read_bytes()).hexdigest()
        persist()
        print(label, record["exit_code"], record["seconds"], record["peak_group_rss_kib"], flush=True)
        if record["exit_code"] or stopped:
            raise RuntimeError(f"{label} failed; see {log}")

    run("lake-dependency-preflight", ["nice", "-n", "10", "lake", "--no-build", "--no-cache", "build",
        "+Mathlib", "+Qq"])
    run("lake-build", ["nice", "-n", "10", "lake", "--no-cache", "build"])
    problems = json.loads((ROOT / "manifest.json").read_text())["problems"]
    outputs = {}
    for problem in problems:
        output = ROOT / ".lake/build/lib/lean" / Path(problem["file"]).with_suffix(".olean")
        assert output.is_file(), str(output)
        outputs[str(output.relative_to(ROOT))] = hashlib.sha256(output.read_bytes()).hexdigest()
    report["outputs"] = outputs
    report["result"] = "PASS"
    persist()


if __name__ == "__main__":
    main()
