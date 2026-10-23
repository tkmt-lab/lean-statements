#!/usr/bin/env python3
"""Check reversible source correspondence, then elaborate one Lean process at a time.

Uses the local dependency cache or an already-built matching Mathlib project. It never invokes Lake,
downloads dependencies, runs the linked proofs, or terminates another task's process.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_only_correspondence(manifest: dict) -> dict[str, bytes]:
    originals = {}
    for entry in manifest["problems"]:
        data = (ROOT / entry["file"]).read_bytes()
        assert sha(data) == entry["normalized_sha256"], entry["file"]
        text = data.decode()
        actual_imports = re.findall(r"^public import (.+)$", text, re.M)
        original_imports = re.findall(r"^import (.+)$", entry["original_import_prefix"], re.M)
        assert actual_imports == ["FormalConjecturesUtil"] + original_imports
        assert text.count(manifest["projection_marker"]) == 1
        body = text.split(manifest["projection_marker"], 1)[1]
        for attribute in entry["inserted_attributes"]:
            assert body.count(attribute) == 1, entry["file"]
            body = body.replace(attribute, "", 1)
        original = (entry["original_import_prefix"] + body).encode()
        assert sha(original) == entry["source_sha256"], entry["file"]
        assert len(original) == entry["source_bytes"]
        assert len(re.findall(r"^theorem ", body, re.M)) == entry["theorem_count"]
        for declaration in entry["declarations"]:
            name = declaration["name"].rsplit(".", 1)[1]
            match = re.search(r"^theorem " + re.escape(name) + r"\b", text, re.M)
            assert match and text[:match.start()].count("\n") + 1 == declaration["normalized_line"]
        originals[entry["id"]] = original
    for entry in manifest["support"]:
        assert sha((ROOT / entry["file"]).read_bytes()) == entry["sha256"]
        if entry.get("origin") != "local" and not entry["modified"]:
            assert entry["sha256"] == entry["upstream_sha256"]
    for file, expected in manifest.get("package_files", {}).items():
        assert sha((ROOT / file).read_bytes()) == expected, file
    return originals


def lean_pids() -> list[int]:
    rows = subprocess.check_output(["ps", "-axo", "pid=,comm="], text=True)
    return [int(row.split(None, 1)[0]) for row in rows.splitlines()
            if len(row.split(None, 1)) == 2
            and Path(row.split(None, 1)[1]).name == "lean"]


def free_percent() -> int:
    """Available-memory guard for the supported macOS and Linux environments."""
    if os.uname().sysname == "Linux":
        fields = {}
        for line in Path("/proc/meminfo").read_text().splitlines():
            key, value = line.split(":", 1)
            fields[key] = int(value.strip().split()[0])
        return 100 * fields["MemAvailable"] // fields["MemTotal"]
    output = subprocess.check_output(["memory_pressure", "-Q"], text=True)
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", output)
    if not match:
        raise RuntimeError("Cannot read available-memory precondition")
    return int(match.group(1))


def inspect_commands(entry: dict, metadata: bool) -> str:
    names = ", ".join("``" + d["name"] for d in entry["declarations"])
    text = "\nopen Lean in\nrun_cmd do\n"
    text += f"  for n in [{names}] do\n"
    text += "    let c ← getConstInfo n\n"
    text += '    let encoded := (reprStr c.type).replace "\\n" "\\\\n"\n'
    text += '    logInfo s!"STATEMENT_TYPE|{n}|{encoded}"\n'
    if metadata:
        for d in entry["declarations"]:
            name, link = d["name"], json.dumps(d["formal_proof_url"])
            text += f"  let n := ``{name}\n"
            text += "  let env ← getEnv\n"
            text += "  unless (ProblemAttributes.categoryExt.getState env).toArray.any "
            text += "(fun t => t.declName == n && t.category == .research .solved) do\n"
            text += '    throwError "Missing parsed solved metadata"\n'
            text += "  unless (ProblemAttributes.formalProofExt.getState env).toArray.any "
            text += f"(fun t => t.declName == n && t.proofKind == .lean4 && t.proofLink == {link}) do\n"
            text += '    throwError "Missing parsed public proof link"\n'
        text += '  logInfo "STATEMENT_METADATA_OK"\n'
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true")
    parser.add_argument("--problem", action="append", help="Elaborate only these manifest IDs; byte-check all files")
    parser.add_argument("--mathlib-project", type=Path, default=ROOT)
    parser.add_argument("--evidence", type=Path, default=ROOT / ".build" / "check")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "manifest.json").read_text())
    originals = read_only_correspondence(manifest)
    selected = [p for p in manifest["problems"] if not args.problem or p["id"] in args.problem]
    if args.problem and set(args.problem) != {p["id"] for p in selected}:
        parser.error("Unknown problem ID")
    print(f"PASS reversible byte correspondence: {len(originals)} sources", flush=True)
    if args.static_only:
        return
    project = args.mathlib_project.resolve()
    expected = manifest["local_toolchain"]
    assert (project / "lean-toolchain").read_text().strip() == expected["lean"]
    packages = json.loads((project / "lake-manifest.json").read_text())["packages"]
    mathlib = next(p for p in packages if p["name"] == "mathlib")
    assert mathlib["rev"] == expected["mathlib_commit"]
    cached = project / ".lake" / "packages" / "mathlib"
    assert subprocess.check_output(["git", "-C", str(cached), "rev-parse", "HEAD"],
                                   text=True).strip() == expected["mathlib_commit"]
    assert (cached / ".lake/build/lib/lean/Mathlib.olean").is_file()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    work = evidence / "raw"
    work.mkdir(exist_ok=True)
    build = ROOT / ".build/oleans"
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = expected["lean"]
    lean = subprocess.check_output(["elan", "which", "lean"], env=env, text=True).strip()
    cache_paths = [project / ".lake/packages" / p["name"] / ".lake/build/lib/lean"
                   for p in packages]
    env["LEAN_PATH"] = os.pathsep.join(map(str, [build] + [p for p in cache_paths if p.is_dir()]))
    report = {"toolchain": expected, "compiler": lean,
              "mathlib_project_read_only": str(project), "mathlib_paths": env["LEAN_PATH"],
              "constraints": {"sequential": True, "nice": 10, "lean_threads": 1,
                              "lean_memory_mib": 3072, "rss_limit_mib": 3072,
                              "per_file_timeout_seconds": 600},
              "linked_proofs_executed": False, "runs": [], "comparisons": []}

    def persist() -> None:
        (evidence / "typecheck.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, source: Path, root: Path, output: Path | None = None) -> str:
        foreign = lean_pids()
        if foreign:
            raise RuntimeError(f"Another Lean task is running: {foreign}; no concurrent launch")
        free = free_percent()
        if free < 30:
            raise RuntimeError(f"Required free memory >=30%; observed {free}%")
        command = ["nice", "-n", "10", lean, "-j1", "-M3072", "--root=" + str(root)]
        if output is not None:
            output.parent.mkdir(parents=True, exist_ok=True)
            command += ["-o", str(output)]
        command += [str(source)]
        log = work / (label + ".log")
        record = {"label": label, "command": command, "free_percent_before": free,
                  "peak_rss_kib": 0, "log": str(log), "started_unix": time.time()}
        report["runs"].append(record)
        started = time.monotonic()
        stopped = None
        with log.open("w") as handle:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=handle,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            record["pid"] = process.pid
            print(f"START {label} pid={process.pid}", flush=True)
            last_memory_check = started
            try:
                while process.poll() is None:
                    rss = subprocess.run(["ps", "-o", "rss=", "-p", str(process.pid)],
                                         text=True, capture_output=True).stdout.strip()
                    record["peak_rss_kib"] = max(record["peak_rss_kib"], int(rss or 0))
                    elapsed = time.monotonic() - started
                    if record["peak_rss_kib"] > 3072 * 1024:
                        stopped = "own RSS exceeded 3 GiB"
                    if elapsed > 600:
                        stopped = "per-file timeout"
                    if time.monotonic() - last_memory_check >= 5:
                        last_memory_check = time.monotonic()
                        if free_percent() < 10:
                            stopped = "system free memory below 10%"
                    if stopped:
                        os.killpg(process.pid, signal.SIGTERM)
                        try:
                            process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                        break
                    time.sleep(0.25)
            except BaseException:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    process.wait(timeout=5)
                raise
            record.update(exit_code=process.wait(), seconds=round(time.monotonic() - started, 3),
                          stopped=stopped)
        text = log.read_text()
        record["log_sha256"] = sha(text.encode())
        record["sorry_warnings"] = len(re.findall(r"declaration uses [`']sorry[`']", text))
        persist()
        print(f"END {label} exit={record['exit_code']} peak={record['peak_rss_kib']} KiB "
              f"seconds={record['seconds']}", flush=True)
        if record["exit_code"] or stopped:
            raise RuntimeError(f"{label} failed; see {log}")
        return text

    for module in ["FormalConjecturesUtil/Attributes/AMS", "FormalConjecturesUtil/Attributes/Basic",
                   "FormalConjecturesUtil"]:
        run("support-" + module.replace("/", "-"), ROOT / "support" / (module + ".lean"),
            ROOT / "support", build / (module + ".olean"))
    for entry in selected:
        captured = {}
        for mode in ["original", "normalized"]:
            source = originals[entry["id"]].decode() if mode == "original" else (ROOT / entry["file"]).read_text()
            source += inspect_commands(entry, mode == "normalized")
            temporary = work / (entry["id"] + "-" + mode + ".lean")
            temporary.write_text(source)
            text = run(entry["id"] + "-" + mode, temporary, work)
            types = dict(re.findall(r"STATEMENT_TYPE\|([^|\n]+)\|([^\n]+)", text))
            assert set(types) == {d["name"] for d in entry["declarations"]}, entry["id"]
            captured[mode] = types
            if mode == "normalized":
                assert "STATEMENT_METADATA_OK" in text
        for name, original_type in captured["original"].items():
            assert original_type == captured["normalized"][name], (entry["id"], name)
            report["comparisons"].append({"problem": entry["id"], "declaration": name,
                                          "lean_expr_repr_sha256": sha(original_type.encode()),
                                          "type_equal": True})
        print("PASS elaborated types and parsed attributes: " + entry["id"], flush=True)
        persist()
    report["result"] = "PASS"
    persist()
    report["selected_problem_ids"] = [p["id"] for p in selected]
    persist()
    print(f"PASS: {len(selected)} independent problem files; "
          f"{len(report['comparisons'])} original/normalized type pairs", flush=True)


if __name__ == "__main__":
    main()
