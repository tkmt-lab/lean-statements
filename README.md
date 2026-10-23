# Lean statements from published papers

Nine Lean files containing 18 theorem statements from three published research
repositories. The files preserve their definitions, namespaces, hypotheses and types.
Each theorem body is intentionally `by sorry`. A `formal_proof` attribute points to
the corresponding proof at a fixed public commit.

The collection is for Lean users and automated readers who want to import a
statement, inspect its assumptions or find its proof. It contains statements and
metadata, not the proof closures. Elaborating a `sorry` statement does not establish
its truth or check the linked proof.

## Contents

| File | Statements | Scope |
|---|---:|---|
| [A3](FormalConjectures/Paper/A3.lean) | 1 | Two-stage classification with `0 < l < k` |
| [AffineRays](FormalConjectures/Paper/AffineRays.lean) | 1 | Formal eventual-periodicity statement under `Valid` and `TrianglesInCharts` |
| [K3](FormalConjectures/Paper/K3.lean) | 1 | Eventual periodicity on all positive-domain rays |
| [C1](FormalConjectures/Paper/C1.lean) | 2 | Classification and eventual periodicity on positive-domain rays |
| [O2](FormalConjectures/Paper/O2.lean) | 2 | Absence when both parameters are at least two, and eventual periodicity on rays |
| [D14](FormalConjectures/Paper/D14.lean) | 1 | Eventual periodicity on positive-domain rays |
| [E10](FormalConjectures/Paper/E10.lean) | 2 | Classification for `r ≥ 2`; eventual periodicity on rays also includes `r = 1` |
| [Heesch](FormalConjectures/Paper/Heesch.lean) | 6 | Conditional Hh/Hc CNF soundness on square, hexagon and triangle grids |
| [D12](FormalConjectures/Paper/D12.lean) | 2 | Classification for `r,s ≥ 1`, and eventual periodicity on all positive-domain rays |

[claims.json](claims.json) lists each declaration, its Lean statement, its own scope
and its public proof location. Shared file scopes are listed separately in `file_scopes`.
[manifest.json](manifest.json) records source commits and hashes.
[CORRESPONDENCE.md](CORRESPONDENCE.md) maps the source and local declarations.

## Build a checkout

Requirements: Git, Python 3.11 or later, and [elan](https://github.com/leanprover/elan).
The checking scripts support macOS and Linux. The pinned toolchain is Lean 4.35.0,
with Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

From the repository root:

```sh
python3 -B tools/check.py --static-only
python3 -B tools/check_claims.py
lake exe cache get
lake build
```

The cache command obtains the pinned dependencies and their prebuilt Mathlib files.
It needs network access. The lock file fixes dependency revisions. A cache download
failure is not a theorem failure; resolve it before building rather than silently
changing the toolchain or dependency revision.

`lake build` compiles all nine files as separate modules. Lake's `needs` dependencies
order the modules, so the files' repeated namespaces are never imported into one
Lean environment. Each compiler uses one thread and `-M3072`. Warnings that the
18 theorem declarations use `sorry` are expected.

For a monitored build using dependencies that are already cached:

```sh
python3 -B tools/build.py --evidence .build/build-check
```

This first runs `lake --no-build` on the dependency cache, then `lake build`. It
refuses to start alongside another Lean process, limits its own process group to
4 GiB sampled RSS and 15 minutes per command, and uses `nice 10`. It neither
installs dependencies nor stops another task's process. Its JSON result lists the
nine built modules and their hashes.

The Ubuntu workflow installs elan, obtains the Mathlib cache and runs the static
checks and monitored build, with a 15-minute job timeout. A timeout is a failed
check, not evidence about a theorem. Local verification and its limits are recorded
in [VERIFICATION-RECORD.md](VERIFICATION-RECORD.md).

## Take one statement into another project

Choose one file and read its scope and proof reference. Several files repeat the
original namespaces `ClaudeChallenge` and `Claude2Aligned`; importing them together
would create declaration conflicts. This collection does not rename or factor
those definitions.

In a matching Mathlib project, copy the chosen problem file and put `support/` on
the Lean source path. The local `FormalConjecturesUtil` facade imports only the
metadata attributes. In an existing formal-conjectures checkout, use that project's
own `FormalConjecturesUtil` instead of this facade, then check the chosen statement
against its toolchain and linters.

The upstream format snapshot uses Lean 4.33.1. Compatibility with that version and
the full upstream linter suite has not been checked. This repository is not an
official part of formal-conjectures and has not been contributed to it.

## Check correspondence with the source

The static check reverses the added header, import visibility and attributes, then
compares the reconstructed source bytes with the published file's SHA-256. It also
checks the unmodified upstream attribute files. It does not need network access.

To compare the original and local theorem types in Lean and inspect the parsed
solved/proof-link attributes, after caching dependencies:

```sh
python3 -B tools/check.py --problem D12 --evidence .build/d12-check
```

Omit `--problem D12` to check all nine files. Each original and normalized file is
elaborated in its own environment. The checker compares the serialized theorem-type
expressions. Its per-file limit is ten minutes and 3 GiB sampled RSS, with one Lean
process at a time. The default Lean memory threshold is also 3072 MiB. A full run
on macOS required higher limits for AffineRays; with enough free memory, use:

```sh
python3 -B tools/check.py --lean-memory-mib 4096 --rss-limit-mib 4608
```

These options permit up to 4 GiB for Lean's memory threshold and 4.5 GiB sampled
RSS. The checker rejects larger values and records the chosen limits in its receipt.
Detailed generated logs stay in ignored `.build/` folders.
The [public summary](checks/statement-correspondence.json) records the earlier
checks of all 18 type pairs.

## Scope of the evidence

The checks establish source correspondence, parsed metadata and successful
elaboration. They do not execute the mathematical proofs in the linked repositories,
provide a new proof or amount to human expert review. The `research solved` category
marks solved status; the separate `formal_proof` attribute records the public proof
location. The local `sorry` body remains a placeholder.

The formal affine-ray statement has explicit hypotheses. Its source paper's step
from geometric assumptions to those hypotheses is a prose correspondence lemma.
The family and Heesch statements have their own domains and conditional hypotheses;
consult the definitions and the source papers for those boundaries. This collection
does not extend them, claim a complete classification of fullerenes or compute
particular Heesch values.

## Sources and acknowledgements

The mathematical files come from the published challenge files in
[a3-gsw-classification](https://github.com/tkmt-lab/a3-gsw-classification),
[gsw-ray-periodicity](https://github.com/tkmt-lab/gsw-ray-periodicity) and
[heesch-certificates](https://github.com/tkmt-lab/heesch-certificates). Their fixed
commits and proof links are in the manifest. Each source repository gives the
mathematical references and acknowledges the prior work on which its results rely.

The [Formal Conjectures Authors](https://github.com/google-deepmind/formal-conjectures/tree/9833012f66a47cdd3a6f3eca9cb4b84e0f18a003)
provided the file format and the category, subject and proof-link attribute
implementation used here. Lean and the Mathlib contributors provide the elaborator
and mathematical library. I am grateful for their work; these acknowledgements
imply no endorsement.

Tatsuhiko Takimoto, Independent researcher, is responsible for this collection.
Claude and Codex were used to prepare statements, code, checks and documentation;
AI tools are not listed as authors of the software citation.

## License and citation

The copied Lean code and this package's code, metadata and documentation are
Apache-2.0. Original copyright notices are retained. [NOTICE](NOTICE) identifies the
two unmodified upstream attribute files and the changes made to the problem copies;
[license records](checks/license-sources.json) identify the checked source licenses.
Linked papers, datasets and dependencies retain their own licenses and are not
relicensed by this package.

Use [CITATION.cff](CITATION.cff) to cite version 1.0.0 of the collection. Cite the
corresponding source paper for a mathematical result. No paper PDF, external dataset
or proof closure is bundled here.
