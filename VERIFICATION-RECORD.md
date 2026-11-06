# Verification record

## Source and theorem-type correspondence

The [recorded summary](checks/statement-correspondence.json) covers all nine original
source files, 18 theorem-type pairs and the parsed solved/proof-link attributes.
It uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The packaging verifier performed these checks separately from the authors of the
published proofs. They establish faithful statement copying, not a new mathematical
proof. Public source commits and file hashes remain in manifest.json.

## Standalone clone, 23 October 2026

A new local Git clone had no build outputs for this package. Existing dependency
packages at the locked revisions were copied into its ignored `.lake/packages/`
folder as a cache. The copied cache had no links back to another workspace. The
run did not test downloading dependencies from the network.

The dependency preflight passed in 36.178 seconds. The following `lake build`
compiled the three metadata modules and all nine independent problem modules from
source in 71.064 seconds. It emitted the 18 expected warnings for intentional
`sorry` theorem bodies. Maximum sampled process-group RSS was 3,092,672 KiB
(about 2.95 GiB); at most one Lean process ran at a time. No resource guard fired.
[The public receipt](checks/fresh-clone-build.json) records these measurements and
the exact source hashes. Detailed logs with machine-local paths are not distributed.

The standalone checker was also run with its default local dependency path for
D12. Both original/normalized theorem types and both parsed metadata entries
matched; this took 24.723 seconds. The earlier summary supplies the recorded
comparison for the other 16 declarations.

At the time of this local preparation, the Ubuntu GitHub Actions workflow was
configured to obtain the Mathlib cache and build all nine modules within a
15-minute job timeout. It was not run as part of that preparation. The current
workflow is described below; this historical build record is not a CI run.

## Review corrections, 23 October 2026

The family summaries now say eventual periodicity. Each claim record has a scope
for its own theorem; shared file descriptions are in `file_scopes`. The solved
category and proof-link attribute are described separately, and the licensing
records for A3 and GSW point to their own licensing documents. The nine Lean files,
their 18 theorem types and proof links, and the three support modules did not change.

A cached build in the package directory compiled the three support modules and
nine problem modules from source. Dependency preflight took 43.406 seconds and
the package build 83.485 seconds, with 18 intentional `sorry` warnings. Peak
sampled process-group RSS was 3,077,664 KiB; at most one Lean process ran at a time.

The full source/local type comparison and parsed-attribute checks passed for all
18 theorem declarations. This run explicitly used
`--lean-memory-mib 4096 --rss-limit-mib 4608`; its 21 serial Lean invocations took
212.785 seconds in total,
with a peak sampled RSS of 3,164,640 KiB. Every type hash matched the earlier record.
The [receipt](checks/review-corrections.json) records the exact commands and limits.

Two earlier attempts stopped while checking AffineRays: the first exceeded the
default 3 GiB sampled RSS limit, and the second reached Lean's default 3072 MiB
memory threshold. These were resource failures, not type mismatches. At that time, the checker
defaulted to those limits and allowed explicitly requested limits up to 4096 MiB
for Lean or 4608 MiB sampled RSS. No linked proof was executed.

## Limits and CI since version 1.0.1

Version 1.0.1 retained the default 3072 MiB Lean threshold and 3072 MiB sampled
RSS limit, but raised the maximum explicitly selectable limits to 11264 MiB
and 12288 MiB respectively. The reason was a Linux run in which the original
AffineRays comparison exceeded the former limits. With the raised limits,
all nine pairs of files (18 theorem types) and their parsed metadata passed.
The largest sampled RSS was 7,372,496 KiB (about 7.03 GiB); the comparison took
146.666 seconds. These are historical measurements, not a new run for 1.0.2,
minimum memory requirements, or a guarantee for another machine.

The [Linux summary](checks/linux-correspondence.json) preserves the per-file
measurements and the limits of that record. The executed diagnostic checker
differed from the checker proposed for version 1.0.1 only in help/error text about the raised
limits. Setup records were checked, but the generated setup JSON files were
not retained, and dependency HEADs were not reread after the run. This was
a Linux test machine, not GitHub Actions.

The current workflow prepares the three support modules and compares all
18 original/local theorem types and parsed attributes, using the explicit
11264/12288 MiB limits. It also runs the static source and claim checks.
It does not run the monitored package build or the nine-module target chain.
The 15-minute job timeout remains in force. The records above do not establish
the status of a current hosted CI run.

## Version 1.0.2 preparation, 6 November 2026

In a fresh local checkout, the static source reconstruction and claim/metadata
checks passed for all nine files and 18 mappings. The mathematical files, support
modules, theorem metadata and dependency pins were unchanged from 1.0.1.
A deliberately mismatched Lake package version was rejected by the metadata check.
Five lightweight diagnostic tests covered missing dependencies and failed process
startup/preflight, including the saved FAIL result. Those tests did not run Lean.

The preparation environment had no Lean/elan installation. Fetching the official
elan installer returned HTTP 403. Consequently no new Lean build, D12 type comparison,
or hosted CI success is recorded here. The historical results above remain historical;
the Lean procedures need to be rerun in an environment with the pinned dependencies.

## Interpretation

The checks establish source correspondence, parsed metadata and successful
elaboration. They do not execute the published mathematical proof closures. The
`research solved` category marks solved status; the separate `formal_proof`
attribute links to the proof. The local theorem bodies remain `sorry`.
No independent new proof or human expert review is claimed. The upstream
Lean 4.33.1 toolchain and full formal-conjectures linter suite were not checked.
