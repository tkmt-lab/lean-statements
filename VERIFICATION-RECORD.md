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

The Ubuntu GitHub Actions workflow is configured to obtain the Mathlib cache and
build all nine modules within a 15-minute job timeout. It has not been run as part
of this local preparation. Its success and network/cache timing remain to be checked
when the repository is hosted.

## Interpretation

The checks establish source correspondence, parsed metadata and successful
elaboration. They do not execute the published mathematical proof closures. The
`research solved` attributes identify those proofs; the local theorem bodies remain
`sorry`. No independent new proof or human expert review is claimed. The upstream
Lean 4.33.1 toolchain and full formal-conjectures linter suite were not checked.
