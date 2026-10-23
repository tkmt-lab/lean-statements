# Entry point for a Lean reader

Read README.md, claims.json and CORRESPONDENCE.md. The repository contains nine
independent statement modules and 18 declarations. Every theorem body deliberately
uses `sorry`; the proof lives at the fixed public URL in its `formal_proof` attribute.

Checks from the repository root (Python 3.11+, macOS or Linux):
- `python3 -B tools/check.py --static-only`: reconstruct exact published source bytes.
- `python3 -B tools/check_claims.py`: check the 18 declaration/proof mappings and package metadata.
- `lake exe cache get`: obtain pinned dependencies and the Mathlib cache (network required).
- `lake build`: elaborate the nine modules independently in a dependency-ordered chain.
- `python3 -B tools/build.py --evidence .build/build-check`: monitored cached build, one Lean process.
- `python3 -B tools/check.py --problem D12`: compare original and normalized theorem types and inspect attributes; omit `--problem` for all files.

Success is exit code 0. The static checks print PASS. Monitored build/type-check JSON
receipts have `result: PASS`; the warnings about intentional `sorry` declarations
are expected. Missing dependencies, a hash mismatch or a resource limit is a failed
or incomplete check, never a theorem refutation.

Use one problem file at a time. Several preserve the same original namespaces;
do not create an umbrella module importing all nine. Do not change definitions or
hypotheses to make a build pass. If adapting a statement to another toolchain or
namespace, document the adaptation and check it separately.

Do not infer that successful elaboration proves a theorem, that this package reruns
the linked proofs, that it is endorsed by or contributed to formal-conjectures, or
that it supplies a new independent proof or human expert review. The scope of each
mathematical claim remains the scope of its source paper and explicit Lean statement.

Keep generated dependencies, detailed logs and local paths in ignored work folders.
Preserve licenses, attribution, source pins and the distinction between statement
correspondence and proof verification.
