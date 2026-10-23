# Verification record

The original/normalized source and theorem-type checks are summarized in
[checks/statement-correspondence.json](checks/statement-correspondence.json).
They cover nine source files, 18 theorem types and the parsed solved/proof-link
metadata, using Lean 4.35.0 and the pinned Mathlib revision. Those checks were
performed by the packaging verifier separately from the authors of the published
proofs. They check faithful copying, not a new mathematical proof.

A fresh-clone build of this standalone package is being prepared. This record will
be replaced by its measured result before the package is handed off. Ubuntu CI has
not run; the workflow is configured for a 15-minute timeout.

The linked mathematical proof closures and upstream Lean 4.33.1/linters were not
executed. No independent new proof or human expert review is claimed.
