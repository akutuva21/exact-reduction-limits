# Model sketches

The Lean proof does not depend on executable Kappa or BNGL files.  The research
note itself presents the reversible-tip rules schematically rather than as a
software-validated model, and the scanner proof depends only on induced local
match structure.

This directory is intentionally documentation-only.  A future parser/runtime
verification project can add executable `.ka` and `.bngl` witnesses and prove a
bridge to `WeightedTransitionSystem` without changing the mathematical proof
modules.
