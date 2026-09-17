# Constructive extension changelog

This revision preserves the original paper formalization and adds a practical
state-sufficiency layer motivated by the discussion after the first version.

## New Lean modules

- `TaskSufficiency.lean`
  - explicit `PredictionTask`;
  - current-assay and future-law sufficiency;
  - proof-carrying current/future counterexamples;
  - injective-state positive certificate;
  - restriction monotonicity.

- `ReductionDiagnostics.lean`
  - domain-restricted macro closure;
  - exact aggregate-rate counterexample objects;
  - exact `MacroClosed <-> no counterexample` theorem;
  - bounded-domain negative results are globally sound;
  - positive domain results require a completeness inclusion proof.

- `CoordinateRepair.lean`
  - coordinate augmentation;
  - representation refinement;
  - heterogeneous feature-library interface;
  - candidate features must separate the witnessed pair;
  - finite lists of known future-law witnesses can be required to be resolved;
  - task-level predictive sufficiency is preserved by refinement.

- `ApproximateReduction.lean`
  - metric future-law error budgets;
  - aggregate-rate error budgets;
  - exact-to-approximate and tolerance-monotonicity theorems;
  - zero rate error recovers exact closure;
  - over-budget witness types;
  - sharp error certificates proving a reported epsilon is minimal.

- `Certification.lean`
  - proof-carrying `certified / counterexample / unknown` verdicts;
  - complete-domain certificates.

- `ScannerDiagnostics.lean`
  - the protected object is the entire scanner survival curve;
  - every finite local family yields an explicit future-law witness;
  - `remaining` separates the canonical failed pair;
  - `remaining` determines the entire survival curve exactly.

- `PracticalTheorems.lean`
  - stable public wrappers for the constructive layer;
  - bounded-species multiplicity coordinates are sufficient for any task once
    finiteness of the connected species type is established.

## Other changes

- generalized `DeterminesFutureLaw` so representation and law codomains can
  differ;
- added `PRACTICAL-FRAMEWORK.md` and `ELI10-PRACTICAL.md`;
- extended `README.md`, `ELI15.md`, `PROOF-PATH.md`, and `PROOF_STATUS.md`;
- added `tools/check_practical.py` and wired it into CI;
- updated `STATIC_CHECKS.txt`.

## Verification boundary

The new files pass the same structural checks as the original repository and do
not use `sorry`, `admit`, or Lean `axiom` declarations.  A Lean/Lake executable
is still unavailable in the generation container, so this revision is not
claimed to be kernel-built locally.  The included CI workflow runs `lake build`
with the pinned toolchain.
