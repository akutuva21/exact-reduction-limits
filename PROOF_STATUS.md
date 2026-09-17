# Proof status

This file is intentionally conservative.  It distinguishes three things:

1. **Lean source implemented**: a theorem/proof term is present with no
   `sorry`, `admit`, or declared `axiom`.
2. **Classical interface**: the paper reuses a theorem from another mathematical
   literature and this repository represents it as an explicit structure field.
3. **Kernel verified**: `lake build` has actually succeeded with the pinned
   toolchain.

Only (1) was available in the generation environment.  The environment had no
Lean or Lake executable and no network path from the shell to install one, so no
local kernel-build claim is made.  CI is included to perform (3).

## Internally implemented paper-specific core

| Component | Main source | Status |
|---|---|---|
| Observation/reduction logical definitions | `Core.lean` | Lean source |
| Rule-match generator and macro hazards | `RuleSemantics.lean` | Lean source |
| Aggregate macro-rate criterion | `MacroCriterion.lean` | Lean source |
| Deep-interior finite-local scanner witness | `Scanner.lean` | Lean source |
| Exact Erlang successive-order separation | `Scanner.lean` | Lean source |
| Scanner uniform exit-rate bound | `Scanner.lean` | Lean source |
| Erlang coefficient triangular independence | `Scanner.lean` | Lean source |
| Scanner-seed recurrence solution | `ScannerSeed.lean` | Lean source |
| Exact quadratic/two-phase transform factorization | `ScannerSeed.lean` | Lean source |
| Reversible-tip characteristic quadratic | `ReversibleTip.lean` | Lean source |
| Physical root `ρ(0)=1` | `ReversibleTip.lean` | Lean source |
| Reversible-tip rate bound | `ReversibleTip.lean` | Lean source |
| Rational-transform contradiction schema | `LinearRealization.lean` | Lean source |
| Nonhalting detector pole locations/distinctness | `Detector.lean` | Lean source |
| Bounded-species multiplicity injection | `BoundedComplex.lean` | Lean source |
| INC/JZDEC counter semantics and exact zero test | `CounterMachine.lean` | Lean source |
| Scanner finite-depth refinement sharpness | `Refinement.lean` | Lean source |
| Abstract omega fixed-point/coarseness step | `Refinement.lean` | Lean source |
| Generic many-one undecidability transfer | `Core.lean` | Lean source |
| Seed-reduction promise certificate and transfer | `Undecidability.lean` | Lean source |
| Reusable-reduction promise certificate and transfer | `Undecidability.lean` | Lean source |
| Reusable reduction global max-rate bound | `Undecidability.lean` | Lean source |
| Task-relative predictive sufficiency | `TaskSufficiency.lean` | Lean source |
| Current/future counterexample refutation | `TaskSufficiency.lean` | Lean source |
| Macro-rate counterexample equivalence | `ReductionDiagnostics.lean` | Lean source |
| Complete-domain closure transfer | `ReductionDiagnostics.lean` | Lean source |
| Counterexample-guided coordinate separation | `CoordinateRepair.lean` | Lean source |
| Metric future-law epsilon sufficiency | `ApproximateReduction.lean` | Lean source |
| Aggregate-rate epsilon closure and zero-error theorem | `ApproximateReduction.lean` | Lean source |
| Proof-carrying three-way certification API | `Certification.lean` | Lean source |
| Scanner local-family diagnostic and remaining-coordinate repair | `ScannerDiagnostics.lean` | Lean source |

## Explicit background interfaces

These are not smuggled in as global axioms.  They are fields of structures in
`ClassicalInterfaces.lean`, so any theorem depending on them must receive a
witness explicitly.

### Probability / CTMC theory

- existence/path-law semantics of stable conservative countable CTMCs;
- the small-time aggregate expansion of Appendix C.1 for an infinite target set;
- finite-measure continuity from above used in Proposition B.1;
- identification of strong lumpability with the rule-level macro-rate criterion.

### Queueing / analysis

- the unique-tip length process is the classical stable M/M/1 busy period;
- the Takacs completion transform is non-rational;
- finite-dimensional matrix-exponential Laplace transforms are rational;
- the Bessel-function density and `t^{-3/2}` tail asymptotic;
- density of phase-type distributions;
- the compactness argument that bounded phase order cannot converge to the
  busy-period law.

### Graph rewriting / Kappa and BNGL

- full Kappa site-graph syntax and embedding-count semantics;
- the disconnected-pattern overlap/gluing polynomial identity;
- the bridge from finite ordinary patterns to bounded-radius deep-interior
  observables;
- parser/runtime equivalence to the corresponding BNGL/NFsim constructs;
- finite-signature + bounded-complex-size enumeration up to graph isomorphism;
- compilation of the numeric two-counter invariant to concrete ordinary-Kappa
  graph rules.

### Computability

- undecidability of halting for the designated all-zero CM2 family.

## Why this boundary is deliberate

The paper itself labels many of these ingredients as classical background.  A
formalization that simply writes them as `axiom`s would look complete while
hiding its trust assumptions.  This repository instead makes each boundary an
ordinary Lean value that must be supplied.

A fully closed formal proof would require separate projects for substantial
parts of countable CTMC probability, queueing analysis, phase-type approximation,
Kappa graph semantics, and the specific CM2 undecidability theorem.  Those are
valid future extensions, but they are not necessary to expose or mechanically
check the new logical architecture of this paper.

## Mechanical checks included

`tools/prelint.py` checks:

- every local Lean import resolves;
- the local import graph is acyclic;
- every local module is reachable from the umbrella target;
- the Lake glob list matches the source modules;
- no `sorry`, `admit`, or Lean `axiom` declaration appears in source.

`tools/check_coverage.py` checks that every paper result tracked in
`PAPER-COVERAGE.md` has a corresponding Lean symbol or explicit interface
marker.

`tools/check_practical.py` checks that the constructive extension contains the
task, witness, repair, approximation, certification, and scanner-example
interfaces described in `PRACTICAL-FRAMEWORK.md`.

GitHub Actions runs all three checks and then the pinned Lean/Mathlib build.
