# Exact reduction limits for Kappa/BNGL in Lean

This repository uses Lean 4 to formalize the mathematical architecture of the
research note **Local Rules Can Require Nonlocal Coordinates and Infinite-State
Realizations: Limits of exact reduction in Kappa/BNGL**.

It is organized as a small umbrella target with modular theorem files, a
paper-to-proof map, an explicit proof-status boundary, an ELI10 explanation,
cheap structural checks, and a pinned Lean/Mathlib CI build.

The central distinction is the same one made in the paper:

- a **finite local coordinate** may fail even when one nonlocal integer is an
  exact state;
- a **finite hidden-state realization from one seed** may exist even when no
  reusable finite local coordinate works for all restart states;
- conversely, a one-integer exact coordinate may exist while **no finite hidden
  CTMC** reproduces the seed-level assay law.

The repository now also contains a **constructive practical layer** motivated by
those limits.  Instead of asking only whether arbitrary exact reduction is
decidable, it formalizes the contracts a useful reduction tool should satisfy:

- define sufficiency relative to an explicit restart set and prediction task;
- return concrete state-pair counterexamples when a proposed representation
  loses predictive information;
- test whether a candidate added coordinate actually separates a failed pair;
- distinguish exact from `epsilon`-approximate closure;
- use proof-carrying `certified / counterexample / unknown` outcomes; and
- certify a bounded search only when completeness of the searched domain is
  independently established.

The scanner is now an end-to-end constructive example: every finite local
representation is refuted by a future-law witness, while the nonlocal
`remaining` coordinate determines the **entire survival curve** exactly.  See
[`PRACTICAL-FRAMEWORK.md`](PRACTICAL-FRAMEWORK.md) and
[`ELI10-PRACTICAL.md`](ELI10-PRACTICAL.md).

## What is formalized

The repository covers every numbered mathematical result in the note and the
proof-critical appendix statements.  The paper-specific core includes:

1. the processive-scanner locality obstruction;
2. exact Erlang survival separation and coefficient independence;
3. the scanner's uniform exit-rate bound;
4. the scanner-seed recurrence and exact two-phase transform factorization;
5. the reversible-tip characteristic quadratic and physical busy-period root;
6. the finite-linear/rational-transform contradiction schema;
7. finite species-count injectivity under bounded connected species;
8. deterministic two-counter INC/JZDEC semantics and the exact free-site zero
   test;
9. finite-depth scanner refinement and separation only at the omega limit;
10. the exact macro-event aggregate-rate criterion;
11. the two many-one undecidability transfers, including their strengthened
    promise fields;
12. task-relative current/future sufficiency and explicit counterexample types;
13. aggregate-rate witness equivalence for exact macro closure;
14. counterexample-guided coordinate augmentation contracts;
15. metric future-law and aggregate-rate `epsilon`-approximate reduction;
16. complete-domain certificates and proof-carrying three-valued verdicts; and
17. the scanner's exact repair by the nonlocal remaining-distance coordinate.

The project does **not** hide imported mathematics behind `axiom`, `sorry`, or
`admit`.  Classical facts that are background rather than contributions of the
paper are represented as explicit typed interfaces in
`ExactReductionLimits/ClassicalInterfaces.lean`.  This includes the full
measure-theoretic construction of countable CTMCs, the Takacs M/M/1 busy-period
non-rationality theorem, Bessel tail asymptotics, phase-type density/compactness,
finite matrix-exponential rationality, CM2 halting undecidability, and the full
Kappa/BNGL parser/site-graph embedding bridge.

That boundary matters.  The Lean development kernel-checks the implications of
those inputs and proves the paper-specific algebra, combinatorics, and reduction
logic.  It does not pretend to have re-formalized entire external literatures.
See [`PROOF_STATUS.md`](PROOF_STATUS.md).

## Headline proof architecture

### Scanner: local syntax can miss an exact predictive coordinate

A scanner state records distances to the two ends of a homogeneous chain.  A
finite local observable has a bounded inspection radius.  Two deep positions on
the same chain can therefore have the same finite local observable vector while
having different remaining distances.

The Done-time survival law at remaining distance `r` is

$$
S_r(t) = e^{-\kappa t} \sum_{j=0}^{r-1} \frac{(\kappa t)^j}{j!}
$$

Lean proves that consecutive orders differ by a strictly positive term for
$\kappa, t > 0$, so the two locally indistinguishable restart states have different
future assay marginals.

### Scanner seed: reusable reduction and one-seed realization differ

From the designated build/freeze seed, first-event conditioning gives the
bounded recurrence

$$
F_n = u F_{n+1} + v w^n, \quad F_n = \frac{v w^n}{1 - u w}
$$

At `n=1`, Lean simplifies this to

$$
\mathbb{E}[e^{-sT}] = \frac{\lambda_s \kappa}{s^2 + (\lambda_b + \lambda_s + \kappa)s + \lambda_s \kappa}
$$

and proves that the denominator factors into two positive phase rates under the
physical rate assumptions.  This is the transform-level core of the exact
three-state hidden CTMC realization.

### Reversible tip: finite coordinate dimension is not finite state cardinality

The unique active tip gives the birth-death length process

$$
r \to r+1 \text{ at } \lambda, \quad r \to r-1 \text{ at } \mu
$$

with $\mu > \lambda$.  Lean proves that the paper's candidate transform

$$
\rho(s) = \frac{s + \lambda + \mu - \sqrt{(s + \lambda + \mu)^2 - 4 \lambda \mu}}{2 \lambda}
$$

satisfies the characteristic quadratic and has $\rho(0)=1$.  The classical fact
that this square-root transform is non-rational is an explicit background
input.  The repository then proves the exact logical implication: because every
finite-dimensional time-homogeneous linear realization has rational Laplace
transform, no such realization can reproduce the assay.

### Positive frontier: bounded connected species

After the standard graph-enumeration fact that a finite signature plus a uniform
complex-size bound yields only finitely many connected species types, Lean proves
that a mixture is injectively represented by its species multiplicity vector.
Copy numbers can remain unbounded, so finite coordinate dimension is kept
separate from finite state cardinality.

### Undecidability

The counter module formalizes the exact computational invariant used by the
paper: a rooted chain represents a nonnegative counter and the root is free iff
the counter is zero.  INC and JZDEC select exactly one local rule variant.

The final undecidability module proves generic many-one transfer theorems for:

- `Seed-Finite-Hidden-CTMC`; and
- `Finite-Local-Pattern-State`.

The concrete Kappa compilation and the classical CM2 halting theorem are
explicit inputs.  The reduction structures also require the paper's stronger
promises: assay-relevant infinitude/countably infinite strong quotients, the NO
branch finite-dimensional marginal obstruction, and the uniform exit-rate bound
for the reusable reduction.

## Build

The project is pinned to Lean **4.31.0** and Mathlib **v4.31.0**.

```bash
python3 tools/prelint.py
python3 tools/check_coverage.py
python3 tools/check_practical.py
lake build
```

The first three commands are cheap structural checks.  Only `lake build` is a Lean
kernel check.

## Verification status

This generated repository was structurally checked in the creation environment,
but that environment did not contain a Lean/Lake executable and could not fetch
one from the network.  Therefore this artifact does **not** claim a completed
local kernel build.  The included GitHub Actions workflow performs the pinned
Mathlib build with `leanprover/lean-action@v1`.

See [`PROOF_STATUS.md`](PROOF_STATUS.md) for the exact boundary rather than
inferring verification from file presence.

## Proof maps

- [`PROOF-PATH.md`](PROOF-PATH.md): dependency path from semantic primitives to
  each headline theorem.
- [`PAPER-COVERAGE.md`](PAPER-COVERAGE.md): paper statement -> Lean declaration
  -> status.
- [`PROOF_STATUS.md`](PROOF_STATUS.md): what is proved internally, what is an
  explicit classical interface, and what still requires a kernel build.
- [`ELI10-PRACTICAL.md`](ELI10-PRACTICAL.md): ELI10-level explanation of the
  paper and the constructive extension.
- [`PRACTICAL-FRAMEWORK.md`](PRACTICAL-FRAMEWORK.md): exact contracts and the
  intended BioNetGen-facing workflow.
- [`CHANGES-PRACTICAL.md`](CHANGES-PRACTICAL.md): concise file-by-file summary
  of the constructive extension.

## Repository layout

```text
.
├── ExactReductionLimits.lean
├── ExactReductionLimits/
│   ├── Core.lean
│   ├── RuleSemantics.lean
│   ├── MacroCriterion.lean
│   ├── Scanner.lean
│   ├── ScannerSeed.lean
│   ├── ReversibleTip.lean
│   ├── LinearRealization.lean
│   ├── Detector.lean
│   ├── BoundedComplex.lean
│   ├── CounterMachine.lean
│   ├── Refinement.lean
│   ├── ClassicalInterfaces.lean
│   ├── Undecidability.lean
│   ├── PaperTheorems.lean
│   ├── TaskSufficiency.lean
│   ├── ReductionDiagnostics.lean
│   ├── CoordinateRepair.lean
│   ├── ApproximateReduction.lean
│   ├── Certification.lean
│   ├── ScannerDiagnostics.lean
│   └── PracticalTheorems.lean
├── models/
│   └── README.md
├── paper/
│   ├── limits_exact_state_reduction_kappa_bngl_v9.pdf
│   ├── limits_exact_state_reduction_kappa_bngl_practical.pdf
│   ├── SHA256SUMS
│   └── README.md
├── tools/
│   ├── prelint.py
│   ├── check_coverage.py
│   └── check_practical.py
├── .github/workflows/lean.yml
├── README.md
├── ELI10-PRACTICAL.md
├── PRACTICAL-FRAMEWORK.md
├── PROOF-PATH.md
├── PROOF_STATUS.md
├── PAPER-COVERAGE.md
├── lakefile.toml
└── lean-toolchain
```

## Scope

The Lean project formalizes mathematical implications of a precise semantic
model.  It does not establish that a biological system satisfies those
assumptions, nor does it formalize KaSim/NFsim executable semantics, parser
behavior, software-specific automorphism normalization, or experimental
identifiability.  Those are separate verification problems.
