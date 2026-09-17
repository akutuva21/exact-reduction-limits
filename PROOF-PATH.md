# Proof path

The default target is `ExactReductionLimits.lean`.

## A. Semantic base

1. `Core.lean` defines observation compatibility, future-law determination, and
   Boolean decidability.
2. `RuleSemantics.lean` gives finite-match weighted rule semantics, total exit
   rates, the generator, and exact macro-event rates.
3. `MacroCriterion.lean` proves the finite-match aggregate-rate closure theorem:
   a surjective statistic has one well-defined macro generator iff aggregate
   rates are constant on its fibers.

This is the rule-semantic core of Appendix C.

## B. Processive scanner

`Scanner.lean` carries the reusable-state obstruction.

1. `State(left,right)` records scanner distances to the two chain boundaries.
2. `LocalObservable` carries a finite inspection radius and the translation
   invariance forced by a deep homogeneous interior.
3. `witnessA R` and `witnessB R` have the same chain length and are both deep,
   but their remaining distances differ by one.
4. `finite_local_family_cannot_locate_deep_scanner` proves Lemma 2.1 at this
   semantic boundary.
5. `erlangSurvival_succ_sub` proves the exact successive-order difference.
6. `erlangSurvival_strict_succ` makes the difference strict for positive
   `κ,t`.
7. `no_finite_local_family_determines_future` proves Theorem 2.2 using a
   one-time marginal; differing path laws follow immediately.
8. `scanner_exitRate_bound` proves Proposition 2.5.
9. `top_erlang_coefficient` and
   `erlang_coefficients_linearly_independent` prove the coefficient core of
   Lemma 2.6.

The finite-pattern-to-bounded-radius graph theorem and the standard polynomial
identity bridge are explicit fields in `ClassicalInterfaces.lean`.

## C. Designated scanner seed

`ScannerSeed.lean` formalizes Proposition 2.8.

1. `recurrenceSolution_step` checks the bounded closed-form recurrence solution.
2. `recurrence_at_one_eq_seedTransform` simplifies the one-monomer seed to the
   quadratic transform in equation (2).
3. `discr_nonneg` proves the denominator discriminant is nonnegative.
4. `phase_sum`, `phase_product`, and `phase_rates_pos` prove that the quadratic
   factors into two positive transient phase rates.
5. `seedTransform_eq_twoPhase` proves the exact transform factorization.

The stochastic first-event derivation of the recurrence and the standard fact
that the product transform is the absorption time of a two-transient-state CTMC
are classical probability bridges, not parser/runtime semantics.

## D. Reversible active tip

`ReversibleTip.lean` proves the algebra behind Lemma 3.2 and Proposition 3.1.

1. `rho_quadratic` proves the displayed busy-period root solves the first-step
   quadratic.
2. `rho_zero` proves the physical root has `ρ(0)=1` in the stable regime.
3. `exitRate_bound` proves the global `λ+μ` rate bound.

`LinearRealization.lean` then proves the logical core of Theorem 3.3:

```text
non-rational completion transform
+ survival/completion identity
+ finite linear realization => rational survival transform
----------------------------------------------------------
no finite linear realization
```

The Takacs busy-period identification, non-rationality of the square-root
transform, matrix-exponential rationality, Bessel tail, phase-type density, and
bounded-order compactness argument are explicit fields in
`ClassicalInterfaces.lean`.

## E. Positive bounded-complex theorem

`BoundedComplex.lean` proves that the vector of connected-species
multiplicities is injective for a finite species type.  The external graph step
"finite signature + uniform connected-complex size bound => finitely many
connected species up to isomorphism" is explicit in `BoundedGraphBackground`.

Together these are Theorem 4.1.

## F. Counter machine

`CounterMachine.lean` defines deterministic INC/JZDEC machines and the exact
rooted-chain counter invariant.

- `rootFree_iff_zero` is the free-site zero test.
- `zero_test_exact` proves zero/nonzero exclusivity.
- `positive_is_one_or_many` proves the two positive pop variants are exhaustive.
- `exactly_one_enabled_variant` records deterministic local rule selection.
- `localCounterStep_*` proves the numeric effect of INC/JZDEC.

The concrete ordinary-Kappa site-graph compiler is isolated in
`KappaCounterBridge` rather than being silently assumed.

## G. Observation-seeded refinement

`Refinement.lean` proves the scanner sharpness witness from Appendix B.

- `finite_stage_still_merges` and `next_stage_splits` give the exact finite-depth
  pattern.
- `no_finite_stage_is_final` proves every finite stage is strict.
- `omega_intersection_separates` proves the omega intersection separates all
  distances.
- `omega_is_coarsest_fixed_refinement` proves the abstract fixed-point argument
  once the countable-CTMC continuity theorem supplies omega stability.

## H. Undecidability

`Core.lean` proves the general many-one lemma
`undecidable_of_iff_reduction`.

`Undecidability.lean` defines two compiler certificates whose fields exactly
record the strengthened promises of Section 6.

- `seed_finite_hidden_ctmc_undecidable` is Theorem 6.2.
- `finite_local_pattern_state_undecidable` is Theorem 6.5.
- `reusableReduction_rate_bound` proves the global max-rate formula used in the
  second reduction.

The concrete compilers are kept separate from the generic computability proof so
that the paper-specific branch obligations remain visible rather than being
buried inside an opaque undecidability declaration.

## I. Paper-facing index

`PaperTheorems.lean` exports stable aliases corresponding to the paper numbering.
`PAPER-COVERAGE.md` records which parts are internally proved and which terminate
at an explicit classical interface.
