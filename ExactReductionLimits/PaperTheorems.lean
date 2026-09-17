import Mathlib
import ExactReductionLimits.Scanner
import ExactReductionLimits.ScannerSeed
import ExactReductionLimits.ReversibleTip
import ExactReductionLimits.LinearRealization
import ExactReductionLimits.Detector
import ExactReductionLimits.BoundedComplex
import ExactReductionLimits.CounterMachine
import ExactReductionLimits.Refinement
import ExactReductionLimits.ClassicalInterfaces
import ExactReductionLimits.Undecidability
import ExactReductionLimits.MacroCriterion

noncomputable section

/-!
# Paper-facing theorem index

This module gives stable paper-numbered wrappers around the implementation
modules.  See `PAPER-COVERAGE.md` for exact theorem-by-theorem provenance and the
boundary between kernel-proved paper-specific reasoning and explicitly supplied
classical background.
-/

namespace ExactReductionLimits
namespace Paper

/-- Lemma 2.1. -/
theorem lemma_2_1
    {n : ℕ} (F : Scanner.LocalFamily n) :
    Scanner.vector F (Scanner.witnessA F.reach) =
      Scanner.vector F (Scanner.witnessB F.reach) :=
  Scanner.finite_local_family_cannot_locate_deep_scanner F

/-- Theorem 2.2. -/
theorem theorem_2_2
    {n : ℕ} (F : Scanner.LocalFamily n) (κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) :
    Scanner.vector F (Scanner.witnessA F.reach) =
        Scanner.vector F (Scanner.witnessB F.reach) ∧
      Scanner.erlangSurvival κ (Scanner.remaining (Scanner.witnessA F.reach)) t ≠
        Scanner.erlangSurvival κ (Scanner.remaining (Scanner.witnessB F.reach)) t :=
  Scanner.no_finite_local_family_determines_future F κ t hκ ht

/-- Proposition 2.5. -/
theorem proposition_2_5
    (λb λs κ : ℝ) (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ)
    (m : Scanner.Mode) :
    Scanner.modeExitRate λb λs κ m ≤ λb + λs + κ :=
  Scanner.scanner_exitRate_bound λb λs κ hλb hλs hκ m

/-- Lemma 2.6, coefficient-exact formulation. -/
theorem lemma_2_6
    (κ : ℝ) (hκ : κ ≠ 0) :
    ∀ N c, Scanner.CoeffCombinationVanishes κ N c →
      ∀ r, r < N → c r = 0 :=
  Scanner.erlang_coefficients_linearly_independent κ hκ

/-- Proposition 2.7: no fixed finite-dimensional model can contain the
assay outputs of every scanner restart, once the standard finite-rank bridge is
supplied. -/
theorem proposition_2_7
    {Model : Type*}
    (κ : ℝ) (hκ : κ ≠ 0)
    (ModelContainsAllRestarts : Model → Prop)
    (model_implies_dependence :
      ∀ M, ModelContainsAllRestarts M →
        Scanner.InitialSegmentDependent (Scanner.erlangCoeffFamily κ)) :
    ¬ ∃ M, ModelContainsAllRestarts M :=
  LinearRealization.no_model_for_all_scanner_restarts
    κ hκ ModelContainsAllRestarts model_implies_dependence

/-- Proposition 2.8, transform-level factorization. -/
theorem proposition_2_8
    (λb λs κ s : ℝ)
    (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ)
    (hA : s + ScannerSeed.phaseA λb λs κ ≠ 0)
    (hB : s + ScannerSeed.phaseB λb λs κ ≠ 0)
    (hQ : s ^ 2 + (λb + λs + κ) * s + λs * κ ≠ 0) :
    ScannerSeed.seedTransform λb λs κ s =
      ScannerSeed.twoPhaseTransform
        (ScannerSeed.phaseA λb λs κ)
        (ScannerSeed.phaseB λb λs κ) s :=
  ScannerSeed.seedTransform_eq_twoPhase λb λs κ s hλb hλs hκ hA hB hQ

/-- Proposition 3.1. -/
theorem proposition_3_1
    (λ μ : ℝ) (hλ : 0 ≤ λ) (hμ : 0 ≤ μ) (m : ReversibleTip.Mode) :
    ReversibleTip.exitRate λ μ m ≤ λ + μ :=
  ReversibleTip.exitRate_bound λ μ hλ hμ m

/-- Lemma 3.2, algebraic characteristic equation plus physical root at zero. -/
theorem lemma_3_2_quadratic
    (λ μ s : ℝ) (hλ : 0 < λ) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    λ * (ReversibleTip.rho λ μ s) ^ 2 -
      (s + λ + μ) * ReversibleTip.rho λ μ s + μ = 0 :=
  ReversibleTip.rho_quadratic λ μ s hλ hμ hs

/-- Theorem 3.3 at the exact rational-transform bridge used in the
paper. -/
theorem theorem_3_3
    {Model : Type*}
    (R : LinearRealization.RationalTransformClass)
    (rho S : ℝ → ℝ)
    (Realizes : Model → (ℝ → ℝ) → Prop)
    (hrel : ReversibleTip.SurvivalCompletionRelation rho S)
    (hrho : ¬ R.member rho)
    (hlinear : ∀ M, Realizes M S → R.member S) :
    ¬ ∃ M, Realizes M S :=
  LinearRealization.no_finite_linear_realization_of_nonrational_completion
    R rho S Realizes hrel hrho hlinear

/-- Corollary 3.5: the two classical analytic consequences are surfaced
explicitly from the busy-period background package. -/
theorem corollary_3_5_tail
    (lambda mu : ℝ)
    (B : ClassicalInterfaces.BusyPeriodBackground lambda mu) :
    ClassicalInterfaces.AsymptoticEquivalentAtTop B.density
      (ClassicalInterfaces.halfIntegerTailProfile B.tailConstant B.eta) :=
  B.half_integer_tail

/-- Corollary 3.5: every phase-type approximation sequence converging to the
busy-period law has unbounded phase order. -/
theorem corollary_3_5_unbounded_order
    (lambda mu : ℝ)
    (B : ClassicalInterfaces.BusyPeriodBackground lambda mu) :
    ∀ H, B.weakConvergesToBusyPeriod H →
      ∀ K : ℕ, ∃ n : ℕ, K < B.phaseOrder (H n) :=
  B.bounded_order_convergence_impossible

/-- Theorem 4.1 after the finite-species enumeration step. -/
theorem theorem_4_1
    {Species : Type*} [Fintype Species] [DecidableEq Species] :
    ∃ phi : Multiset Species → (Species → ℕ), Function.Injective phi :=
  BoundedComplex.finite_exact_coordinate

/-- Lemma 5.1 zero-test core. -/
theorem lemma_5_1_zero_test (n : ℕ) :
    (n = 0) ↔ ¬ 0 < n :=
  CounterMachine.zero_test_exact n

/-- Remark B.2: no finite scanner refinement depth is final. -/
theorem remark_B_2_finite (n : ℕ) :
    ∃ r s, Refinement.scannerLabel n r = Refinement.scannerLabel n s ∧
      Refinement.scannerLabel (n + 1) r ≠ Refinement.scannerLabel (n + 1) s :=
  Refinement.no_finite_stage_is_final n

/-- Remark B.2: omega separates all remaining-distance classes. -/
theorem remark_B_2_omega {r s : ℕ}
    (h : ∀ n, Refinement.scannerLabel n r = Refinement.scannerLabel n s) :
    r = s :=
  Refinement.omega_intersection_separates h

/-- Proposition B.1's countable-CTMC conclusion, with the measure-
theoretic background supplied explicitly. -/
theorem proposition_B_1
    (C : ClassicalInterfaces.CountableCTMCBackground) :
    C.omega_refinement_is_coarsest_strong_lumping :=
  C.omega_refinement_is_coarsest_strong_lumping

/-- Lemma C.1's small-time expansion, supplied by the countable-CTMC background
package. -/
theorem lemma_C_1
    (C : ClassicalInterfaces.CountableCTMCBackground) :
    C.small_time_aggregate_expansion :=
  C.small_time_aggregate_expansion

/-- Proposition C.2 at the finite-match generator level. -/
theorem proposition_C_2
    {State Macro : Type*} [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (hsurj : Function.Surjective phi) :
    sys.MacroClosed phi ↔ sys.HasMacroGenerator phi :=
  WeightedTransitionSystem.macroCriterion sys phi hsurj

/-- Theorem 6.2. -/
theorem theorem_6_2
    {Code Instance : Type*}
    {Halts : Code → Prop} {FiniteHiddenCTMC : Instance → Prop}
    (hhalt : UndecidableByBool Halts)
    (R : Undecidability.SeedReduction Code Instance Halts FiniteHiddenCTMC) :
    UndecidableByBool FiniteHiddenCTMC :=
  Undecidability.seed_finite_hidden_ctmc_undecidable hhalt R

/-- Theorem 6.5. -/
theorem theorem_6_5
    {Code Instance : Type*}
    {Halts : Code → Prop} {FiniteLocalPatternState : Instance → Prop}
    (hhalt : UndecidableByBool Halts)
    (R : Undecidability.LocalReduction Code Instance Halts FiniteLocalPatternState) :
    UndecidableByBool FiniteLocalPatternState :=
  Undecidability.finite_local_pattern_state_undecidable hhalt R

end Paper
end ExactReductionLimits
