import Mathlib
import ExactReductionLimits.Scanner
import ExactReductionLimits.ScannerSeed
import ExactReductionLimits.ReversibleTip
import ExactReductionLimits.LinearRealization
import ExactReductionLimits.Detector
import ExactReductionLimits.CounterMachine
import ExactReductionLimits.Refinement

noncomputable section

/-!
# Explicit interfaces to classical background theorems

The research note deliberately reuses substantial classical mathematics:
countable-CTMC small-time expansions, M/M/1 busy-period analysis, rationality of
finite matrix-exponential laws, Bessel asymptotics, density of phase-type laws,
and undecidability of CM2 halting.  Re-proving those entire libraries would turn
the project into a formalization of probability/queueing/computability rather
than a formalization of the paper's new reduction argument.

Crucially, none of those facts is inserted as a Lean `axiom`.  They are explicit
fields of structures.  Any end-to-end use of a paper theorem must supply the
corresponding background witness, making the trust boundary mechanically
visible in theorem signatures and in `PROOF_STATUS.md`.
-/

namespace ExactReductionLimits
namespace ClassicalInterfaces

/-- Background facts about the actual rational-function class and finite linear
systems. -/
structure LinearBackground where
  rational : LinearRealization.RationalTransformClass
  FiniteLinearModel : Type*
  realizes : FiniteLinearModel → (ℝ → ℝ) → Prop
  finite_linear_has_rational_transform :
    ∀ M S, realizes M S → rational.member S

/-- Elementary epsilon definition of `f(t) ~ g(t)` as `t → +∞`. -/
def AsymptoticEquivalentAtTop (f g : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
    |f t / g t - 1| < ε

/-- Half-integer exponential tail profile in Corollary 3.5. -/
def halfIntegerTailProfile (C eta : ℝ) (t : ℝ) : ℝ :=
  C * Real.rpow t (-(3 : ℝ) / 2) * Real.exp (-eta * t)

/-- Classical M/M/1 facts used beyond the quadratic algebra proved in
`ReversibleTip.lean`. -/
structure BusyPeriodBackground (λ μ : ℝ) where
  stable : 0 < λ ∧ λ < μ
  rational : LinearRealization.RationalTransformClass
  completion_nonrational : ¬ rational.member (ReversibleTip.rho λ μ)
  density : ℝ → ℝ
  eta : ℝ
  tailConstant : ℝ
  tailConstant_pos : 0 < tailConstant
  eta_formula : eta = (Real.sqrt μ - Real.sqrt λ) ^ 2
  half_integer_tail :
    AsymptoticEquivalentAtTop density (halfIntegerTailProfile tailConstant eta)
  PhaseTypeLaw : Type*
  phaseOrder : PhaseTypeLaw → ℕ
  weakConvergesToBusyPeriod : (ℕ → PhaseTypeLaw) → Prop
  phaseTypeDenseAtBusyPeriod : ∃ H, weakConvergesToBusyPeriod H
  bounded_order_convergence_impossible :
    ∀ H, weakConvergesToBusyPeriod H →
      ∀ K : ℕ, ∃ n : ℕ, K < phaseOrder (H n)

/-- Classical stochastic-process bridge for the unique-tip site-graph process. -/
structure BusyPeriodCTMCBridge (λ μ : ℝ) where
  completionTransform : ℝ → ℝ
  transform_eq_rho : completionTransform = ReversibleTip.rho λ μ
  active_length_is_birth_death : Prop
  site_graph_realizable : Prop

/-- Standard polynomial identity bridge used to pass from equality of Erlang
survival functions to equality of the finite coefficient vectors proved
independent in `Scanner.lean`. -/
structure ErlangPolynomialBridge (κ : ℝ) where
  function_dependence_implies_coeff_dependence :
    ∀ N c,
      (∀ t : ℝ,
        ∑ r in Finset.range N,
          c r * Scanner.erlangSurvival κ (r + 1) t = 0) →
      Scanner.CoeffCombinationVanishes κ N c

/-- Background measure-theoretic CTMC facts from Appendices B and C. -/
structure CountableCTMCBackground where
  State : Type*
  countableState : Countable State
  small_time_aggregate_expansion : Prop
  finite_rate_continuity_from_above : Prop
  omega_refinement_is_fixed : Prop
  omega_refinement_is_coarsest_strong_lumping : Prop

/-- The graph-theoretic bridge from finite Kappa/BNGL patterns to the bounded-
radius semantic observables in `Scanner.lean`. -/
structure LocalPatternBridge where
  every_finite_pattern_family_has_bounded_reach : Prop
  disconnected_patterns_reduce_to_finite_overlap_data : Prop
  bngl_species_observables_obey_same_deep_locality : Prop
  fixed_functions_preserve_indistinguishability : Prop

/-- Finite-signature/size-bound graph enumeration used before the concrete
species-count injection in `BoundedComplex.lean`. -/
structure BoundedGraphBackground where
  bounded_connected_species_form_finite_type : Prop

/-- Analytic facts behind equations (10)-(11) of the nonhalting detector. -/
structure DetectorAnalyticBackground (γ κ : ℝ) where
  kappa_pos : 0 < κ
  survival_eq_poisson_laplace_functional : Prop
  exponential_series_eq : Prop
  laplace_meromorphic_continuation : Prop
  poles_exactly : Prop
  infinitely_many_poles_implies_nonrational : Prop

/-- Full ordinary-Kappa syntax bridge for the explicit counter invariant proved
in `CounterMachine.lean`. -/
structure KappaCounterBridge where
  finite_site_graph_encoding : Prop
  free_root_is_zero_test : Prop
  exactly_one_rule_variant_enabled : Prop
  graph_successor_matches_machine_successor : Prop

/-- External computability-theory fact used by Section 6. -/
structure CM2Background where
  Code : Type*
  Halts : Code → Prop
  halting_undecidable : UndecidableByBool Halts

/-- A compact bundle of the external background used by the entire paper. -/
structure PaperBackground where
  localPatterns : LocalPatternBridge
  boundedGraphs : BoundedGraphBackground
  counterSyntax : KappaCounterBridge
  cm2 : CM2Background

end ClassicalInterfaces
end ExactReductionLimits
