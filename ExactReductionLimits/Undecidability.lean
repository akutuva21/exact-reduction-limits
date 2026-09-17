import Mathlib
import ExactReductionLimits.Core
import ExactReductionLimits.ClassicalInterfaces

noncomputable section

/-!
# The two exact-reduction decision problems

This file formalizes the many-one reduction skeleton of Theorems 6.2 and 6.5,
including the strengthened promises.  Concrete Kappa compilation and the
classical CM2 undecidability theorem are explicit inputs rather than hidden
axioms.
-/

namespace ExactReductionLimits
namespace Undecidability

/-- A compiled instance of the seed-level finite-hidden-CTMC question.  The
actual finite Kappa program/seed/assay representation is deliberately generic. -/
structure SeedReduction
    (Code Instance : Type*) (Halts : Code → Prop)
    (FiniteHiddenCTMC : Instance → Prop) where
  compile : Code → Instance
  correctness : ∀ c, Halts c ↔ FiniteHiddenCTMC (compile c)
  assayRelevantInfinite : Instance → Prop
  quotientCountablyInfinite : Instance → Prop
  noFiniteDimensionalMarginal : Instance → Prop
  promise_infinite : ∀ c, assayRelevantInfinite (compile c)
  promise_quotient : ∀ c, quotientCountablyInfinite (compile c)
  no_branch_stronger : ∀ c, ¬ Halts c → noFiniteDimensionalMarginal (compile c)

/-- Theorem 6.2 as a pure many-one consequence of the constructed compiler. -/
theorem seed_finite_hidden_ctmc_undecidable
    {Code Instance : Type*}
    {Halts : Code → Prop} {FiniteHiddenCTMC : Instance → Prop}
    (hhalt : UndecidableByBool Halts)
    (R : SeedReduction Code Instance Halts FiniteHiddenCTMC) :
    UndecidableByBool FiniteHiddenCTMC := by
  exact undecidable_of_iff_reduction hhalt R.compile R.correctness

/-- A compiled instance of the reusable finite-local-pattern-state question. -/
structure LocalReduction
    (Code Instance : Type*) (Halts : Code → Prop)
    (FiniteLocalPatternState : Instance → Prop) where
  compile : Code → Instance
  correctness : ∀ c, Halts c ↔ FiniteLocalPatternState (compile c)
  quotientCountablyInfinite : Instance → Prop
  uniformlyBoundedExitRate : Instance → Prop
  promise_quotient : ∀ c, quotientCountablyInfinite (compile c)
  promise_exitRate : ∀ c, uniformlyBoundedExitRate (compile c)

/-- Theorem 6.5 as a pure many-one consequence of the constructed compiler. -/
theorem finite_local_pattern_state_undecidable
    {Code Instance : Type*}
    {Halts : Code → Prop} {FiniteLocalPatternState : Instance → Prop}
    (hhalt : UndecidableByBool Halts)
    (R : LocalReduction Code Instance Halts FiniteLocalPatternState) :
    UndecidableByBool FiniteLocalPatternState := by
  exact undecidable_of_iff_reduction hhalt R.compile R.correctness

/-- The global exit-rate bound used in the reusable reduction. -/
def reusableReductionBound (γ σ κ λ μ : ℝ) : ℝ :=
  max (γ + σ) (max κ (λ + μ))

/-- Every mode-specific rate is below the paper's maximum bound. -/
theorem reusableReduction_rate_bound
    (γ σ κ λ μ : ℝ) :
    γ + σ ≤ reusableReductionBound γ σ κ λ μ ∧
    κ ≤ reusableReductionBound γ σ κ λ μ ∧
    λ + μ ≤ reusableReductionBound γ σ κ λ μ := by
  unfold reusableReductionBound
  constructor
  · exact le_max_left _ _
  constructor
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The two decision notions are not logically interchangeable: a reusable local
coordinate property can hold while a seed finite-state realization property
fails.  This logical wrapper is instantiated by the reversible-tip branch in the
paper. -/
theorem notions_separate
    {Instance : Type*}
    (Local Seed : Instance → Prop) (x : Instance)
    (hLocal : Local x) (hSeed : ¬ Seed x) :
    ¬ (∀ y, Local y → Seed y) := by
  intro h
  exact hSeed (h x hLocal)

end Undecidability
end ExactReductionLimits
