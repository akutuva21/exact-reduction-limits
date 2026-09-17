import Mathlib
import ExactReductionLimits.ReversibleTip
import ExactReductionLimits.Scanner

noncomputable section

/-!
# Rational-transform obstruction to finite linear realization

The paper uses one classical fact: every finite-dimensional time-homogeneous
linear realization has a rational Laplace transform.  We isolate the algebraic
part from that background fact by working with any transform class closed under
the rational operations required by equation (5).
-/

namespace ExactReductionLimits
namespace LinearRealization

/-- The closure properties of rational functions actually used by the proof. -/
structure RationalTransformClass where
  member : (ℝ → ℝ) → Prop
  one_mem : member (fun _ => 1)
  id_mem : member (fun s => s)
  sub_mem : ∀ {f g}, member f → member g → member (fun s => f s - g s)
  mul_mem : ∀ {f g}, member f → member g → member (fun s => f s * g s)
  congr : ∀ {f g}, f = g → member f → member g

/-- If `ρ = 1 - s S(s)`, rationality of `S` forces rationality of `ρ`. -/
theorem completion_rational_of_survival_rational
    (R : RationalTransformClass) (ρ S : ℝ → ℝ)
    (hrel : ReversibleTip.SurvivalCompletionRelation ρ S)
    (hS : R.member S) :
    R.member ρ := by
  have hform : ρ = fun s => (fun _ : ℝ => 1) s - (fun s : ℝ => s) s * S s := by
    funext s
    exact hrel s
  apply R.congr hform.symm
  exact R.sub_mem R.one_mem (R.mul_mem R.id_mem hS)

/-- Theorem 3.3, abstracted at precisely the classical bridge used in the paper:
if the completion transform is non-rational and every finite linear realization
has a rational survival transform, no finite linear realization can exist. -/
theorem no_finite_linear_realization_of_nonrational_completion
    {Model : Type*}
    (R : RationalTransformClass)
    (ρ S : ℝ → ℝ)
    (Realizes : Model → (ℝ → ℝ) → Prop)
    (hrel : ReversibleTip.SurvivalCompletionRelation ρ S)
    (hρ : ¬ R.member ρ)
    (linear_implies_rational : ∀ M, Realizes M S → R.member S) :
    ¬ ∃ M, Realizes M S := by
  rintro ⟨M, hM⟩
  apply hρ
  exact completion_rational_of_survival_rational R ρ S hrel
    (linear_implies_rational M hM)

/-- Proposition 2.7 in scanner-specific form.  Once a fixed-dimensional
linear realization is known to force a finite dependence among the Erlang
coefficient outputs, the internally proved triangular independence gives the
contradiction. -/
theorem no_model_for_all_scanner_restarts
    {Model : Type*}
    (κ : ℝ) (hκ : κ ≠ 0)
    (ModelContainsAllRestarts : Model → Prop)
    (model_implies_dependence :
      ∀ M, ModelContainsAllRestarts M →
        Scanner.InitialSegmentDependent (Scanner.erlangCoeffFamily κ)) :
    ¬ ∃ M, ModelContainsAllRestarts M := by
  rintro ⟨M, hM⟩
  exact Scanner.erlang_initial_segments_independent κ hκ
    (model_implies_dependence M hM)

/-- A genuinely finite-rank family: some `K` forces every `K+1` selected
vectors to have a nontrivial real linear dependence. -/
def FiniteRankFamily {Index Vector : Type*}
    [AddCommGroup Vector] [Module ℝ Vector]
    (family : Index → Vector) : Prop :=
  ∃ K : ℕ, ∀ xs : Fin (K + 1) → Index,
    ∃ c : Fin (K + 1) → ℝ,
      (∃ i, c i ≠ 0) ∧
      (∑ i : Fin (K + 1), c i • family (xs i)) = 0

/-- Contradiction wrapper for Proposition 2.7.  The concrete Erlang coefficient
theorem supplies the independent family; a `K`-dimensional matrix-exponential
realization supplies finite rank. -/
theorem no_model_if_independent_and_finite_rank
    {Model Index Vector : Type*}
    [AddCommGroup Vector] [Module ℝ Vector]
    (family : Index → Vector)
    (Independent : Prop)
    (ModelContains : Model → Prop)
    (independent_excludes_finite_rank : Independent → ¬ FiniteRankFamily family)
    (model_implies_finite_rank : ∀ M, ModelContains M → FiniteRankFamily family)
    (hIndependent : Independent) :
    ¬ ∃ M, ModelContains M := by
  intro h
  rcases h with ⟨M, hM⟩
  exact independent_excludes_finite_rank hIndependent
    (model_implies_finite_rank M hM)

end LinearRealization
end ExactReductionLimits
