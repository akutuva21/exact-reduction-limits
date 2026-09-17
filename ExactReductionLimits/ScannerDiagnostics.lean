import Mathlib
import ExactReductionLimits.Scanner
import ExactReductionLimits.TaskSufficiency
import ExactReductionLimits.CoordinateRepair

noncomputable section

/-!
# Scanner as a concrete state-discovery example

The paper's scanner is not only an impossibility witness.  It also demonstrates
what a successful diagnostic should return: bounded local coordinates merge
states with different futures, while the nonlocal `remaining` coordinate repairs
the prediction problem exactly.
-/

namespace ExactReductionLimits
namespace Scanner

/-- The full survival curve, not merely one selected time point. -/
def survivalLaw (κ : ℝ) (x : State) : ℝ → ℝ :=
  fun t => erlangSurvival κ (remaining x) t

/-- The exact nonlocal coordinate `remaining` determines the entire scanner
survival curve. -/
theorem remaining_determines_survivalLaw (κ : ℝ) :
    DeterminesFutureLaw remaining (survivalLaw κ) := by
  intro x y hxy
  funext t
  simp [survivalLaw, hxy]

/-- Adding `remaining` to any existing representation is therefore sufficient
for the complete scanner survival curve. -/
theorem augment_with_remaining_determines_survivalLaw
    {Rep : Type*} (phi : State → Rep) (κ : ℝ) :
    DeterminesFutureLaw (augment phi remaining) (survivalLaw κ) :=
  augment_determines_future_of_feature phi remaining (survivalLaw κ)
    (remaining_determines_survivalLaw κ)

/-- Prediction task used to turn the scanner theorem into a concrete diagnostic
object.  All scan restart states are relevant and the current assay is trivial;
the protected object is the complete Done-time survival curve. -/
def survivalTask (κ : ℝ) : PredictionTask State Unit (ℝ → ℝ) where
  relevant := Set.univ
  current := fun _ => ()
  future := survivalLaw κ

/-- Any finite local family yields an explicit future-law counterexample.  The
same local vector hides a difference visible at any chosen positive time. -/
def local_family_future_counterexample
    {n : ℕ} (F : LocalFamily n) (κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) :
    PredictionTask.FutureCounterexample (survivalTask κ) (vector F) := by
  have hpaper := no_finite_local_family_determines_future F κ t hκ ht
  refine {
    x := witnessA F.reach
    y := witnessB F.reach
    x_relevant := by simp [survivalTask]
    y_relevant := by simp [survivalTask]
    sameRepresentation := hpaper.1
    differentFuture := ?_
  }
  intro hfun
  have hat := congrFun hfun t
  exact hpaper.2 (by simpa [survivalTask, survivalLaw] using hat)

/-- Consequently the finite local vector is not an exact predictive state for
the scanner survival task. -/
theorem local_family_not_predictively_sufficient
    {n : ℕ} (F : LocalFamily n) (κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) :
    ¬ (survivalTask κ).PredictivelySufficient (vector F) :=
  PredictionTask.futureCounterexample_refutes
    (local_family_future_counterexample F κ t hκ ht)

/-- The diagnostic identifies a coordinate that separates the exact pair used
by the finite-local counterexample: distance remaining.  This theorem is stated
directly on the source pair so it does not depend on proof-term reduction. -/
theorem remaining_separates_local_counterexample_pair
    {n : ℕ} (F : LocalFamily n) :
    Separates remaining (witnessA F.reach) (witnessB F.reach) := by
  unfold Separates
  rw [witnessA_remaining, witnessB_remaining]
  omega

/-- Stronger than merely repairing one witness: `remaining` itself is globally
sufficient on every scanner restart state for the whole survival curve. -/
theorem remaining_is_predictively_sufficient (κ : ℝ) :
    (survivalTask κ).PredictivelySufficient remaining := by
  intro x y hx hy hxy
  exact remaining_determines_survivalLaw κ hxy

end Scanner
end ExactReductionLimits
