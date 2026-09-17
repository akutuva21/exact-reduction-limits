import Mathlib
import ExactReductionLimits.Core
import ExactReductionLimits.TaskSufficiency
import ExactReductionLimits.ReductionDiagnostics

noncomputable section

/-!
# Counterexample-guided coordinate repair

A counterexample says that the current state representation merged two states it
should not have merged.  An added coordinate explains that particular failure
only if it separates those two states.  This module formalizes that modest but
useful contract and deliberately does not claim that repairing one witness makes
the entire reduction exact.
-/

namespace ExactReductionLimits

/-- Add one candidate coordinate to an existing representation. -/
def augment {State Rep Feature : Type*}
    (phi : State → Rep) (feature : State → Feature) :
    State → Rep × Feature :=
  fun x => (phi x, feature x)

/-- A candidate feature separates a particular pair of microscopic states. -/
def Separates {State Feature : Type*}
    (feature : State → Feature) (x y : State) : Prop :=
  feature x ≠ feature y

/-- `fine` refines `coarse` when equality under the finer representation always
implies equality under the coarser one. -/
def RefinesRepresentation {State Fine Coarse : Type*}
    (fine : State → Fine) (coarse : State → Coarse) : Prop :=
  ∀ ⦃x y : State⦄, fine x = fine y → coarse x = coarse y

/-- Adding a coordinate always refines the original representation. -/
theorem augment_refines_base
    {State Rep Feature : Type*}
    (phi : State → Rep) (feature : State → Feature) :
    RefinesRepresentation (augment phi feature) phi := by
  intro x y hxy
  exact congrArg Prod.fst hxy

/-- A possibly heterogeneous library of candidate coordinates.  An external
search procedure may enumerate or rank indices; Lean only specifies what it
means for one of them to genuinely distinguish a failed pair. -/
structure FeatureLibrary (State : Type*) where
  Index : Type*
  Value : Index → Type*
  feature : (i : Index) → State → Value i

/-- At least one coordinate in a candidate library distinguishes the pair. -/
def FeatureLibrary.ExplainsPair
    {State : Type*} (L : FeatureLibrary State) (x y : State) : Prop :=
  ∃ i : L.Index, L.feature i x ≠ L.feature i y

/-- If the added feature separates a pair, the augmented representation cannot
continue to merge that pair. -/
theorem augment_separates
    {State Rep Feature : Type*}
    (phi : State → Rep) (feature : State → Feature)
    {x y : State} (h : Separates feature x y) :
    augment phi feature x ≠ augment phi feature y := by
  intro hpair
  apply h
  exact congrArg Prod.snd hpair

/-- If a feature by itself determines a future law, then adding it to any base
representation also determines that law. -/
theorem augment_determines_future_of_feature
    {State Rep Feature Law : Type*}
    (phi : State → Rep) (feature : State → Feature) (future : State → Law)
    (hfeature : DeterminesFutureLaw feature future) :
    DeterminesFutureLaw (augment phi feature) future := by
  intro x y hxy
  apply hfeature
  exact congrArg Prod.snd hxy

namespace PredictionTask

variable {State Current Law Rep Feature : Type*}

/-- Future-law sufficiency is monotone under representational refinement: once
a coarse state is sufficient for a fixed task, remembering additional
information cannot destroy that functional dependence.  This statement is
specific to task sufficiency; arbitrary refinement need not preserve strong
Markov lumpability because the target partition also changes. -/
theorem predictiveSufficient_of_refinement
    {T : PredictionTask State Current Law}
    {coarse : State → Rep} {fine : State → Feature}
    (href : RefinesRepresentation fine coarse)
    (hcoarse : T.PredictivelySufficient coarse) :
    T.PredictivelySufficient fine := by
  intro x y hx hy hfine
  exact hcoarse hx hy (href hfine)

/-- In particular, augmenting a task-sufficient representation preserves
predictive sufficiency. -/
theorem augment_preserves_predictive_sufficiency
    {T : PredictionTask State Current Law}
    {phi : State → Rep} {feature : State → Feature}
    (h : T.PredictivelySufficient phi) :
    T.PredictivelySufficient (augment phi feature) :=
  predictiveSufficient_of_refinement (augment_refines_base phi feature) h

/-- A candidate feature explains a future-law counterexample when it distinguishes
exactly the pair that the current representation incorrectly merged. -/
def ExplainsFutureCounterexample
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (feature : State → Feature) (w : FutureCounterexample T phi) : Prop :=
  Separates feature w.x w.y

/-- An explaining feature eliminates that particular collision after
augmentation.  No claim is made about unseen counterexamples. -/
theorem explained_future_witness_is_eliminated
    {T : PredictionTask State Current Law} {phi : State → Rep}
    {feature : State → Feature} {w : FutureCounterexample T phi}
    (h : ExplainsFutureCounterexample feature w) :
    augment phi feature w.x ≠ augment phi feature w.y :=
  augment_separates phi feature h

/-- A feature resolves every currently known future counterexample in a finite
witness list. -/
def ResolvesKnownFutureCounterexamples
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (feature : State → Feature) (ws : List (FutureCounterexample T phi)) : Prop :=
  ∀ w, w ∈ ws → ExplainsFutureCounterexample feature w

/-- Every witness in a resolved list is separated by the augmented state. -/
theorem resolved_list_is_eliminated
    {T : PredictionTask State Current Law} {phi : State → Rep}
    {feature : State → Feature} {ws : List (FutureCounterexample T phi)}
    (h : ResolvesKnownFutureCounterexamples feature ws) :
    ∀ w, w ∈ ws → augment phi feature w.x ≠ augment phi feature w.y := by
  intro w hw
  exact explained_future_witness_is_eliminated (h w hw)

end PredictionTask

namespace WeightedTransitionSystem

variable {State Macro Feature : Type*} [DecidableEq Macro]

/-- A candidate structural coordinate explains a macro-rate counterexample when
it distinguishes the two source states involved in that witness. -/
def ExplainsMacroCounterexample
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    (feature : State → Feature) (w : MacroCounterexample sys phi) : Prop :=
  Separates feature w.x w.y

/-- Adding an explaining feature removes the witnessed source-state collision. -/
theorem explained_macro_witness_is_eliminated
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {feature : State → Feature} {w : MacroCounterexample sys phi}
    (h : ExplainsMacroCounterexample feature w) :
    augment phi feature w.x ≠ augment phi feature w.y :=
  augment_separates phi feature h

end WeightedTransitionSystem
end ExactReductionLimits
