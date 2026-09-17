import Mathlib
import ExactReductionLimits.TaskSufficiency
import ExactReductionLimits.ReductionDiagnostics

noncomputable section

/-!
# Sound incomplete certification

The undecidability theorems rule out a complete decision procedure for arbitrary
rule-based models.  They do not rule out useful sound tools.  The correct API is
therefore proof-carrying and three-valued: certify exactness, return a concrete
counterexample, or report unknown.
-/

namespace ExactReductionLimits

namespace PredictionTask

variable {State Current Law Rep : Type*}

/-- Proof-carrying result for task-level state sufficiency. -/
inductive Verdict
    (T : PredictionTask State Current Law) (phi : State → Rep) : Type _ where
  | certified (proof : T.Sufficient phi)
  | currentCounterexample (witness : CurrentCounterexample T phi)
  | futureCounterexample (witness : FutureCounterexample T phi)
  | unknown

/-- Any non-unknown task verdict is automatically sound because the evidence is
stored in the constructor. -/
theorem verdict_certified_sound
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (h : T.Sufficient phi) :
    T.Sufficient phi := h

/-- The future-counterexample constructor carries a proof of failure. -/
theorem verdict_future_refutation_sound
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (w : FutureCounterexample T phi) :
    ¬ T.Sufficient phi := by
  intro hs
  exact (futureCounterexample_refutes w) hs.2

/-- The current-counterexample constructor likewise carries a proof of failure. -/
theorem verdict_current_refutation_sound
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (w : CurrentCounterexample T phi) :
    ¬ T.Sufficient phi := by
  intro hs
  exact (currentCounterexample_refutes w) hs.1

end PredictionTask

namespace WeightedTransitionSystem

variable {State Macro : Type*} [DecidableEq Macro]

/-- Proof-carrying three-way result for exact macro closure. -/
inductive Verdict
    (sys : WeightedTransitionSystem State) (phi : State → Macro) : Type _ where
  | certified (proof : sys.MacroClosed phi)
  | counterexample (witness : MacroCounterexample sys phi)
  | unknown

/-- A returned macro counterexample is a logically complete refutation. -/
theorem verdict_counterexample_sound
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    (w : MacroCounterexample sys phi) :
    ¬ sys.MacroClosed phi :=
  macroCounterexample_refutes w

/-- A finite or otherwise bounded search domain may safely prove a target
restart set only when completeness of that domain is independently certified. -/
structure DomainCertificate
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (target domain : Set State) where
  targetContained : target ⊆ domain
  closedOnDomain : sys.MacroClosedOn phi domain

/-- A complete-domain certificate yields exact closure on the requested restart
set. -/
theorem DomainCertificate.closedOnTarget
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {target domain : Set State}
    (C : DomainCertificate sys phi target domain) :
    sys.MacroClosedOn phi target :=
  macroClosedOn_of_complete_domain sys phi C.targetContained C.closedOnDomain

end WeightedTransitionSystem
end ExactReductionLimits
