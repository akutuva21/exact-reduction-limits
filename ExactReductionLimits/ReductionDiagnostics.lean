import Mathlib
import ExactReductionLimits.RuleSemantics

noncomputable section

/-!
# Exact reduction diagnostics

A failed reduction should return a scientifically inspectable witness rather
than only a Boolean.  For rule semantics, the canonical witness is a pair of
microscopic states that the proposed representation merges even though their
aggregate hazards into some target macrostate differ.
-/

namespace ExactReductionLimits
namespace WeightedTransitionSystem

variable {State Macro : Type*} [DecidableEq Macro]

/-- Strong macro closure restricted to a user-specified collection of restart
states.  The unrestricted paper definition is `MacroClosed`. -/
def MacroClosedOn
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) : Prop :=
  ∀ ⦃x y : State⦄, x ∈ relevant → y ∈ relevant → phi x = phi y →
    ∀ z : Macro, z ≠ phi x →
      macroRate sys phi x z = macroRate sys phi y z

/-- A constructive obstruction to exact strong lumpability. -/
structure MacroCounterexample
    (sys : WeightedTransitionSystem State) (phi : State → Macro) where
  x : State
  y : State
  target : Macro
  sameMacro : phi x = phi y
  targetDifferent : target ≠ phi x
  rateDifferent :
    macroRate sys phi x target ≠ macroRate sys phi y target

/-- A constructive obstruction whose two source states lie in a particular
restart set. -/
structure MacroCounterexampleOn
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) extends MacroCounterexample sys phi where
  x_relevant : x ∈ relevant
  y_relevant : y ∈ relevant

/-- Any global counterexample refutes exact macro closure. -/
theorem macroCounterexample_refutes
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    (w : MacroCounterexample sys phi) :
    ¬ sys.MacroClosed phi := by
  intro h
  exact w.rateDifferent
    (h w.sameMacro w.target w.targetDifferent)

/-- A counterexample discovered inside any search domain is already a global
refutation: failure needs no completeness proof for the searched domain. -/
theorem macroCounterexampleOn_refutes_global
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {relevant : Set State}
    (w : MacroCounterexampleOn sys phi relevant) :
    ¬ sys.MacroClosed phi :=
  macroCounterexample_refutes w.toMacroCounterexample

/-- Any in-domain counterexample refutes exact closure on that domain. -/
theorem macroCounterexampleOn_refutes
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {relevant : Set State}
    (w : MacroCounterexampleOn sys phi relevant) :
    ¬ sys.MacroClosedOn phi relevant := by
  intro h
  exact w.rateDifferent
    (h w.x_relevant w.y_relevant w.sameMacro w.target w.targetDifferent)

/-- Exact macro closure is equivalent to absence of a concrete aggregate-rate
counterexample.  This is a proof-level specification of what a refuting search
procedure should return. -/
theorem macroClosed_iff_no_counterexample
    (sys : WeightedTransitionSystem State) (phi : State → Macro) :
    sys.MacroClosed phi ↔ ¬ Nonempty (MacroCounterexample sys phi) := by
  constructor
  · intro h ⟨w⟩
    exact (macroCounterexample_refutes w) h
  · intro h
    intro x y hxy z hz
    by_contra hne
    apply h
    exact ⟨{
      x := x
      y := y
      target := z
      sameMacro := hxy
      targetDifferent := hz
      rateDifferent := hne
    }⟩

/-- Domain-restricted analogue of `macroClosed_iff_no_counterexample`. -/
theorem macroClosedOn_iff_no_counterexample
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) :
    sys.MacroClosedOn phi relevant ↔
      ¬ Nonempty (MacroCounterexampleOn sys phi relevant) := by
  constructor
  · intro h ⟨w⟩
    exact (macroCounterexampleOn_refutes w) h
  · intro h
    intro x y hx hy hxy z hz
    by_contra hne
    apply h
    exact ⟨{
      x := x
      y := y
      target := z
      sameMacro := hxy
      targetDifferent := hz
      rateDifferent := hne
      x_relevant := hx
      y_relevant := hy
    }⟩

/-- Global closure implies closure on every restricted restart set. -/
theorem macroClosedOn_of_macroClosed
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) (h : sys.MacroClosed phi) :
    sys.MacroClosedOn phi relevant := by
  intro x y hx hy hxy z hz
  exact h hxy z hz

/-- A certificate on a search domain is globally useful for a target restart
set only when that target set is known to be contained in the search domain. -/
theorem macroClosedOn_of_complete_domain
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    {target domain : Set State}
    (hcomplete : target ⊆ domain)
    (hdomain : sys.MacroClosedOn phi domain) :
    sys.MacroClosedOn phi target := by
  intro x y hx hy hxy z hz
  exact hdomain (hcomplete hx) (hcomplete hy) hxy z hz

end WeightedTransitionSystem
end ExactReductionLimits
