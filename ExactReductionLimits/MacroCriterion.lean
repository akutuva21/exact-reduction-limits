import Mathlib
import ExactReductionLimits.RuleSemantics

noncomputable section

/-!
# Exact macro-event closure criterion

This is the finite-match generator core of Appendix C.  The probabilistic
small-time expansion needed to identify this criterion with a projected CTMC is
kept as a classical interface in `ClassicalInterfaces.lean`; the rule-semantic
rate equivalence itself is proved here.
-/

namespace ExactReductionLimits
namespace WeightedTransitionSystem

variable {State Macro : Type*} [DecidableEq Macro]

/-- A shared macro generator immediately implies the aggregate-rate closure
condition. -/
theorem macroClosed_of_hasMacroGenerator
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (hgen : sys.HasMacroGenerator phi) :
    sys.MacroClosed phi := by
  rcases hgen with ⟨qbar, hq⟩
  intro x y hxy z hz
  calc
    macroRate sys phi x z = qbar (phi x) z := hq x z hz
    _ = qbar (phi y) z := by rw [hxy]
    _ = macroRate sys phi y z := by
      symm
      apply hq y z
      simpa [hxy] using hz

/-- Conversely, if every macrostate has a representative, aggregate-rate
closure constructs a well-defined macro generator. -/
theorem hasMacroGenerator_of_macroClosed
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (hsurj : Function.Surjective phi)
    (hclosed : sys.MacroClosed phi) :
    sys.HasMacroGenerator phi := by
  classical
  choose rep hrep using hsurj
  refine ⟨fun z z' => macroRate sys phi (rep z) z', ?_⟩
  intro x z hz
  have hsame : phi x = phi (rep (phi x)) := by
    symm
    exact hrep (phi x)
  have h := hclosed hsame z hz
  simpa only [hrep] using h

/-- Generator-level form of Proposition C.2. -/
theorem macroCriterion
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (hsurj : Function.Surjective phi) :
    sys.MacroClosed phi ↔ sys.HasMacroGenerator phi := by
  constructor
  · exact hasMacroGenerator_of_macroClosed sys phi hsurj
  · exact macroClosed_of_hasMacroGenerator sys phi

end WeightedTransitionSystem
end ExactReductionLimits
