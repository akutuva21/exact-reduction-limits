import Mathlib
import ExactReductionLimits.Core

noncomputable section

/-!
# Finite-match rule semantics

A finite Kappa/BNGL mixture has finitely many legal matches of each finite rule.
For the paper's exact-reduction arguments, the only required information is the
list of post-rewrite states and exact hazards.  This module therefore exposes a
small semantic kernel rather than a Kappa parser.
-/

namespace ExactReductionLimits

/-- A stable finite-outgoing weighted transition system.  Each list entry is one
concrete rule match; several matches may lead to the same successor. -/
structure WeightedTransitionSystem (State : Type*) where
  transitions : State → List (State × ℝ)
  rate_nonneg : ∀ x e, e ∈ transitions x → 0 ≤ e.2

namespace WeightedTransitionSystem

variable {State Macro : Type*}

/-- Total microscopic exit rate `q_x`. -/
def exitRate (sys : WeightedTransitionSystem State) (x : State) : ℝ :=
  ((sys.transitions x).map Prod.snd).sum

/-- Generator action on a test function, matching the paper's equation (12). -/
def generator (sys : WeightedTransitionSystem State)
    (f : State → ℝ) (x : State) : ℝ :=
  ((sys.transitions x).map (fun e => e.2 * (f e.1 - f x))).sum

/-- Total hazard of all microscopic matches whose products land in macrostate
`z'`; this is the finite-match version of equation (13). -/
def macroRate [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (x : State) (z : Macro) : ℝ :=
  (((sys.transitions x).filter (fun e => phi e.1 = z)).map Prod.snd).sum

/-- Exact rule-level closure: states in the same macro fiber have identical
aggregate rates into every different macro fiber. -/
def MacroClosed [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro) : Prop :=
  ∀ ⦃x y : State⦄, phi x = phi y →
    ∀ z : Macro, z ≠ phi x → macroRate sys phi x z = macroRate sys phi y z

/-- Existence of one macro generator shared by every microscopic representative. -/
def HasMacroGenerator [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro) : Prop :=
  ∃ qbar : Macro → Macro → ℝ,
    ∀ x z, z ≠ phi x → macroRate sys phi x z = qbar (phi x) z

/-- Nonnegative rule hazards imply a nonnegative exit rate. -/
theorem exitRate_nonneg (sys : WeightedTransitionSystem State) (x : State) :
    0 ≤ sys.exitRate x := by
  unfold exitRate
  apply List.sum_nonneg
  intro r hr
  rcases List.mem_map.mp hr with ⟨e, he, rfl⟩
  exact sys.rate_nonneg x e he

end WeightedTransitionSystem
end ExactReductionLimits
