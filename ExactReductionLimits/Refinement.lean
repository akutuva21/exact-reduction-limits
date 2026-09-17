import Mathlib

noncomputable section

/-!
# Observation-seeded refinement and the scanner's omega sharpness

For the scanner, refinement depth has an exact closed form.  After `n` rounds it
has isolated distances `0,...,n` and leaves all larger distances in one tail
class.  This module proves strictness at every finite depth and separation in the
omega intersection (Remark B.2).
-/

namespace ExactReductionLimits
namespace Refinement

/-- Label of a remaining-distance state after `n` finite refinement rounds. -/
def scannerLabel (n r : ℕ) : ℕ := if r ≤ n then r else n + 1

/-- Distances `n+1` and `n+2` are still merged after `n` rounds. -/
theorem finite_stage_still_merges (n : ℕ) :
    scannerLabel n (n + 1) = scannerLabel n (n + 2) := by
  simp [scannerLabel]
  omega

/-- The very next refinement round splits those two distances. -/
theorem next_stage_splits (n : ℕ) :
    scannerLabel (n + 1) (n + 1) ≠ scannerLabel (n + 1) (n + 2) := by
  simp [scannerLabel]
  omega

/-- No finite refinement depth is stable on all scanner distances. -/
theorem no_finite_stage_is_final (n : ℕ) :
    ∃ r s, scannerLabel n r = scannerLabel n s ∧
      scannerLabel (n + 1) r ≠ scannerLabel (n + 1) s := by
  exact ⟨n + 1, n + 2, finite_stage_still_merges n, next_stage_splits n⟩

/-- Equality at every finite depth forces equality of the actual remaining
distance: the omega intersection separates all scanner classes. -/
theorem omega_intersection_separates {r s : ℕ}
    (h : ∀ n, scannerLabel n r = scannerLabel n s) : r = s := by
  have hmax := h (max r s)
  simp [scannerLabel, Nat.le_max_left, Nat.le_max_right] at hmax
  exact hmax

/-- Generic relation refinement order: `p` is finer than `q`. -/
def Refines {S : Type*} (p q : S → S → Prop) : Prop :=
  ∀ ⦃x y⦄, p x y → q x y

/-- Finite iteration of a relation-refinement operator. -/
def iterateRel {S : Type*}
    (R : (S → S → Prop) → (S → S → Prop))
    (p0 : S → S → Prop) : ℕ → (S → S → Prop)
  | 0 => p0
  | n + 1 => R (iterateRel R p0 n)

/-- The omega intersection of finite iterates of a refinement operator. -/
def omegaRel {S : Type*}
    (R : (S → S → Prop) → (S → S → Prop))
    (p0 : S → S → Prop) (x y : S) : Prop :=
  ∀ n, iterateRel R p0 n x y

/-- Abstract fixed-point version of Proposition B.1.  Once CTMC finite-measure
continuity establishes that the omega intersection is a fixed point, ordinary
monotonicity makes it the coarsest fixed refinement of the assay partition. -/
theorem omega_is_coarsest_fixed_refinement
    {S : Type*}
    (R : (S → S → Prop) → (S → S → Prop))
    (p0 : S → S → Prop)
    (hmono : ∀ {p q}, Refines p q → Refines (R p) (R q))
    (homega : R (omegaRel R p0) = omegaRel R p0) :
    R (omegaRel R p0) = omegaRel R p0 ∧
      ∀ q, Refines q p0 → R q = q → Refines q (omegaRel R p0) := by
  constructor
  · exact homega
  · intro q hqp0 hfix
    have hq_all : ∀ n, Refines q (iterateRel R p0 n) := by
      intro n
      induction n with
      | zero =>
          exact hqp0
      | succ n ih =>
          have hRq : Refines (R q) (R (iterateRel R p0 n)) := hmono ih
          intro x y hxy
          apply hRq
          rw [hfix]
          exact hxy
    intro x y hxy n
    exact hq_all n hxy

end Refinement
end ExactReductionLimits
