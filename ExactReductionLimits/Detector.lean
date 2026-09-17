import Mathlib

noncomputable section

/-!
# Nonhalting detector branch

The seed-level undecidability reduction couples a live Probe to the number of
simulated machine steps.  This module records the closed-form survival law and
kernel-proves the elementary infinite-pole geometry used in equations (9)-(11).
The analytic statement that the displayed series is the meromorphic continuation
is kept in the classical interface layer.
-/

namespace ExactReductionLimits
namespace Detector

/-- Equation (9). -/
def survival (γ κ t : ℝ) : ℝ :=
  Real.exp (γ / κ) * Real.exp (-(γ + κ) * t) *
    Real.exp (-(γ / κ) * Real.exp (-κ * t))

/-- Location of the `m`th pole in equation (11). -/
def pole (γ κ : ℝ) (m : ℕ) : ℝ :=
  -(γ + κ + (m : ℝ) * κ)

/-- For nonzero `κ`, all candidate poles are distinct. -/
theorem pole_injective (γ κ : ℝ) (hκ : κ ≠ 0) :
    Function.Injective (pole γ κ) := by
  intro m n h
  unfold pole at h
  have hmul : (m : ℝ) * κ = (n : ℝ) * κ := by
    linarith
  have hcast : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hκ hmul
  exact_mod_cast hcast

/-- Probe completion hazard after `n` simulated steps. -/
def completionHazard (κ : ℝ) (n : ℕ) : ℝ := κ * (n + 1)

/-- Distinct step counts have distinct instantaneous assay hazards when
`κ > 0`; this gives infinitely many future-law-distinguishable restart states
in the nonhalting branch. -/
theorem completionHazard_strict
    (κ : ℝ) (hκ : 0 < κ) {m n : ℕ} (hmn : m < n) :
    completionHazard κ m < completionHazard κ n := by
  unfold completionHazard
  have hcast : ((m + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ hmn
  have h1 : κ * ((m + 1 : ℕ) : ℝ) < κ * ((n + 1 : ℕ) : ℝ) := mul_lt_mul_of_pos_left hcast hκ
  simpa using h1

end Detector
end ExactReductionLimits
