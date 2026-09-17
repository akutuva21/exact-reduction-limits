import Mathlib

noncomputable section

/-!
# Reversible active tip / M/M/1 busy-period algebra

The stochastic identification with the classical M/M/1 busy period is exposed
as a background interface.  This file kernel-proves the characteristic
quadratic, the physical root at `s = 0`, and the global rate bound used by the
paper's realization obstruction.
-/

namespace ExactReductionLimits
namespace ReversibleTip

/-- Discriminant of the busy-period quadratic. -/
def discr (λ μ s : ℝ) : ℝ := (s + λ + μ) ^ 2 - 4 * λ * μ

/-- The bounded root of the M/M/1 completion transform. -/
def rho (λ μ s : ℝ) : ℝ :=
  (s + λ + μ - Real.sqrt (discr λ μ s)) / (2 * λ)

/-- For `s ≥ 0` and positive rates, the discriminant is nonnegative. -/
theorem discr_nonneg
    (λ μ s : ℝ) (hλ : 0 ≤ λ) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    0 ≤ discr λ μ s := by
  unfold discr
  nlinarith [sq_nonneg (μ - λ)]

/-- The proposed transform solves the first-step quadratic. -/
theorem rho_quadratic
    (λ μ s : ℝ) (hλ : 0 < λ) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    λ * (rho λ μ s) ^ 2 - (s + λ + μ) * rho λ μ s + μ = 0 := by
  have hd : 0 ≤ discr λ μ s := discr_nonneg λ μ s (le_of_lt hλ) hμ hs
  have hsqrt : (Real.sqrt (discr λ μ s)) ^ 2 = discr λ μ s := by
    simpa using Real.sq_sqrt hd
  have hλ0 : λ ≠ 0 := ne_of_gt hλ
  unfold rho discr at *
  field_simp [hλ0]
  nlinarith

/-- In the stable regime `μ > λ > 0`, the bounded root satisfies `ρ(0)=1`. -/
theorem rho_zero
    (λ μ : ℝ) (hλ : 0 < λ) (hstable : λ < μ) :
    rho λ μ 0 = 1 := by
  have hdiff : 0 ≤ μ - λ := by linarith
  have hsqrt : Real.sqrt ((μ - λ) ^ 2) = μ - λ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff]
  have hλ0 : λ ≠ 0 := ne_of_gt hλ
  unfold rho discr
  rw [show (0 + λ + μ) ^ 2 - 4 * λ * μ = (μ - λ) ^ 2 by ring]
  rw [hsqrt]
  field_simp [hλ0]
  ring

/-- Abstract active-tip execution modes. -/
inductive Mode where
  | active
  | done
  deriving DecidableEq, Repr

/-- Exactly one Push and one Pop match are present at positive active length. -/
def exitRate (λ μ : ℝ) : Mode → ℝ
  | .active => λ + μ
  | .done => 0

/-- Proposition 3.1. -/
theorem exitRate_bound
    (λ μ : ℝ) (hλ : 0 ≤ λ) (hμ : 0 ≤ μ) (m : Mode) :
    exitRate λ μ m ≤ λ + μ := by
  cases m <;> simp [exitRate] <;> linarith

/-- Survival-transform relation used in equation (5), represented without
committing to a particular integration library. -/
def SurvivalCompletionRelation (ρ S : ℝ → ℝ) : Prop :=
  ∀ s, ρ s = 1 - s * S s

end ReversibleTip
end ExactReductionLimits
