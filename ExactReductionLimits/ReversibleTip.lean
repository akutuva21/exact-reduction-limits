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
def discr (lam μ s : ℝ) : ℝ := (s + lam + μ) ^ 2 - 4 * lam * μ

/-- The bounded root of the M/M/1 completion transform. -/
def rho (lam μ s : ℝ) : ℝ :=
  (s + lam + μ - Real.sqrt (discr lam μ s)) / (2 * lam)

/-- For `s ≥ 0` and positive rates, the discriminant is nonnegative. -/
theorem discr_nonneg
    (lam μ s : ℝ) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    0 ≤ discr lam μ s := by
  unfold discr
  nlinarith [sq_nonneg (μ - lam)]

/-- The proposed transform solves the first-step quadratic. -/
theorem rho_quadratic
    (lam μ s : ℝ) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    lam * (rho lam μ s) ^ 2 - (s + lam + μ) * rho lam μ s + μ = 0 := by
  have hd : 0 ≤ discr lam μ s := discr_nonneg lam μ s (le_of_lt hlam) hμ hs
  have hsqrt : (Real.sqrt (discr lam μ s)) ^ 2 = discr lam μ s := Real.sq_sqrt hd
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hdiscr_eq : discr lam μ s = (s + lam + μ) ^ 2 - 4 * lam * μ := by
    unfold discr; ring
  have hsqrt' : (Real.sqrt ((s + lam + μ) ^ 2 - 4 * lam * μ)) ^ 2 = (s + lam + μ) ^ 2 - 4 * lam * μ := by
    rw [← hdiscr_eq]; exact hsqrt
  unfold rho
  field_simp [hlam0, h2]
  nlinarith [hsqrt', hdiscr_eq, sq_nonneg (Real.sqrt ((s + lam + μ) ^ 2 - 4 * lam * μ)), sq_nonneg (s + lam + μ), sq_nonneg lam, sq_nonneg μ, sq_nonneg s]

/-- In the stable regime `μ > lam > 0`, the bounded root satisfies `ρ(0)=1`. -/
theorem rho_zero
    (lam μ : ℝ) (hlam : 0 < lam) (hstable : lam < μ) :
    rho lam μ 0 = 1 := by
  have hdiff : 0 ≤ μ - lam := by linarith
  have hsqrt : Real.sqrt ((μ - lam) ^ 2) = μ - lam := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff]
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  unfold rho discr
  rw [show (0 + lam + μ) ^ 2 - 4 * lam * μ = (μ - lam) ^ 2 by ring]
  rw [hsqrt]
  field_simp [hlam0]
  ring

/-- Abstract active-tip execution modes. -/
inductive Mode where
  | active
  | done
  deriving DecidableEq, Repr

/-- Exactly one Push and one Pop match are present at positive active length. -/
def exitRate (lam μ : ℝ) : Mode → ℝ
  | .active => lam + μ
  | .done => 0

/-- Proposition 3.1. -/
theorem exitRate_bound
    (lam μ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (m : Mode) :
    exitRate lam μ m ≤ lam + μ := by
  cases m <;> simp [exitRate] <;> linarith

/-- Survival-transform relation used in equation (5), represented without
committing to a particular integration library. -/
def SurvivalCompletionRelation (ρ S : ℝ → ℝ) : Prop :=
  ∀ s, ρ s = 1 - s * S s

end ReversibleTip
end ExactReductionLimits
