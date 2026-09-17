import Mathlib
import ExactReductionLimits.Scanner

noncomputable section

/-!
# Designated scanner seed: exact two-phase completion

This module formalizes the algebra behind Proposition 2.8.  The stochastic
first-event argument producing the recurrence is part of the CTMC interface;
starting from that recurrence, the bounded solution and the two-positive-root
factorization are exact Lean theorems here.
-/

namespace ExactReductionLimits
namespace ScannerSeed

/-- Build-mode first-event coefficients. -/
def u (λb λs s : ℝ) : ℝ := λb / (λb + λs + s)
def v (λb λs s : ℝ) : ℝ := λs / (λb + λs + s)
def w (κ s : ℝ) : ℝ := κ / (κ + s)

/-- Closed-form bounded solution of `F_n = u F_{n+1} + v w^n`. -/
def recurrenceSolution (u v w : ℝ) (n : ℕ) : ℝ :=
  v * w ^ n / (1 - u * w)

/-- The proposed solution satisfies the scanner recurrence. -/
theorem recurrenceSolution_step
    (u v w : ℝ) (n : ℕ) (hden : 1 - u * w ≠ 0) :
    recurrenceSolution u v w n =
      u * recurrenceSolution u v w (n + 1) + v * w ^ n := by
  unfold recurrenceSolution
  field_simp [hden]
  ring

/-- Equation (2) from the paper. -/
def seedTransform (λb λs κ s : ℝ) : ℝ :=
  λs * κ / (s ^ 2 + (λb + λs + κ) * s + λs * κ)

/-- The first-event closed form at chain length one simplifies to equation (2). -/
theorem recurrence_at_one_eq_seedTransform
    (λb λs κ s : ℝ)
    (hbuild : λb + λs + s ≠ 0)
    (hscan : κ + s ≠ 0)
    (hden : 1 - u λb λs s * w κ s ≠ 0) :
    recurrenceSolution (u λb λs s) (v λb λs s) (w κ s) 1 =
      seedTransform λb λs κ s := by
  unfold recurrenceSolution u v w seedTransform
  field_simp [hbuild, hscan, hden]
  ring

/-- Discriminant of the quadratic denominator in equation (2). -/
def discr (λb λs κ : ℝ) : ℝ :=
  (λb + λs + κ) ^ 2 - 4 * λs * κ

/-- The scanner-seed discriminant is nonnegative for physical nonnegative
rates. -/
theorem discr_nonneg
    (λb λs κ : ℝ) (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ) :
    0 ≤ discr λb λs κ := by
  unfold discr
  nlinarith [sq_nonneg (λs - κ)]

/-- The two transient phase rates obtained by factoring the denominator. -/
def phaseA (λb λs κ : ℝ) : ℝ :=
  ((λb + λs + κ) + Real.sqrt (discr λb λs κ)) / 2

def phaseB (λb λs κ : ℝ) : ℝ :=
  ((λb + λs + κ) - Real.sqrt (discr λb λs κ)) / 2

/-- The phase rates sum to the coefficient of `s`. -/
theorem phase_sum (λb λs κ : ℝ) :
    phaseA λb λs κ + phaseB λb λs κ = λb + λs + κ := by
  unfold phaseA phaseB
  ring

/-- Their product is `λs κ`. -/
theorem phase_product
    (λb λs κ : ℝ) (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ) :
    phaseA λb λs κ * phaseB λb λs κ = λs * κ := by
  have hd : 0 ≤ discr λb λs κ := discr_nonneg λb λs κ hλb hλs hκ
  have hsqrt : (Real.sqrt (discr λb λs κ)) ^ 2 = discr λb λs κ := by
    simpa using Real.sq_sqrt hd
  unfold phaseA phaseB discr at *
  nlinarith


/-- Both transient phase rates are strictly positive when `λs` and `κ` are
strictly positive and `λb` is nonnegative. -/
theorem phase_rates_pos
    (λb λs κ : ℝ) (hλb : 0 ≤ λb) (hλs : 0 < λs) (hκ : 0 < κ) :
    0 < phaseA λb λs κ ∧ 0 < phaseB λb λs κ := by
  have hd : 0 ≤ discr λb λs κ :=
    discr_nonneg λb λs κ hλb (le_of_lt hλs) (le_of_lt hκ)
  have hsqrt : 0 ≤ Real.sqrt (discr λb λs κ) := Real.sqrt_nonneg _
  have hsumpos : 0 < λb + λs + κ := by linarith
  have hA : 0 < phaseA λb λs κ := by
    unfold phaseA
    linarith
  have hprod := phase_product λb λs κ hλb (le_of_lt hλs) (le_of_lt hκ)
  have hprodpos : 0 < phaseA λb λs κ * phaseB λb λs κ := by
    rw [hprod]
    exact mul_pos hλs hκ
  have hB : 0 < phaseB λb λs κ :=
    pos_of_mul_pos_left hprodpos (le_of_lt hA)
  exact ⟨hA, hB⟩

/-- Two-phase absorption transform. -/
def twoPhaseTransform (a b s : ℝ) : ℝ :=
  (a / (s + a)) * (b / (s + b))

/-- Algebraic factorization of the scanner seed transform into two exponential
phases. -/
theorem seedTransform_eq_twoPhase
    (λb λs κ s : ℝ)
    (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ)
    (hA : s + phaseA λb λs κ ≠ 0)
    (hB : s + phaseB λb λs κ ≠ 0)
    (hQ : s ^ 2 + (λb + λs + κ) * s + λs * κ ≠ 0) :
    seedTransform λb λs κ s =
      twoPhaseTransform (phaseA λb λs κ) (phaseB λb λs κ) s := by
  have hsum := phase_sum λb λs κ
  have hprod := phase_product λb λs κ hλb hλs hκ
  unfold seedTransform twoPhaseTransform
  field_simp [hA, hB, hQ]
  nlinarith

end ScannerSeed
end ExactReductionLimits
