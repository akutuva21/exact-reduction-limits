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
def u (lb ls s : ℝ) : ℝ := lb / (lb + ls + s)
def v (lb ls s : ℝ) : ℝ := ls / (lb + ls + s)
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
def seedTransform (lb ls κ s : ℝ) : ℝ :=
  ls * κ / (s ^ 2 + (lb + ls + κ) * s + ls * κ)

/-- The first-event closed form at chain length one simplifies to equation (2). -/
theorem recurrence_at_one_eq_seedTransform
    (lb ls κ s : ℝ)
    (hbuild : lb + ls + s ≠ 0)
    (hscan : κ + s ≠ 0)
    (hden : 1 - u lb ls s * w κ s ≠ 0) :
    recurrenceSolution (u lb ls s) (v lb ls s) (w κ s) 1 =
      seedTransform lb ls κ s := by
  unfold recurrenceSolution u v w seedTransform
  field_simp [hbuild, hscan, hden]
  ring

/-- Discriminant of the quadratic denominator in equation (2). -/
def discr (lb ls κ : ℝ) : ℝ :=
  (lb + ls + κ) ^ 2 - 4 * ls * κ

/-- The scanner-seed discriminant is nonnegative for physical nonnegative
rates. -/
theorem discr_nonneg
    (lb ls κ : ℝ) (hlb : 0 ≤ lb) (hls : 0 ≤ ls) (hκ : 0 ≤ κ) :
    0 ≤ discr lb ls κ := by
  unfold discr
  nlinarith [sq_nonneg (ls - κ)]

/-- The two transient phase rates obtained by factoring the denominator. -/
def phaseA (lb ls κ : ℝ) : ℝ :=
  ((lb + ls + κ) + Real.sqrt (discr lb ls κ)) / 2

def phaseB (lb ls κ : ℝ) : ℝ :=
  ((lb + ls + κ) - Real.sqrt (discr lb ls κ)) / 2

/-- The phase rates sum to the coefficient of `s`. -/
theorem phase_sum (lb ls κ : ℝ) :
    phaseA lb ls κ + phaseB lb ls κ = lb + ls + κ := by
  unfold phaseA phaseB
  ring

/-- Their product is `ls κ`. -/
theorem phase_product
    (lb ls κ : ℝ) (hlb : 0 ≤ lb) (hls : 0 ≤ ls) (hκ : 0 ≤ κ) :
    phaseA lb ls κ * phaseB lb ls κ = ls * κ := by
  have hd : 0 ≤ discr lb ls κ := discr_nonneg lb ls κ hlb hls hκ
  have hsqrt : (Real.sqrt (discr lb ls κ)) ^ 2 = discr lb ls κ := by
    simpa using Real.sq_sqrt hd
  unfold phaseA phaseB discr at *
  nlinarith


/-- Both transient phase rates are strictly positive when `ls` and `κ` are
strictly positive and `lb` is nonnegative. -/
theorem phase_rates_pos
    (lb ls κ : ℝ) (hlb : 0 ≤ lb) (hls : 0 < ls) (hκ : 0 < κ) :
    0 < phaseA lb ls κ ∧ 0 < phaseB lb ls κ := by
  have hd : 0 ≤ discr lb ls κ :=
    discr_nonneg lb ls κ hlb (le_of_lt hls) (le_of_lt hκ)
  have hsqrt : 0 ≤ Real.sqrt (discr lb ls κ) := Real.sqrt_nonneg _
  have hsumpos : 0 < lb + ls + κ := by linarith
  have hA : 0 < phaseA lb ls κ := by
    unfold phaseA
    linarith
  have hprod := phase_product lb ls κ hlb (le_of_lt hls) (le_of_lt hκ)
  have hprodpos : 0 < phaseA lb ls κ * phaseB lb ls κ := by
    rw [hprod]
    exact mul_pos hls hκ
  have hB : 0 < phaseB lb ls κ := by
    nlinarith [hprodpos, le_of_lt hA]
  exact ⟨hA, hB⟩

/-- Two-phase absorption transform. -/
def twoPhaseTransform (a b s : ℝ) : ℝ :=
  (a / (s + a)) * (b / (s + b))

/-- Algebraic factorization of the scanner seed transform into two exponential
phases. -/
theorem seedTransform_eq_twoPhase
    (lb ls κ s : ℝ)
    (hlb : 0 ≤ lb) (hls : 0 ≤ ls) (hκ : 0 ≤ κ)
    (hA : s + phaseA lb ls κ ≠ 0)
    (hB : s + phaseB lb ls κ ≠ 0)
    (hQ : s ^ 2 + (lb + ls + κ) * s + ls * κ ≠ 0) :
    seedTransform lb ls κ s =
      twoPhaseTransform (phaseA lb ls κ) (phaseB lb ls κ) s := by
  have hsum := phase_sum lb ls κ
  have hprod := phase_product lb ls κ hlb hls hκ
  have hden : (s + phaseA lb ls κ) * (s + phaseB lb ls κ) = s ^ 2 + (lb + ls + κ) * s + ls * κ := by
    calc (s + phaseA lb ls κ) * (s + phaseB lb ls κ)
        = s ^ 2 + (phaseA lb ls κ + phaseB lb ls κ) * s + phaseA lb ls κ * phaseB lb ls κ := by ring
      _ = s ^ 2 + (lb + ls + κ) * s + ls * κ := by rw [hsum, hprod]
  unfold seedTransform twoPhaseTransform
  rw [← hden]
  field_simp [hA, hB, hQ]
  exact hprod.symm

end ScannerSeed
end ExactReductionLimits
