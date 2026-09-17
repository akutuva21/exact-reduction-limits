import Mathlib
import ExactReductionLimits.Core

noncomputable section

/-!
# Processive scanner

The paper's first witness is represented by the two distances from the unique
scanner to the ends of a homogeneous path.  A finite local observable is
captured extensionally by a finite inspection radius and the translation
invariance it must satisfy in a sufficiently deep homogeneous interior.

This module proves the paper-specific locality obstruction, the Erlang
separation used by Theorem 2.2, the bounded scanner exit rate, and a finite
coefficient version of the Erlang linear-independence argument.
-/

namespace ExactReductionLimits
namespace Scanner

/-- Scanner position inside a homogeneous chain. -/
structure State where
  left : ℕ
  right : ℕ
  deriving DecidableEq, Repr

/-- Total chain length, including the scanner monomer. -/
def chainLength (x : State) : ℕ := x.left + x.right + 1

/-- Number of rate-`κ` events remaining, including the final Done event. -/
def remaining (x : State) : ℕ := x.right + 1

/-- The scanner lies beyond radius `R` from both boundaries. -/
def Deep (R : ℕ) (x : State) : Prop := R < x.left ∧ R < x.right

/-- Increasing the demanded depth only makes the predicate stronger. -/
theorem deep_mono {r R : ℕ} {x : State} (hrR : r ≤ R) (h : Deep R x) :
    Deep r x := by
  constructor <;> omega

/-- Semantic interface of one ordinary finite local site-graph observable. -/
structure LocalObservable where
  reach : ℕ
  value : State → ℤ
  deep_translation_invariant :
    ∀ ⦃x y : State⦄, chainLength x = chainLength y →
      Deep reach x → Deep reach y → value x = value y

/-- A finite vocabulary of local observables has a maximum inspection radius. -/
structure LocalFamily (n : ℕ) where
  obs : Fin n → LocalObservable
  reach : ℕ
  reach_bound : ∀ i, (obs i).reach ≤ reach

/-- Vector of all observables in a finite family. -/
def vector {n : ℕ} (F : LocalFamily n) (x : State) : Fin n → ℤ :=
  fun i => (F.obs i).value x

/-- First deep-interior witness. -/
def witnessA (R : ℕ) : State := ⟨R + 1, R + 3⟩

/-- Second deep-interior witness on the same chain, but one step closer to Done. -/
def witnessB (R : ℕ) : State := ⟨R + 2, R + 2⟩

@[simp] theorem witness_chainLength (R : ℕ) :
    chainLength (witnessA R) = chainLength (witnessB R) := by
  simp [chainLength, witnessA, witnessB]
  omega

@[simp] theorem witnessA_remaining (R : ℕ) :
    remaining (witnessA R) = R + 4 := by
  simp [remaining, witnessA]

@[simp] theorem witnessB_remaining (R : ℕ) :
    remaining (witnessB R) = R + 3 := by
  simp [remaining, witnessB]

/-- Lemma 2.1 at the semantic locality boundary: no finite bounded-radius local
vocabulary can distinguish two sufficiently deep positions on one homogeneous
chain. -/
theorem finite_local_family_cannot_locate_deep_scanner
    {n : ℕ} (F : LocalFamily n) :
    vector F (witnessA F.reach) = vector F (witnessB F.reach) := by
  funext i
  apply (F.obs i).deep_translation_invariant
  · exact witness_chainLength F.reach
  · apply deep_mono (F.reach_bound i)
    constructor <;> simp [Deep, witnessA] <;> omega
  · apply deep_mono (F.reach_bound i)
    constructor <;> simp [Deep, witnessB] <;> omega

/-- Erlang survival probability from a scan state with `r` rate-`κ` events left. -/
def erlangSurvival (κ : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-κ * t) *
    ∑ j in Finset.range r, (κ * t) ^ j / (Nat.factorial j : ℝ)

/-- Successive Erlang orders differ by exactly their new highest-order term. -/
theorem erlangSurvival_succ_sub (κ t : ℝ) (r : ℕ) :
    erlangSurvival κ (r + 1) t - erlangSurvival κ r t =
      Real.exp (-κ * t) * ((κ * t) ^ r / (Nat.factorial r : ℝ)) := by
  unfold erlangSurvival
  rw [Finset.sum_range_succ]
  ring

/-- At positive time and rate, increasing the remaining distance changes the
future Done marginal strictly. -/
theorem erlangSurvival_strict_succ
    (κ t : ℝ) (r : ℕ) (hκ : 0 < κ) (ht : 0 < t) :
    erlangSurvival κ r t < erlangSurvival κ (r + 1) t := by
  have hpow : 0 < (κ * t) ^ r := pow_pos (mul_pos hκ ht) _
  have hfac : 0 < (Nat.factorial r : ℝ) := by positivity
  have hexp : 0 < Real.exp (-κ * t) := Real.exp_pos _
  have hterm :
      0 < Real.exp (-κ * t) * ((κ * t) ^ r / (Nat.factorial r : ℝ)) :=
    mul_pos hexp (div_pos hpow hfac)
  have hdiff := erlangSurvival_succ_sub κ t r
  linarith

/-- Theorem 2.2: every finite local family has two reachable-style scanner
states with identical local coordinates but different future one-time Done
marginals.  The path-law conclusion follows a fortiori. -/
theorem no_finite_local_family_determines_future
    {n : ℕ} (F : LocalFamily n) (κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) :
    vector F (witnessA F.reach) = vector F (witnessB F.reach) ∧
    erlangSurvival κ (remaining (witnessA F.reach)) t ≠
      erlangSurvival κ (remaining (witnessB F.reach)) t := by
  constructor
  · exact finite_local_family_cannot_locate_deep_scanner F
  · rw [witnessA_remaining, witnessB_remaining]
    have hlt := erlangSurvival_strict_succ κ t (F.reach + 3) hκ ht
    exact ne_of_gt hlt

/-- Scanner execution modes used only for the global rate bound. -/
inductive Mode where
  | build
  | scan
  | done
  deriving DecidableEq, Repr

/-- Total exit rate of the abstract scanner mode. -/
def modeExitRate (λb λs κ : ℝ) : Mode → ℝ
  | .build => λb + λs
  | .scan => κ
  | .done => 0

/-- Proposition 2.5: one Append plus one Freeze in build mode, or one scanner
move in scan mode, gives the uniform bound. -/
theorem scanner_exitRate_bound
    (λb λs κ : ℝ) (hλb : 0 ≤ λb) (hλs : 0 ≤ λs) (hκ : 0 ≤ κ)
    (m : Mode) :
    modeExitRate λb λs κ m ≤ λb + λs + κ := by
  cases m <;> simp [modeExitRate] <;> linarith

/-- Coefficient of `t^j` after removing the common factor `exp(-κt)` from an
Erlang survival function of order `r`. -/
def erlangCoeff (κ : ℝ) (r j : ℕ) : ℝ :=
  if j < r then κ ^ j / (Nat.factorial j : ℝ) else 0

/-- Vanishing of a finite linear combination at the coefficient level. -/
def CoeffCombinationVanishes
    (κ : ℝ) (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ j, j < N →
    ∑ r in Finset.range N, c r * erlangCoeff κ (r + 1) j = 0

/-- The top coefficient in the first `N+1` Erlang orders comes only from the
largest order. -/
theorem top_erlang_coefficient
    (κ : ℝ) (N : ℕ) (c : ℕ → ℝ) :
    (∑ r in Finset.range (N + 1), c r * erlangCoeff κ (r + 1) N) =
      c N * (κ ^ N / (Nat.factorial N : ℝ)) := by
  rw [Finset.sum_range_succ]
  have hzero :
      (∑ r in Finset.range N, c r * erlangCoeff κ (r + 1) N) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    have hb' : b < N := Finset.mem_range.mp hb
    have hnot : ¬ N < b + 1 := by omega
    simp [erlangCoeff, hnot]
  rw [hzero, zero_add]
  simp [erlangCoeff]

/-- Lemma 2.6 in a coefficient-exact form: the exponential-stripped Erlang
polynomials of distinct orders are linearly independent whenever `κ ≠ 0`.
A standard polynomial-identity bridge turns function-level equality into this
coefficient statement; that bridge is recorded explicitly in
`ClassicalInterfaces.lean`. -/
theorem erlang_coefficients_linearly_independent
    (κ : ℝ) (hκ : κ ≠ 0) :
    ∀ N c, CoeffCombinationVanishes κ N c → ∀ r, r < N → c r = 0 := by
  intro N
  induction N with
  | zero =>
      intro c h r hr
      omega
  | succ N ih =>
      intro c h r hr
      have htop := h N (Nat.lt_succ_self N)
      rw [top_erlang_coefficient] at htop
      have hfactor : κ ^ N / (Nat.factorial N : ℝ) ≠ 0 := by
        apply div_ne_zero
        · exact pow_ne_zero N hκ
        · positivity
      have hcN : c N = 0 := by
        exact (mul_eq_zero.mp htop).resolve_right hfactor
      by_cases hrN : r = N
      · simpa [hrN] using hcN
      · have hrlt : r < N := by omega
        apply ih c
        · intro j hj
          have hfull := h j (lt_trans hj (Nat.lt_succ_self N))
          rw [Finset.sum_range_succ] at hfull
          simpa [hcN] using hfull
        · exact r
        · exact hrlt


/-- A nontrivial finite dependence among an initial segment of a sequence of
coefficient vectors. -/
def InitialSegmentDependent (family : ℕ → ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∃ c : ℕ → ℝ,
    (∃ r, r < N ∧ c r ≠ 0) ∧
    ∀ j, ∑ r in Finset.range N, c r * family r j = 0

/-- Erlang coefficient vectors indexed from order one. -/
def erlangCoeffFamily (κ : ℝ) (r j : ℕ) : ℝ :=
  erlangCoeff κ (r + 1) j

/-- No finite initial segment of the Erlang coefficient family has a nontrivial
linear dependence when `κ ≠ 0`. -/
theorem erlang_initial_segments_independent
    (κ : ℝ) (hκ : κ ≠ 0) :
    ¬ InitialSegmentDependent (erlangCoeffFamily κ) := by
  rintro ⟨N, c, ⟨r, hr, hcr⟩, hzero⟩
  have hvanish : CoeffCombinationVanishes κ N c := by
    intro j hj
    simpa [erlangCoeffFamily] using hzero j
  have hall := erlang_coefficients_linearly_independent κ hκ N c hvanish
  exact hcr (hall r hr)

end Scanner
end ExactReductionLimits
