import Mathlib
import ExactReductionLimits.TaskSufficiency
import ExactReductionLimits.ReductionDiagnostics

noncomputable section

/-!
# Approximate state sufficiency

Exact equality is often too strict for scientific modeling.  This module adds
an explicit error budget without pretending that an approximation is exact.
The key design is universal: every pair merged by the proposed representation
must disagree by at most `ε` in the quantity being protected.
-/

namespace ExactReductionLimits
namespace PredictionTask

variable {State Current Law Rep : Type*}

/-- Metric future-law analogue of exact predictive sufficiency. -/
def ApproxPredictivelySufficient
    [PseudoMetricSpace Law]
    (T : PredictionTask State Current Law) (phi : State → Rep) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ ⦃x y : State⦄, x ∈ T.relevant → y ∈ T.relevant → phi x = phi y →
      dist (T.future x) (T.future y) ≤ ε

/-- Exact predictive sufficiency implies every nonnegative error tolerance. -/
theorem exact_implies_approx
    [PseudoMetricSpace Law]
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (h : T.PredictivelySufficient phi) {ε : ℝ} (hε : 0 ≤ ε) :
    T.ApproxPredictivelySufficient phi ε := by
  constructor
  · exact hε
  · intro x y hx hy hphi
    rw [h hx hy hphi]
    simpa using hε

/-- In a genuine metric space, zero error recovers exact future-law
sufficiency. -/
theorem approx_zero_implies_exact
    [MetricSpace Law]
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (h : T.ApproxPredictivelySufficient phi 0) :
    T.PredictivelySufficient phi := by
  intro x y hx hy hphi
  have hle := h.2 hx hy hphi
  have hzero : dist (T.future x) (T.future y) = 0 := by
    exact le_antisymm hle (dist_nonneg)
  exact dist_eq_zero.mp hzero

/-- Increasing the allowed error cannot invalidate an approximate certificate. -/
theorem approx_mono
    [PseudoMetricSpace Law]
    {T : PredictionTask State Current Law} {phi : State → Rep}
    {ε δ : ℝ}
    (h : T.ApproxPredictivelySufficient phi ε) (hεδ : ε ≤ δ) :
    T.ApproxPredictivelySufficient phi δ := by
  constructor
  · exact le_trans h.1 hεδ
  · intro x y hx hy hphi
    exact le_trans (h.2 hx hy hphi) hεδ

/-- A concrete pair exceeding the error budget. -/
structure ApproxFutureViolation
    [PseudoMetricSpace Law]
    (T : PredictionTask State Current Law) (phi : State → Rep) (ε : ℝ) where
  x : State
  y : State
  x_relevant : x ∈ T.relevant
  y_relevant : y ∈ T.relevant
  sameRepresentation : phi x = phi y
  exceedsBudget : ε < dist (T.future x) (T.future y)

/-- A sharp future-law error certificate supplies both a valid uniform bound and
a relevant merged pair that attains it.  When such a certificate is available,
its `epsilon` is not merely a convenient tolerance: it is the smallest possible
uniform bound for this representation on this task. -/
structure SharpFutureErrorCertificate
    [PseudoMetricSpace Law]
    (T : PredictionTask State Current Law) (phi : State → Rep) where
  epsilon : ℝ
  valid : T.ApproxPredictivelySufficient phi epsilon
  x : State
  y : State
  x_relevant : x ∈ T.relevant
  y_relevant : y ∈ T.relevant
  sameRepresentation : phi x = phi y
  attained : dist (T.future x) (T.future y) = epsilon

/-- The attained sharp future-law bound is minimal among all valid uniform
bounds. -/
theorem SharpFutureErrorCertificate.minimal
    [PseudoMetricSpace Law]
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (C : SharpFutureErrorCertificate T phi) {δ : ℝ}
    (hδ : T.ApproxPredictivelySufficient phi δ) :
    C.epsilon ≤ δ := by
  rw [← C.attained]
  exact hδ.2 C.x_relevant C.y_relevant C.sameRepresentation

/-- One over-budget pair refutes the approximate certificate. -/
theorem approxFutureViolation_refutes
    [PseudoMetricSpace Law]
    {T : PredictionTask State Current Law} {phi : State → Rep} {ε : ℝ}
    (w : ApproxFutureViolation T phi ε) :
    ¬ T.ApproxPredictivelySufficient phi ε := by
  intro h
  have hle := h.2 w.x_relevant w.y_relevant w.sameRepresentation
  exact (not_lt_of_ge hle) w.exceedsBudget

end PredictionTask

namespace WeightedTransitionSystem

variable {State Macro : Type*} [DecidableEq Macro]

/-- Absolute aggregate-hazard discrepancy for one merged source pair and one
macro target. -/
def macroRateGap
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (x y : State) (z : Macro) : ℝ :=
  |macroRate sys phi x z - macroRate sys phi y z|

/-- Approximate strong lumpability on a restart set, with a uniform hazard error
budget `ε`. -/
def ApproxMacroClosedOn
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ ⦃x y : State⦄, x ∈ relevant → y ∈ relevant → phi x = phi y →
      ∀ z : Macro, z ≠ phi x → macroRateGap sys phi x y z ≤ ε

/-- Global shorthand for approximate closure over all microscopic states. -/
def ApproxMacroClosed
    (sys : WeightedTransitionSystem State) (phi : State → Macro) (ε : ℝ) : Prop :=
  sys.ApproxMacroClosedOn phi Set.univ ε

/-- Exact closure on a domain gives approximate closure at every nonnegative
error budget. -/
theorem macroClosedOn_implies_approx
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) {ε : ℝ} (hε : 0 ≤ ε)
    (h : sys.MacroClosedOn phi relevant) :
    sys.ApproxMacroClosedOn phi relevant ε := by
  constructor
  · exact hε
  · intro x y hx hy hxy z hz
    have heq := h hx hy hxy z hz
    simp [macroRateGap, heq, hε]

/-- Zero aggregate-rate error recovers exact macro closure. -/
theorem approxMacroClosedOn_zero_implies_exact
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State)
    (h : sys.ApproxMacroClosedOn phi relevant 0) :
    sys.MacroClosedOn phi relevant := by
  intro x y hx hy hxy z hz
  have hle := h.2 hx hy hxy z hz
  have habs : macroRateGap sys phi x y z = 0 := by
    exact le_antisymm hle (abs_nonneg _)
  unfold macroRateGap at habs
  have hsub : macroRate sys phi x z - macroRate sys phi y z = 0 :=
    abs_eq_zero.mp habs
  linarith

/-- Approximate closure is monotone in the error budget. -/
theorem approxMacroClosedOn_mono
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) {ε δ : ℝ}
    (h : sys.ApproxMacroClosedOn phi relevant ε) (hεδ : ε ≤ δ) :
    sys.ApproxMacroClosedOn phi relevant δ := by
  constructor
  · exact le_trans h.1 hεδ
  · intro x y hx hy hxy z hz
    exact le_trans (h.2 hx hy hxy z hz) hεδ

/-- A concrete aggregate-rate discrepancy larger than the declared tolerance. -/
structure ApproxMacroViolation
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) (ε : ℝ) where
  x : State
  y : State
  target : Macro
  x_relevant : x ∈ relevant
  y_relevant : y ∈ relevant
  sameMacro : phi x = phi y
  targetDifferent : target ≠ phi x
  exceedsBudget : ε < macroRateGap sys phi x y target

/-- A sharp rate-error certificate proves a uniform aggregate-hazard bound and
exhibits a merged pair/target that attains it.  This is a proof-oriented way to
report "how bad" a proposed macrostate is on a searched restart domain. -/
structure SharpMacroErrorCertificate
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State) where
  epsilon : ℝ
  valid : sys.ApproxMacroClosedOn phi relevant epsilon
  x : State
  y : State
  target : Macro
  x_relevant : x ∈ relevant
  y_relevant : y ∈ relevant
  sameMacro : phi x = phi y
  targetDifferent : target ≠ phi x
  attained : macroRateGap sys phi x y target = epsilon

/-- The attained rate discrepancy is the smallest valid uniform error budget. -/
theorem SharpMacroErrorCertificate.minimal
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {relevant : Set State}
    (C : SharpMacroErrorCertificate sys phi relevant) {δ : ℝ}
    (hδ : sys.ApproxMacroClosedOn phi relevant δ) :
    C.epsilon ≤ δ := by
  rw [← C.attained]
  exact hδ.2 C.x_relevant C.y_relevant C.sameMacro
    C.target C.targetDifferent

/-- One over-budget aggregate-rate witness refutes approximate lumpability. -/
theorem approxMacroViolation_refutes
    {sys : WeightedTransitionSystem State} {phi : State → Macro}
    {relevant : Set State} {ε : ℝ}
    (w : ApproxMacroViolation sys phi relevant ε) :
    ¬ sys.ApproxMacroClosedOn phi relevant ε := by
  intro h
  have hle := h.2 w.x_relevant w.y_relevant w.sameMacro
    w.target w.targetDifferent
  exact (not_lt_of_ge hle) w.exceedsBudget

end WeightedTransitionSystem
end ExactReductionLimits
