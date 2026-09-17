import Mathlib
import ExactReductionLimits.Core

noncomputable section

/-!
# Task-specific state sufficiency

The negative results in the paper are useful only after fixing the prediction
problem.  This module therefore makes the task explicit: which microscopic
states are relevant, what is observed now, and which exact future law is to be
preserved.

A proposed state representation is sufficient only relative to such a task.
The definitions here are intentionally independent of Kappa/BNGL syntax.
-/

namespace ExactReductionLimits

/-- A prediction task specifies the restart states of interest, the present
assay, and the exact future-law object that must be preserved. -/
structure PredictionTask (State Current Law : Type*) where
  relevant : Set State
  current : State → Current
  future : State → Law

namespace PredictionTask

variable {State Current Law Rep : Type*}

/-- The representation does not merge two relevant states that have different
current assay values. -/
def CurrentCompatible
    (T : PredictionTask State Current Law) (phi : State → Rep) : Prop :=
  ∀ ⦃x y : State⦄, x ∈ T.relevant → y ∈ T.relevant →
    phi x = phi y → T.current x = T.current y

/-- Equal reduced states imply equal exact future laws on the restart set of
interest.  This is the main task-relative notion of predictive sufficiency. -/
def PredictivelySufficient
    (T : PredictionTask State Current Law) (phi : State → Rep) : Prop :=
  ∀ ⦃x y : State⦄, x ∈ T.relevant → y ∈ T.relevant →
    phi x = phi y → T.future x = T.future y

/-- A state representation is task-sufficient when it preserves both the
present assay and the exact future law. -/
def Sufficient
    (T : PredictionTask State Current Law) (phi : State → Rep) : Prop :=
  T.CurrentCompatible phi ∧ T.PredictivelySufficient phi

/-- Concrete witness that a proposed representation loses present-assay
information. -/
structure CurrentCounterexample
    (T : PredictionTask State Current Law) (phi : State → Rep) where
  x : State
  y : State
  x_relevant : x ∈ T.relevant
  y_relevant : y ∈ T.relevant
  sameRepresentation : phi x = phi y
  differentCurrent : T.current x ≠ T.current y

/-- Concrete witness that a proposed representation loses future-predictive
information. -/
structure FutureCounterexample
    (T : PredictionTask State Current Law) (phi : State → Rep) where
  x : State
  y : State
  x_relevant : x ∈ T.relevant
  y_relevant : y ∈ T.relevant
  sameRepresentation : phi x = phi y
  differentFuture : T.future x ≠ T.future y

/-- One current-assay counterexample is enough to refute compatibility. -/
theorem currentCounterexample_refutes
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (w : CurrentCounterexample T phi) :
    ¬ T.CurrentCompatible phi := by
  intro h
  exact w.differentCurrent
    (h w.x_relevant w.y_relevant w.sameRepresentation)

/-- One future-law counterexample is enough to refute predictive sufficiency. -/
theorem futureCounterexample_refutes
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (w : FutureCounterexample T phi) :
    ¬ T.PredictivelySufficient phi := by
  intro h
  exact w.differentFuture
    (h w.x_relevant w.y_relevant w.sameRepresentation)

/-- Any injective representation is sufficient for every prediction task,
because it never merges distinct microscopic states.  This is the generic
positive certificate used by the bounded-complex result. -/
theorem sufficient_of_injective
    (T : PredictionTask State Current Law) (phi : State → Rep)
    (hinj : Function.Injective phi) :
    T.Sufficient phi := by
  constructor
  · intro x y hx hy hphi
    have hxy : x = y := hinj hphi
    subst y
    rfl
  · intro x y hx hy hphi
    have hxy : x = y := hinj hphi
    subst y
    rfl

/-- Exact sufficiency excludes every current-assay counterexample. -/
theorem sufficient_has_no_current_counterexample
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (h : T.Sufficient phi) :
    ¬ Nonempty (CurrentCounterexample T phi) := by
  rintro ⟨w⟩
  exact (currentCounterexample_refutes w) h.1

/-- Exact sufficiency excludes every future-law counterexample. -/
theorem sufficient_has_no_future_counterexample
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (h : T.Sufficient phi) :
    ¬ Nonempty (FutureCounterexample T phi) := by
  rintro ⟨w⟩
  exact (futureCounterexample_refutes w) h.2

/-- Conversely, if neither kind of concrete collision exists, the representation
is task-sufficient.  This is the logical basis of counterexample-guided state
discovery. -/
theorem sufficient_of_no_counterexamples
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (hcur : ¬ Nonempty (CurrentCounterexample T phi))
    (hfut : ¬ Nonempty (FutureCounterexample T phi)) :
    T.Sufficient phi := by
  constructor
  · intro x y hx hy hphi
    by_contra hne
    apply hcur
    exact ⟨{
      x := x
      y := y
      x_relevant := hx
      y_relevant := hy
      sameRepresentation := hphi
      differentCurrent := hne
    }⟩
  · intro x y hx hy hphi
    by_contra hne
    apply hfut
    exact ⟨{
      x := x
      y := y
      x_relevant := hx
      y_relevant := hy
      sameRepresentation := hphi
      differentFuture := hne
    }⟩

/-- Restrict a task to a smaller restart set while keeping the same assay and
future law. -/
def restrict
    (T : PredictionTask State Current Law) (S : Set State) :
    PredictionTask State Current Law where
  relevant := T.relevant ∩ S
  current := T.current
  future := T.future

/-- Predictive sufficiency on a larger restart set immediately implies
sufficiency on any smaller restart set. -/
theorem predictiveSufficiency_mono
    {T : PredictionTask State Current Law} {phi : State → Rep}
    {S : Set State}
    (h : T.PredictivelySufficient phi) :
    (T.restrict S).PredictivelySufficient phi := by
  intro x y hx hy hphi
  exact h hx.1 hy.1 hphi

/-- Present-assay compatibility is likewise monotone under restriction of the
restart set. -/
theorem currentCompatibility_mono
    {T : PredictionTask State Current Law} {phi : State → Rep}
    {S : Set State}
    (h : T.CurrentCompatible phi) :
    (T.restrict S).CurrentCompatible phi := by
  intro x y hx hy hphi
  exact h hx.1 hy.1 hphi

end PredictionTask
end ExactReductionLimits
