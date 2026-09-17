import Mathlib

noncomputable section

/-!
# Core notions for exact state reduction

This file formalizes the logical distinctions used throughout the paper:
observation compatibility, finite local statistics, exact prediction, and
Boolean decidability.  Stochastic-process-specific semantics are layered on top
in later modules.
-/

namespace ExactReductionLimits

/-- A deterministic experimental readout. -/
abbrev Assay (State Output : Type*) := State → Output

/-- Two microscopic states are observationally compatible for an assay when
that assay gives them the same current value. -/
def ObservationCompatible {State Output : Type*}
    (h : Assay State Output) (x y : State) : Prop := h x = h y

/-- A generic future-law descriptor.  The project deliberately keeps the
codomain abstract: it can be a path law, a family of one-time marginals, a
Laplace transform, or any other exact law representation. -/
structure FutureLaw (State Law : Type*) where
  law : State → Law

/-- Equality of future assay laws from two restart states. -/
def SameFutureLaw {State Law : Type*} (F : FutureLaw State Law)
    (x y : State) : Prop := F.law x = F.law y

/-- A finite vector of rule-native observables. -/
structure FiniteLocalStatistic (State : Type*) where
  dimension : ℕ
  value : State → Fin dimension → ℤ

/-- A statistic determines an exact future law when equal statistic values imply
identical future laws. -/
def DeterminesFutureLaw {State Law : Type*}
    (phi : State → Law) (F : State → Law) : Prop :=
  ∀ ⦃x y : State⦄, phi x = phi y → F x = F y

/-- A Boolean program decides a predicate when it returns true exactly on the
positive instances. -/
def Decides {α : Type*} (P : α → Prop) (d : α → Bool) : Prop :=
  ∀ x, d x = true ↔ P x

/-- Computable decidability in the explicit Boolean-program sense used by the
many-one reductions below. -/
def DecidableByBool {α : Type*} (P : α → Prop) : Prop :=
  ∃ d : α → Bool, Decides P d

/-- Undecidability in the Boolean-program sense. -/
def UndecidableByBool {α : Type*} (P : α → Prop) : Prop :=
  ¬ DecidableByBool P

/-- A standard many-one transfer lemma. -/
theorem undecidable_of_iff_reduction
    {α β : Type*} {P : α → Prop} {Q : β → Prop}
    (hP : UndecidableByBool P)
    (compile : α → β)
    (correct : ∀ x, P x ↔ Q (compile x)) :
    UndecidableByBool Q := by
  intro hQ
  rcases hQ with ⟨dQ, hdQ⟩
  apply hP
  refine ⟨fun x => dQ (compile x), ?_⟩
  intro x
  exact (hdQ (compile x)).trans (correct x).symm

/-- A property that is constant on fibers of a statistic factors through the
statistic, provided the statistic is surjective.  This elementary fact is used
repeatedly when turning microscopic rates into a macro generator. -/
theorem factor_through_surjection
    {State Macro Value : Type*}
    (phi : State → Macro) (f : State → Value)
    (hsurj : Function.Surjective phi)
    (hfiber : ∀ ⦃x y⦄, phi x = phi y → f x = f y) :
    ∃ g : Macro → Value, f = g ∘ phi := by
  classical
  choose rep hrep using hsurj
  refine ⟨fun z => f (rep z), ?_⟩
  funext x
  simp only [Function.comp_apply]
  exact hfiber (hrep (phi x)).symm

end ExactReductionLimits
