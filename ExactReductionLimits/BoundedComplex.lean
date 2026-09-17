import Mathlib

noncomputable section

/-!
# Bounded complexes and finite exact coordinates

Once a finite signature plus a uniform complex-size bound has reduced the set of
possible connected species to a finite type, a mixture is exactly its vector of
species multiplicities.  This is the algebraic core of Theorem 4.1.
-/

namespace ExactReductionLimits
namespace BoundedComplex

variable {Species : Type*} [Fintype Species] [DecidableEq Species]

/-- Species-count coordinate of a finite mixture. -/
def multiplicityVector (m : Multiset Species) : Species → ℕ :=
  fun s => Multiset.count s m

/-- A finite mixture is uniquely determined by all species counts. -/
theorem multiplicityVector_injective :
    Function.Injective (multiplicityVector : Multiset Species → Species → ℕ) := by
  intro a b h
  ext s
  have hs := congrFun h s
  simpa [multiplicityVector] using hs

/-- The bounded-complex certificate, after the graph-theoretic finiteness step:
there exists a finite-dimensional injective coordinate for the complete
microscopic mixture. -/
theorem finite_exact_coordinate :
    ∃ phi : Multiset Species → (Species → ℕ), Function.Injective phi := by
  exact ⟨multiplicityVector, multiplicityVector_injective⟩

/-- Finite coordinate dimension does not imply finite state cardinality: if one
species exists, arbitrarily large copy counts give pairwise distinct coordinate
values. -/
theorem unbounded_copy_number_gives_infinite_values
    (s : Species) :
    Function.Injective (fun n : ℕ => multiplicityVector (Multiset.replicate n s)) := by
  intro m n h
  have hs := congrFun h s
  simpa [multiplicityVector] using hs

end BoundedComplex
end ExactReductionLimits
