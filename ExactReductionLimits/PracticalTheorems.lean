import Mathlib
import ExactReductionLimits.TaskSufficiency
import ExactReductionLimits.ReductionDiagnostics
import ExactReductionLimits.CoordinateRepair
import ExactReductionLimits.ApproximateReduction
import ExactReductionLimits.Certification
import ExactReductionLimits.ScannerDiagnostics
import ExactReductionLimits.BoundedComplex

noncomputable section

/-!
# Practical theorem index

Stable wrappers for the constructive layer added on top of the paper: task
sufficiency, counterexamples, coordinate repair, approximate reduction, and
sound incomplete certification.
-/

namespace ExactReductionLimits
namespace Practical

/-- A concrete future-law witness refutes task-level predictive sufficiency. -/
theorem future_witness_refutes
    {State Current Law Rep : Type*}
    {T : PredictionTask State Current Law} {phi : State → Rep}
    (w : PredictionTask.FutureCounterexample T phi) :
    ¬ T.PredictivelySufficient phi :=
  PredictionTask.futureCounterexample_refutes w

/-- Exact rule-level closure is exactly the absence of an aggregate-rate witness. -/
theorem exact_macro_iff_no_witness
    {State Macro : Type*} [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro) :
    sys.MacroClosed phi ↔
      ¬ Nonempty (WeightedTransitionSystem.MacroCounterexample sys phi) :=
  WeightedTransitionSystem.macroClosed_iff_no_counterexample sys phi

/-- Zero-tolerance approximate rate closure collapses to exact closure. -/
theorem zero_rate_error_is_exact
    {State Macro : Type*} [DecidableEq Macro]
    (sys : WeightedTransitionSystem State) (phi : State → Macro)
    (relevant : Set State)
    (h : sys.ApproxMacroClosedOn phi relevant 0) :
    sys.MacroClosedOn phi relevant :=
  WeightedTransitionSystem.approxMacroClosedOn_zero_implies_exact
    sys phi relevant h

/-- Positive frontier: whenever the connected species type has already been
proved finite, its exact multiplicity vector is injective and therefore
sufficient for *any* present/future prediction task on mixtures. -/
theorem finite_species_coordinate_is_task_sufficient
    {Species Current Law : Type*} [Fintype Species] [DecidableEq Species]
    (T : PredictionTask (Multiset Species) Current Law) :
    T.Sufficient BoundedComplex.multiplicityVector :=
  PredictionTask.sufficient_of_injective T
    BoundedComplex.multiplicityVector
    BoundedComplex.multiplicityVector_injective

/-- Scanner case study: the missing global coordinate exactly determines the
entire survival law. -/
theorem scanner_missing_coordinate_is_sufficient (κ : ℝ) :
    DeterminesFutureLaw Scanner.remaining (Scanner.survivalLaw κ) :=
  Scanner.remaining_determines_survivalLaw κ

end Practical
end ExactReductionLimits
