#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

required = {
    "ExactReductionLimits/TaskSufficiency.lean": [
        "structure PredictionTask",
        "def PredictivelySufficient",
        "structure FutureCounterexample",
        "theorem sufficient_of_injective",
        "theorem sufficient_of_no_counterexamples",
    ],
    "ExactReductionLimits/ReductionDiagnostics.lean": [
        "structure MacroCounterexample",
        "theorem macroCounterexampleOn_refutes_global",
        "theorem macroClosed_iff_no_counterexample",
        "theorem macroClosedOn_of_complete_domain",
    ],
    "ExactReductionLimits/CoordinateRepair.lean": [
        "def augment",
        "def Separates",
        "structure FeatureLibrary",
        "theorem augment_determines_future_of_feature",
        "theorem augment_preserves_predictive_sufficiency",
    ],
    "ExactReductionLimits/ApproximateReduction.lean": [
        "def ApproxPredictivelySufficient",
        "def ApproxMacroClosedOn",
        "theorem approxMacroClosedOn_zero_implies_exact",
        "structure SharpMacroErrorCertificate",
    ],
    "ExactReductionLimits/Certification.lean": [
        "inductive Verdict",
        "structure DomainCertificate",
    ],
    "ExactReductionLimits/ScannerDiagnostics.lean": [
        "def survivalLaw",
        "theorem local_family_not_predictively_sufficient",
        "theorem remaining_is_predictively_sufficient",
    ],
    "ExactReductionLimits/PracticalTheorems.lean": [
        "namespace Practical",
        "theorem exact_macro_iff_no_witness",
        "theorem finite_species_coordinate_is_task_sufficient",
        "theorem scanner_missing_coordinate_is_sufficient",
    ],
}

errors: list[str] = []
for rel, needles in required.items():
    p = ROOT / rel
    if not p.exists():
        errors.append(f"missing file: {rel}")
        continue
    text = p.read_text()
    for needle in needles:
        if needle not in text:
            errors.append(f"{rel}: missing marker {needle!r}")

for rel in ["PRACTICAL-FRAMEWORK.md", "ELI10-PRACTICAL.md"]:
    if not (ROOT / rel).exists():
        errors.append(f"missing documentation: {rel}")

if errors:
    print("PRACTICAL CHECK: FAIL")
    for e in errors:
        print("-", e)
    sys.exit(1)

print("PRACTICAL CHECK: PASS")
print("- task-specific sufficiency layer present")
print("- exact counterexample diagnostics present")
print("- coordinate-repair contracts present")
print("- approximate reduction layer present")
print("- proof-carrying YES/NO/UNKNOWN API present")
print("- scanner end-to-end diagnostic example present")
