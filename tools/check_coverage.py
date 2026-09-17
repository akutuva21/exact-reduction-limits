#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
coverage = (ROOT / "PAPER-COVERAGE.md").read_text()
lean = "\n".join(p.read_text() for p in ROOT.rglob("*.lean"))

required_paper_items = [
    "Def. 1.1", "Def. 1.2", "Def. 1.3",
    "Lemma 2.1", "Theorem 2.2", "Proposition 2.5", "Lemma 2.6",
    "Proposition 2.7", "Proposition 2.8",
    "Proposition 3.1", "Lemma 3.2", "Theorem 3.3", "Corollary 3.5",
    "Theorem 4.1", "Lemma 5.1", "Def. 6.1", "Theorem 6.2",
    "Def. 6.4", "Theorem 6.5", "Proposition B.1", "Remark B.2",
    "Lemma C.1", "Proposition C.2",
]

required_symbols = [
    "finite_local_family_cannot_locate_deep_scanner",
    "no_finite_local_family_determines_future",
    "scanner_exitRate_bound",
    "erlang_coefficients_linearly_independent",
    "seedTransform_eq_twoPhase",
    "exitRate_bound",
    "rho_quadratic",
    "no_finite_linear_realization_of_nonrational_completion",
    "finite_exact_coordinate",
    "zero_test_exact",
    "seed_finite_hidden_ctmc_undecidable",
    "finite_local_pattern_state_undecidable",
    "omega_is_coarsest_fixed_refinement",
    "omega_intersection_separates",
    "macroCriterion",
    "small_time_aggregate_expansion",
    "half_integer_tail",
    "phaseTypeDenseAtBusyPeriod",
    "bounded_order_convergence_impossible",
]

errors: list[str] = []
for item in required_paper_items:
    if item not in coverage:
        errors.append(f"coverage table missing {item}")
for symbol in required_symbols:
    if not re.search(rf"\b{re.escape(symbol)}\b", lean):
        errors.append(f"Lean/interface symbol missing: {symbol}")

if errors:
    print("COVERAGE: FAIL")
    for e in errors:
        print("-", e)
    sys.exit(1)

print("COVERAGE: PASS")
print(f"- {len(required_paper_items)} paper result labels tracked")
print(f"- {len(required_symbols)} proof/interface symbols present")
