# Paper coverage map

Canonical source: **Local Rules Can Require Nonlocal Coordinates and
Infinite-State Realizations: Limits of exact reduction in Kappa/BNGL**.

Status meanings:

- **proved** - paper-specific statement or algebra is implemented as a Lean proof;
- **proved + bridge** - the paper-specific part is proved, with one clearly named
  classical/semantic bridge required for the exact source-language statement;
- **interface** - the statement is classical background reused by the paper and
  represented as an explicit typed input rather than re-proved here.

| Paper item | Lean declaration / interface | Status |
|---|---|---|
| Def. 1.1 observation-compatible strong lumping | `ObservationCompatible`; CTMC part in `CountableCTMCBackground` | proved + bridge |
| Def. 1.2 finite local pattern statistic | `FiniteLocalStatistic`; `Scanner.LocalFamily` | proved + bridge |
| Def. 1.3 finite hidden CTMC realization | realization bridge in `LinearBackground` | interface |
| Eq. (1) Erlang scanner survival | `Scanner.erlangSurvival` | proved definition |
| Lemma 2.1 finite patterns cannot locate deep scanner | `Scanner.finite_local_family_cannot_locate_deep_scanner`; `LocalPatternBridge` | proved + bridge |
| Theorem 2.2 no finite local pattern family determines future assay law | `Paper.theorem_2_2` | proved + bridge |
| Remark 2.3 BNGL Species/functionals | `LocalPatternBridge.bngl_species_observables_obey_same_deep_locality`, `.fixed_functions_preserve_indistinguishability` | interface |
| Remark 2.4 counter escape hatch | nonlocal `Scanner.remaining`; Kappa counter syntax bridge | proved + bridge |
| Proposition 2.5 uniform nonexplosion/rate bound | `Paper.proposition_2_5`; CTMC bounded-rate=>nonexplosion bridge | proved + bridge |
| Lemma 2.6 Erlang linear independence | `Paper.lemma_2_6`; `ErlangPolynomialBridge` | proved + bridge |
| Proposition 2.7 no finite hidden model for all restarts | `LinearRealization.no_model_if_independent_and_finite_rank` + Erlang bridge | proved + bridge |
| Equation (2) scanner seed transform | `ScannerSeed.seedTransform`; `recurrence_at_one_eq_seedTransform` | proved |
| Proposition 2.8 exact three-state seed realization | `Paper.proposition_2_8`, `ScannerSeed.phase_rates_pos` | proved + standard CTMC bridge |
| Equation (3) reversible-tip birth/death process | `BusyPeriodCTMCBridge.active_length_is_birth_death` | interface |
| Proposition 3.1 uniform nonexplosion/rate bound | `Paper.proposition_3_1` | proved + bridge |
| Equation (4) busy-period root | `ReversibleTip.rho` | proved definition |
| Lemma 3.2 completion transform/quadratic and non-rationality | `Paper.lemma_3_2_quadratic`; `BusyPeriodBackground.completion_nonrational` | proved + bridge |
| Equation (5) survival/completion transform relation | `ReversibleTip.SurvivalCompletionRelation` | formalized relation |
| Theorem 3.3 no finite-dimensional realization | `LinearRealization.no_finite_linear_realization_of_nonrational_completion` | proved + bridge |
| Corollary 3.5 half-integer tail | `BusyPeriodBackground.half_integer_tail` (typed asymptotic equivalence) | interface |
| Corollary 3.5 unbounded approximation order | `BusyPeriodBackground.bounded_order_convergence_impossible` (typed unbounded-order statement) | interface |
| Theorem 4.1 bounded-complex certificate | `Paper.theorem_4_1`; `BoundedGraphBackground` | proved + bridge |
| Lemma 5.1 finite ordinary-Kappa two-counter encoding | `CounterMachine.*`; `KappaCounterBridge` | proved + bridge |
| Def. 6.1 Seed-Finite-Hidden-CTMC | `Undecidability.SeedReduction` property field | formalized |
| Theorem 6.2 seed-level realization undecidable | `Paper.theorem_6_2` | proved + compiler/CM2 bridge |
| Eq. (9) nonhalting survival closed form | `Detector.survival` | formalized definition; Poisson derivation interface |
| Eq. (10) exponential series | `DetectorAnalyticBackground.exponential_series_eq` | interface |
| Eq. (11) infinitely many Laplace poles | `Detector.pole`, `Detector.pole_injective`; analytic continuation interface | proved + bridge |
| Def. 6.4 Finite-Local-Pattern-State | `Undecidability.LocalReduction` property field | formalized |
| Theorem 6.5 reusable finite-local-pattern exactness undecidable | `Paper.theorem_6_5` | proved + compiler/CM2 bridge |
| Uniform bound in Thm. 6.5 | `Undecidability.reusableReduction_rate_bound` | proved |
| Remark 6.6 decision notions differ | `Undecidability.notions_separate` | proved |
| Proposition B.1 omega limit is coarsest strong lumping | `Refinement.omega_is_coarsest_fixed_refinement`; `CountableCTMCBackground` | proved + measure bridge |
| Remark B.2 scanner sharpness | `Paper.remark_B_2_finite`, `Paper.remark_B_2_omega` | proved |
| Remark B.3 finite total rate vs finite branching | `CountableCTMCBackground.finite_rate_continuity_from_above` | interface |
| Equation (12) rule generator | `WeightedTransitionSystem.generator` | proved definition |
| Equation (13) macro-event rate | `WeightedTransitionSystem.macroRate` | proved definition |
| Lemma C.1 small-time aggregate expansion | `CountableCTMCBackground.small_time_aggregate_expansion` | interface |
| Proposition C.2 macro-event criterion | `Paper.proposition_C_2` + CTMC small-time bridge | proved + bridge |
| Remark C.3 arbitrary BNGL rate laws absorbed into match hazard | generic `WeightedTransitionSystem` real-valued match hazards | formalized semantic design |

## Non-theorem prose

Sections on novelty, relation to prior Kappa reductions, signaling analogies,
RNA/ATAC interpretation, and modeling practice are explanatory scientific prose,
not mathematical propositions.  They are summarized in `ELI15.md` and the
README rather than converted into meaningless Lean declarations.
