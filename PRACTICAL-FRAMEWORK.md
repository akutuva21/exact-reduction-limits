# Practical reduction framework

The original paper proves limits on exact state reduction.  Those limits become
useful only when they are turned into a model-specific workflow.  The Lean
extension in this repository does that without pretending to solve the
undecidable general problem.

## 1. Fix the prediction task first

A reduced state is not simply "good" or "bad" in isolation.  It is sufficient
relative to:

1. a set of microscopic restart states that matter;
2. the current assay to be preserved; and
3. the exact future-law object to be predicted.

`PredictionTask` stores exactly those three ingredients.  A representation
`phi : State -> Rep` is `PredictivelySufficient` when any two relevant states
with the same `phi` value have the same future law.

This is the precise version of the scientific question

```text
Did my definition of state throw away information that changes the future I
care about?
```

## 2. Fail with a witness, not a Boolean

`FutureCounterexample` stores two relevant microscopic states that

```text
phi(x) = phi(y)
```

but

```text
future(x) != future(y).
```

For rule semantics, `MacroCounterexample` is even more local and constructive:
the two states are merged by the proposed macrostate, but their aggregate hazard
into one target macrostate differs.

The repository proves that one such witness is enough to refute exactness, and
that exact macro closure is equivalent to there being no macro-rate witness.

This is the intended diagnostic object for a future BioNetGen tool.  Instead of
returning only

```text
NOT LUMPABLE
```

it should return the actual pair of states and the transition-rate discrepancy.

## 3. Ask what separates the witness

`CoordinateRepair.lean` formalizes a deliberately modest notion of explanation.
A candidate feature explains a counterexample only if it distinguishes the two
states that the current representation merged.

For example, candidate features could be

- connected-complex size;
- distance to a unique boundary;
- number of unmodified sites;
- graph diameter;
- occupancy of a compartment;
- number of processive steps remaining;
- a history variable introduced explicitly by the modeler.

If a feature separates the pair, augmenting the state with that feature removes
that particular collision.  Lean intentionally does **not** conclude that the
whole model is now exact: another counterexample may still exist.

This gives the counterexample-guided loop

```text
propose representation
        |
search for witness
        |
   +----+----+
   |         |
none       found
   |         |
certify   inspect difference
(if search   |
 complete) add candidate coordinate
             |
           repeat
```

## 4. Exactness is only the zero-error endpoint

`ApproximateReduction.lean` adds a declared tolerance `epsilon`.

For future laws in a metric space, an approximate representation requires

```text
dist(future(x), future(y)) <= epsilon
```

whenever the representation merges `x` and `y`.

For rule semantics, approximate macro closure requires every aggregate-hazard
discrepancy inside a macro fiber to satisfy

```text
|Lambda(x,z) - Lambda(y,z)| <= epsilon.
```

Lean proves:

- exact sufficiency implies every nonnegative tolerance;
- larger tolerances are monotone;
- a single over-budget witness refutes an approximate certificate;
- at `epsilon = 0`, the rate-level definition recovers exact macro closure; and
- a `SharpMacroErrorCertificate` or `SharpFutureErrorCertificate` proves that an
  attained `epsilon` is the **smallest** valid uniform error bound on the domain.

The repository does **not** yet claim a theorem converting a local rate error
`epsilon` into a path-law, hitting-time, or posterior-predictive error bound.
That requires additional stability assumptions and should be formalized
separately rather than guessed.

## 5. The correct software answer is YES / NO / UNKNOWN

The paper's undecidability theorem means an arbitrary-model tool cannot always
terminate with the right yes/no answer.

`Certification.lean` therefore exposes proof-carrying verdicts:

```text
certified      -- comes with a proof of exactness
counterexample -- comes with a concrete proof of failure
unknown        -- neither claim was established
```

A bounded state-space search can safely refute global exactness as soon as it
finds a witness; `macroCounterexampleOn_refutes_global` formalizes that no
completeness assumption is needed for a negative result.  A bounded search can
safely certify a requested restart set only when an independent
`DomainCertificate` proves that the searched domain contains every relevant
state.

That is the operational consequence of the undecidability result: incompleteness
must be explicit rather than hidden behind timeouts or heuristic success.

## 6. The scanner now demonstrates the full workflow

`ScannerDiagnostics.lean` turns the original negative example into a positive
state-discovery example.

For every finite family of bounded local scanner observables, Lean constructs the
same canonical deep-interior pair used by the paper.  The local representation
merges them, but their future Done-time survival curves differ.

The missing coordinate is

```text
remaining distance
```

and the extension proves something stronger than witness repair:

```text
remaining distance -> entire survival curve
```

is an exact functional dependency.  Therefore

```text
(local observables, remaining distance)
```

is sufficient for the scanner survival law even though the local observables
alone are not.

This is the pattern the practical project should try to reproduce on real
rule-based models.

The positive bounded-complex theorem is also connected to this task language.
Once graph enumeration has proved that the connected species type is finite,
the species-multiplicity vector is injective.  `sufficient_of_injective` then
proves that this coordinate is sufficient for **any** current/future prediction
task on those mixtures.  That is a genuine positive certificate, not just a
failed search for counterexamples.

## 7. What this enables in a future BioNetGen implementation

The Lean code is a specification layer, not yet a BNGL executable analyzer.  A
runtime implementation could use the theorem interfaces as contracts for:

1. **state-sufficiency testing** on an explicitly defined restart set;
2. **counterexample generation** using exact aggregate hazards;
3. **feature diagnosis** by evaluating candidate structural coordinates on the
   witness pair;
4. **counterexample-guided refinement** of the proposed reduced state;
5. **approximate reduction diagnostics** with a declared numerical tolerance;
6. **complete-domain certification** when bounded reachability has been proved;
7. a truthful **certified / refuted / unknown** API.

## 8. Important things not claimed yet

This extension does not yet formalize or implement:

- automatic discovery of the "best" biological feature;
- a BNGL/Kappa parser or NFsim state enumerator;
- symbolic reachability for arbitrary graph-rewrite systems;
- a proof that a finite simulation sample exhausts a restart set;
- propagation of one-step rate error into long-time path-law error;
- statistical uncertainty from finite experimental data;
- identifiability of the newly proposed coordinate from an assay;
- a ranking or optimization objective for competing repairs.

Those are separate problems.  The current contribution is the formal contract
that tells such algorithms what counts as a valid certificate, a valid
counterexample, and a valid local repair claim.
