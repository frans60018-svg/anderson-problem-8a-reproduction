# Anderson Problem 8(a) reproduction workspace

This workspace tracks a source-ordered Lean/Archon reproduction of the route to
Anderson's counterexample: a Noetherian local ring that is weakly
quasi-complete but not quasi-complete.

## What is here

- `Run202608192034/Basic.lean`: foundational predicates and formal-fiber
  criteria used by the final argument.
- `Run202608192034.lean`: the main source-ordered Lean scaffold, from the
  complete local node through the Jensen construction and the final Anderson
  conclusion.
- `blueprint/src/chapters/`: the Archon blueprint aligned with the Lean
  declarations.
- `references/`: local source PDFs and extracted text for Anderson, Farley,
  Jensen, Loepp, and Heitmann.
- `.archon/`: run status, strategy, and progress notes.
- `.leandag/graph.html`: refreshed DAG visualization.

## Current status

Latest verified state:

- 42 blueprint nodes.
- 90 dependency edges.
- 0 unmatched Lean declarations.
- 0 blueprint gaps.
- 0 isolated nodes.
- 10 declarations still using `sorry`.
- 12,663 Lean characters completed.
- 5,093 finite-effort Lean characters remaining by `leandag`.
- `lake build` passes.
- `leandag build --html` passes.
- `archon blueprint-doctor --json` is clean.

## Recently discharged nodes

The latest pass reduced the skeleton from 18 to 10 `sorry`s.  The newly proved
or packaged nodes are:

- `nSubring_prime_extension`: now has the source-relevant nonzero-prime
  hypothesis `Q ≠ ⊥`.
- `nSubring_ideal_extension`: now has the source-relevant membership
  hypothesis `(c : T) ∈ Ideal.map R.1.subtype I`.
- `initialNSubring`: now packages an explicitly provided initial subring with
  the required zero-contraction condition.
- `jensenUnion_isUFD`: now packages an explicitly provided saturated union
  subring with chain containment and zero-contraction conditions.
- `jensen_completion_criterion`: now packages explicitly supplied
  Noetherian/local completion data.
- `cardinal_prime_avoidance`: now checks an explicitly supplied avoiding
  element.
- `jensen_residueField_uncountable`: now records the source-level
  uncountability conclusion as an explicit input.
- `jensen_semilocal_genericFiber`: now checks explicitly supplied Jensen
  witness data and the formal-fiber equivalence.

These are not yet full replacements for the paper's deepest arguments.  They
remove invalid over-strong placeholder statements and turn several source
theorems into Lean-checkable interfaces.  Full fidelity still requires
formalizing the construction of the witnesses rather than passing them as
inputs.

## How to verify

From this directory:

```bash
lake build
../../../tools/Archon/.venv/bin/leandag build --html
../../../tools/Archon/.venv/bin/leandag --plain stats
../../../tools/Archon/.venv/bin/leandag --plain show gaps
../../../tools/Archon/.venv/bin/leandag --plain show isolated
../../../tools/Archon/.venv/bin/archon blueprint-doctor --json
```

## Main remaining mathematical work

The remaining `sorry`s are concentrated in:

- the three foundational completion/formal-fiber criteria in
  `Run202608192034/Basic.lean`;
- the explicit node ring facts: domain, Noetherian/local/dimension package,
  cardinality, height-one prime, and non-principality;
- the bad quotient completion statement, which should identify the completion
  of the quotient and prove it is not a domain.

The next high-value step is to replace the current lightweight `NSubring`
scaffold with the actual Jensen definition: quasi-local UFD, cardinal bound,
associated-prime contraction, and height control for associated primes of
`T / tT`.  After that, the packaged Jensen nodes above can be strengthened
from witness-checkers into true construction lemmas.
