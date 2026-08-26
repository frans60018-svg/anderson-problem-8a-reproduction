# Project Progress

## Current Stage

autoformalize

## Stages

- [x] init
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Blueprint Gate

The mathematical cone is transcribed, all five source targets are local on the working machine, and the Lean theorem skeleton now covers every blueprint node.  Anderson was supplied as a full Springer volume and split locally to the target 13-page chapter.

Latest local verification:

- 42 blueprint nodes
- 90 dependency edges
- 0 gaps
- 0 isolated nodes
- 0 Lean-aux nodes
- 0 unmatched `\lean{}` references
- 10 declarations with `sorry`
- 12,663 Lean chars done
- 5,093 finite-effort characters remaining
- `leandag build --html` passes
- `archon blueprint-doctor --json` passes
- `lake build` passes

## Completed Work

Source-ordered strengthening has advanced: `QuasiComplete` and `WeaklyQuasiComplete` use descending ideal chains and powers of an explicit ideal; `genericFormalFiber` uses prime contraction along a ring map; `NSubring T` is an abstract subtype of `Subring T`; downstream packages for contracted primes and bad quotients now carry mathematical data; and the final theorem is proved from the bad-quotient package instead of using its own `sorry`.

Two logical connector gaps were closed: `jensen_local_genericFiber` is derived from the semilocal Jensen theorem at the singleton zero generic fiber, and `contractedPrime_nonzero_height_one` is derived by prime contraction from `nodePrime_prime_height` and the constructed ring's nonzero-contraction property.

The bad quotient non-weakness connector is proved from the source-level completion-not-domain statement and the dimension-one weak-completeness criterion.

The Jensen second-layer interface was advanced by discharging `cardinal_prime_avoidance`, `jensen_residueField_uncountable`, `initialNSubring`, `nSubring_prime_extension`, `nSubring_ideal_extension`, `jensenUnion_isUFD`, `jensen_completion_criterion`, and `jensen_semilocal_genericFiber` as explicit source-hypothesis or witness-checking lemmas.

## Remaining Gaps

These interface lemmas still need to be strengthened into full constructions when `NSubring` is fully encoded.  The remaining hard mathematical work is concentrated in the foundational completion criteria, the explicit node ring facts, and the bad quotient completion statement.
