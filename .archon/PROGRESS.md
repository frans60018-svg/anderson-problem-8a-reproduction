# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

## Blueprint Gate

The mathematical cone is transcribed, all five source targets are local under
`references/`, and the Lean theorem skeleton now covers every blueprint node.
Anderson was supplied as a full Springer volume and split to the target 13-page
chapter.

Latest local verification: 42 blueprint nodes, 90 dependency edges, 0 gaps,
0 isolated nodes, 0 Lean-aux nodes, 0 unmatched `\lean{}` references, 10
declarations with `sorry`, 12,663 Lean chars done, and 5,093 finite-effort
characters remaining.  `leandag build --html`, `leandag --plain stats`,
`leandag --plain show gaps`, `leandag --plain show isolated`,
`archon blueprint-doctor --json`, and `lake build` all pass.  The starter
`hello` scaffold has been removed.

Source-ordered strengthening has advanced: `QuasiComplete` and
`WeaklyQuasiComplete` now use descending ideal chains and powers of an explicit
ideal, `genericFormalFiber` uses prime contraction along a ring map,
`NSubring T` is an abstract subtype of `Subring T`, `contractedPrime`,
`primeGenerator`, and `badQuotient` now carry the downstream Anderson data, and
`badQuotient_dimension_domain` now proves the quotient Noetherian/local/domain
package using Mathlib quotient instances.  Node cardinality, node dimension,
prime height, cardinal prime avoidance, residue-field uncountability,
initial N-subring, prime/ideal extension, saturation chain, and completion
criterion now have nontrivial statements.  `andersonProblem8a` is proved from
the bad-quotient package rather than using its own `sorry`.

Two logical connector gaps have been closed: `jensen_local_genericFiber` is now
derived from the semilocal Jensen theorem at the singleton zero generic fiber,
and `contractedPrime_nonzero_height_one` is now derived by prime contraction
from `nodePrime_prime_height` and the constructed ring's nonzero-contraction
property.

The bad quotient non-weakness connector is now proved from the source-level
completion-not-domain statement and the dimension-one weak-completeness
criterion.  The Jensen second-layer interface was then advanced by discharging
`cardinal_prime_avoidance`, `jensen_residueField_uncountable`,
`initialNSubring`, `nSubring_prime_extension`, `nSubring_ideal_extension`,
`jensenUnion_isUFD`, `jensen_completion_criterion`, and
`jensen_semilocal_genericFiber` as explicit source-hypothesis or witness
checking lemmas.  These still need to be strengthened into full constructions
when `NSubring` is fully encoded.

Remaining gate: the prescribed independent `blueprint-reviewer` could not run
in this sandbox; local doctor/graph/source audits are clean, but they are not a
full substitute for that reviewer verdict.
