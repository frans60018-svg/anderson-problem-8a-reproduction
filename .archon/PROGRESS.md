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

Latest local verification: 63 blueprint nodes, 137 dependency edges, 0 gaps,
0 isolated nodes, 0 Lean-aux nodes, 0 unmatched `\lean{}` references, 5
declarations with `sorry`, 29,476 Lean chars done, and 1,057 finite-effort
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

The completion/formal-fiber interface has also advanced: the quotient
characterization, Farley completion-prime criterion, and Anderson dimension-one
analytic criterion now use explicit source-criterion hypotheses instead of bare
`sorry`s.  Their full source proofs remain future fidelity work.

The node-ring interface has been compressed: `completeDomainChoice` now carries
the concrete node ring source package, and `nodeRing_isDomain`,
`node_complete_cm_dim`, `node_cardinality`, `nodePrime_prime_height`, and
`nodePrime_not_principal` are projections from that package.  The detailed
embedding, kernel, dimension, cardinality, height, and Nakayama arguments still
remain to be unfolded for full fidelity.

The downstream data packages have now been strengthened: `primeGenerator`,
`badQuotient`, and the bad-quotient completion package retain the completion
map `ι`, the equality `q = Ideal.comap ι nodePrime`, and the principal witness
`q = Ideal.span {a}`.
`extendedPrincipal_not_prime` is now fully checked by Lean: it proves
`Ideal.map ι q = Ideal.span {ι a}`, `Ideal.span {ι a} ≤ nodePrime`,
nonzeroness of the extended ideal from injectivity, the principal-height bound
via `Ideal.height_le_spanRank_toENat`, and the height-one equality contradiction
via `Ideal.primeHeight_strict_mono`.
The bad-quotient completion step has now been split further.  The specific
nonprimality theorem `extendedPrincipal_not_prime_of_generator_data` exposes
the exact ideal `Ideal.span {ι a}` needed downstream, and
`quotient_not_domain_of_not_prime` proves the Mathlib bridge from a nonprime
ideal to a non-domain quotient.  The public theorem
`badQuotient_completion_not_domain` is no longer a bare source hole: it derives
non-domainness from the remaining source package
`badQuotient_completion_source` was then proved by taking the completion target
to be `nodeRing / Ideal.span {ι a}` with the identity equivalence.  The
remaining bad-quotient hole has been split once more: `BadQuotientSourceData`
stores the Jensen/UFD output, `JensenCompletionWitness` records the completion
equivalence `Ahat ≃ nodeRing`, `QuotientCompletionWitness` records the
completion-of-quotient bridge, and
`QuotientCompletionWitness.dimensionCriterion` transports the dimension-one
criterion across the quotient equivalence.  The actual remaining bad-quotient
`sorry` is now `badQuotient_structured_source`, whose content is the source
construction of the bad quotient together with the strengthened Jensen
completion output and final Anderson/Farley criteria for this chosen target.
`BadQuotientSourceData` has also been strengthened to store the original
counterexample-ring witness and the nonzero-prime contraction property.  The
checked projections `BadQuotientSourceData.to_contractedPrime` and
`BadQuotientSourceData.to_primeGenerator` recover the contracted-prime and
prime-generator nodes from this package.
The latest pass intentionally split `badQuotient_structured_source` into four
source-ordered targets: `badQuotient_sourceData_from_jensen`,
`jensenCompletionWitness_source`, `quotientCompletionWitness_source`, and
`badQuotient_quasiCriterion_source`.  Consequently the current `sorry` count is
5, but the public structured source theorem is now a checked combination proof.
`badQuotient_sourceData_from_jensen` is now checked from the new upstream
`primeGenerator_source`, so the remaining source obligation is aligned with the
paper's UFD height-one-prime generator step.

Remaining gate: the prescribed independent `blueprint-reviewer` could not run
in this sandbox; local doctor/graph/source audits are clean, but they are not a
full substitute for that reviewer verdict.
