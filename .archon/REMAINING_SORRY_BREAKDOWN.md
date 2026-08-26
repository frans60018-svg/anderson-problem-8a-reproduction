# Remaining Sorry Breakdown

This note breaks the current Lean `sorry`s into smaller source-ordered
lemmas.  The purpose is to make clear which parts are routine Mathlib plumbing,
which parts require new local interface lemmas, and which parts are genuine
deep formalization work.

Current actual proof holes:

```text
Run202608192034.lean:53   completeDomainChoice
Run202608192034.lean:297  primeGenerator_source
Run202608192034.lean:559  jensenCompletionWitness_source
Run202608192034.lean:565  quotientCompletionWitness_source
Run202608192034.lean:571  badQuotient_quasiCriterion_source
```

Status labels:

- `direct`: likely provable now from existing project hypotheses and Mathlib.
- `interface`: should first be stated as a source theorem / bridge lemma, then
  unfolded later.
- `deep`: requires substantial new formalization, not just tactic search.

## 1. `completeDomainChoice`

Lean target:

```lean
IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
  ringKrullDim nodeRing = 2 ∧ Cardinal.mk nodeRing = Cardinal.mk ℂ ∧
    nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 ∧
      ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing)
```

Source route:

- `source_blueprint.md`, lines 47--55: defines
  `T = C[[x,y,z]]/(x^2-yz)`, `M = (x,y,z)T`, and states that `T` is a
  complete two-dimensional Cohen--Macaulay local domain, has cardinality
  `|C|`, and `Q = (x,y)T` is a nonprincipal height-one prime.
- `source_blueprint.md`, lines 58--78: constructs
  `Phi : C[[x,y,z]] -> C[[u,v]]`, sends `x -> uv`, `y -> u^2`, `z -> v^2`,
  and identifies the kernel with `(x^2-yz)`.
- `source_blueprint.md`, lines 82--86: uses the hypersurface argument for
  completeness, Cohen--Macaulayness, and dimension two.
- `source_blueprint.md`, lines 88--101: proves the cardinality assertion.
- `source_blueprint.md`, lines 103--118: proves `Q` is prime, height one, and
  nonprincipal by the quotient `T/Q ~= C[[z]]` and Nakayama.

Suggested lemma split:

| Proposed Lean lemma | Source sentence | Mathlib needed | Current status |
|---|---|---|---|
| `nodeRelation_mem_uvKernel` | "The relation `x^2-yz` maps to zero." | `MvPowerSeries.substAlgHom`, `map_pow`, `map_mul`, simplification of `X` images | `interface`: substitution API exists, but the exact two-variable target map must be set up. |
| `node_uvKernel_le_span_relation` | "`ker Phi = (x^2-yz)`" | kernel/order API for ideals, `Ideal.span_le`, `RingHom.mem_ker` | `deep`: requires formal division / normal form, not just ideal algebra. |
| `node_normal_form_remainder` | "Formal division by the monic polynomial ... gives a unique expression." | Weierstrass/division-style result for power series, or custom coefficient proof | `deep`: Mathlib likely does not have this exact multivariate power-series division lemma ready. |
| `even_odd_uv_remainder_zero` | "even-even and odd-odd monomials cannot cancel." | coefficient extensionality for `MvPowerSeries`, parity on `Fin 2 ->₀ ℕ`, support/coefficient lemmas | `deep`: elementary mathematically, but lengthy in Lean. |
| `nodeRing_embeds_in_uvPowerSeries` | "`T ~= C[[u^2,uv,v^2]] subset C[[u,v]]`" | quotient lift by kernel, injective quotient map from exact kernel equality | `interface`: straightforward after the kernel theorem. |
| `nodeRing_isDomain_from_embedding` | "Thus `T` is a domain." | `IsDomain` transfer along injective ring hom into a domain, or ring equivalence to subring | `direct` after embedding; not direct before kernel equality. |
| `mvPowerSeries_three_isNoetherian` | "`S` is a complete regular local ring of dimension three." | Noetherian/local instances for finite-variable `MvPowerSeries` over `C`; possibly power-series regular local theory | `interface/deep`: local instance exists for `MvPowerSeries`, but Noetherian/dimension-three regularity may need missing API. |
| `nodeRing_isLocal` | "A quotient of a complete Noetherian local ring is ... local." | quotient local ring API, `IsLocalRing.of_surjective`, quotient nontriviality | `direct` once the defining ideal is proper. |
| `nodeRing_isNoetherian` | "A quotient of a complete Noetherian local ring is Noetherian." | `Ideal.Quotient.Noetherian`, Noetherian source ring | `direct` after source `MvPowerSeries` Noetherian instance. |
| `nodeRing_dimension_two` | "quotienting ... by a nonzerodivisor lowers dimension by one." | `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`, regular/non-zero-divisor facts | `interface/deep`: Mathlib has quotient dimension lemmas, but proving all hypotheses for this hypersurface is nontrivial. |
| `nodeRing_cardinality_source` | "There are countably many monomials ... CSB gives `|T|=|C|`." | cardinal arithmetic, quotient cardinal bound, constants injection into quotient | `interface`: possible, but several cardinal facts around `MvPowerSeries` must be assembled manually. |
| `nodePrime_quotient_equiv_powerSeries_z` | "Setting `x=y=0` identifies `T/Q` with `C[[z]]`." | quotient-by-span equivalence, substitution/evaluation maps | `deep`: needs explicit quotient equivalence for multivariate power series. |
| `nodePrime_isPrime` | "`T/Q ~= C[[z]]`, so `Q` is prime." | prime kernel / quotient-domain criterion | `direct` after quotient equivalence. |
| `nodePrime_nonzero` | "`Q` is nonzero because `x != 0` in the domain `T`." | quotient equality/membership criterion, domain/embedding result | `interface`: depends on the uv embedding or explicit coefficient argument. |
| `nodePrime_height_one` | "`(0) < Q < M`, and `dim T = 2`, so height is one." | `Ideal.height`, strict prime chains, finite Krull dimension facts | `interface`: follows after prime/nonzero/nonmaximal/dimension facts, but Lean height arithmetic will take work. |
| `nodePrime_not_principal_nakayama` | "classes of `x` and `y` in `Q/MQ` are linearly independent ... Nakayama." | `RingTheory.Nakayama`, cotangent space, quotient modules, linear independence over residue field | `deep`: this is a real formalization task; likely the hardest subpart of this package after kernel equality. |

Recommended approach:

1. First create named source-interface lemmas for the kernel equality,
   dimension-two hypersurface fact, quotient `T/Q ~= C[[z]]`, and Nakayama
   nonprincipal argument.
2. Then prove the projection lemmas from those interfaces.
3. Only after that unfold the interfaces into coefficient-level Lean proofs.

## Completed. `extendedPrincipal_not_prime`

Lean target:

```lean
primeGenerator →
  ∃ (a : nodeRing), ¬ (Ideal.span ({a} : Set nodeRing)).IsPrime
```

Source route:

- `source_blueprint.md`, lines 216--229: defines `q = Q ∩ A`, uses faithful
  flatness and going-down to show `ht q = 1`, then uses that a height-one
  prime in a UFD is principal, `q = aA`.
- `source_blueprint.md`, lines 235--242: claims `aT` is not prime; if it were
  prime, principal ideal theorem gives height at most one, nonzeroness gives
  height at least one, so the nested height-one primes `aT ⊆ Q` would be equal,
  contradicting nonprincipality of `Q`.

Suggested lemma split:

| Proposed Lean lemma | Source sentence | Mathlib needed | Current status |
|---|---|---|---|
| `primeGenerator_unpack` | "`q = aA` for some prime element `a`." | destructuring current `primeGenerator` package | `done`: current definition stores `q = span {a}`. |
| `principal_generator_maps_into_nodePrime` | "`a in q subset Q` gives `aT subset Q`." | `Ideal.map`, `Ideal.comap`, `Ideal.map_comap_le` | `done`: Lean proves `Ideal.span {ι a} ≤ nodePrime`. |
| `mapped_principal_is_principal` | "the extended ideal `aT` is principal." | `Ideal.map_span`, `Ideal.span_singleton` | `done`: Lean proves `Ideal.map ι q = Ideal.span {ι a}`. |
| `extended_principal_nonzero` | "the injection `A -> T` shows `a != 0` in `T`." | `RingHom.injective_iff_ker_eq_bot`, `Ideal.map_eq_bot_iff_of_injective` | `done`: nonzeroness follows from `comap ι ⊥ = ⊥` and `q ≠ ⊥`. |
| `principal_prime_height_le_one` | "principal ideal theorem gives `ht(aT) <= 1`." | `Ideal.height_le_spanRank_toENat`, `Submodule.spanRank_span_le_card` | `done`: Lean derives height at most one for `span {ι a}`. |
| `nonzero_prime_height_ge_one_in_domain` | "nonzeroness in the domain `T` gives the reverse inequality." | `Ideal.height_strict_mono_of_is_prime`, `Ideal.height_bot` | `done`: Lean proves `(0) < span {ι a}` implies positive height. |
| `nested_height_one_primes_eq` | "nested height-one primes ... would then be equality." | `Ideal.primeHeight_strict_mono` | `done`: strict containment would force strict prime-height inequality, contradicting both heights being one. |
| `nodePrime_principal_contradiction` | "contradicting the fact that `Q` is not principal." | existential witness for a principal ideal | `done`: equality makes `nodePrime = span {ι a}` and contradicts `nodePrime_not_principal`. |
| `extendedPrincipal_not_prime_strong` | full theorem | previous lemmas | `done`: `extendedPrincipal_not_prime` has no `sorry`. |

This proof is now a completed downstream connector.  It still depends on
`completeDomainChoice` for the source facts that `nodeRing` is a Noetherian
domain and that `nodePrime` is a nonprincipal height-one prime, but it no
longer contributes an independent `sorry`.

## 2. Bad quotient source targets

Lean targets:

```lean
primeGenerator_source :
  primeGenerator

jensenCompletionWitness_source
  (d : BadQuotientSourceData) :
  JensenCompletionWitness d.A d.𝔪 d.ι

quotientCompletionWitness_source
  (d : BadQuotientSourceData)
  (_w : JensenCompletionWitness d.A d.𝔪 d.ι) :
  QuotientCompletionWitness d

badQuotient_quasiCriterion_source
  (d : BadQuotientSourceData)
  (_w : JensenCompletionWitness d.A d.𝔪 d.ι) :
  d.QuasiCriterion
```

Source route:

- `source_blueprint.md`, lines 244--251: sets `B = A/aA`, proves `B` is a
  one-dimensional Noetherian local domain.
- `source_blueprint.md`, lines 251--256: uses completion commuting with
  quotient by a finitely generated ideal to identify
  `Bhat ~= Ahat/aAhat ~= T/aT`.
- `source_blueprint.md`, lines 256--258: since this completion is not a domain,
  `B` is not analytically irreducible.

Suggested lemma split:

| Proposed Lean lemma | Source sentence | Mathlib needed | Current status |
|---|---|---|---|
| `primeGenerator_source` | "`q=Q∩A` is height one, and height-one primes in a UFD are principal." | contracted-prime package, UFD/principal height-one-prime interface, weak quasi-completeness criterion | `interface`: current upstream source theorem; needs the UFD output of Jensen and a height-one-prime principalization theorem. |
| `badQuotient_source_data_from_primeGenerator` | "Put `B = A/aA`." | construction from strengthened `primeGenerator`, quotient ring instances | `done`: proved as `badQuotient_sourceData_from_jensen` by destructuring `primeGenerator_source`. |
| `source_data_to_contractedPrime` | recover "`q=Q∩A` is nonzero prime." | destructuring the source data package | `done`: proved as `BadQuotientSourceData.to_contractedPrime`. |
| `source_data_to_primeGenerator` | recover "`q=aA` for a chosen generator." | destructuring the source data package | `done`: proved as `BadQuotientSourceData.to_primeGenerator`. |
| `quotient_by_prime_is_domain` | "`aA = q` is prime, so `B` is a domain." | existing quotient domain instance from `[q.IsPrime]` | `direct`: already used in `badQuotient_dimension_domain`. |
| `quotient_is_noetherian_local` | "quotients of Noetherian local rings are Noetherian and local." | `Ideal.Quotient.Noetherian`, `IsLocalRing.of_surjective` | `direct`: already essentially proved. |
| `badQuotient_dimension_one` | "`dim B = 1`." | quotient dimension, prime chains, `ringKrullDim` API | `interface`: current theorem avoids storing dimension; formal proof needs more height-chain work. |
| `completion_identifies_Ahat_with_nodeRing` | "`Ahat ~= T`." | Jensen construction output should carry a ring equivalence, not just a map `ι` | `interface`: now represented by `JensenCompletionWitness`; the source proof remains. |
| `completion_quotient_equiv` | "`Bhat ~= Ahat/aAhat`." | `AdicCompletion.map_exact`, `AdicCompletion.kerProj`, exactness of completion over Noetherian rings | `deep/interface`: now represented by `QuotientCompletionWitness`; the source proof remains. |
| `bad_completion_equiv_node_quotient` | "`Bhat ~= T/aT`." | composition of the two equivalences above | `interface`: represented by `QuotientCompletionWitness.quotientCompletionEquiv`. |
| `dimension_criterion_transport` | move analytic irreducibility criterion from `Bhat` to `T/aT` | ring-equivalence transfer of `IsDomain` | `done`: proved as `QuotientCompletionWitness.dimensionCriterion`. |
| `quotient_not_domain_of_ideal_not_prime` | "By `aT` not prime, this quotient is not a domain." | `RingHom.ker_isPrime`, `Ideal.mk_ker` | `done`: formalized as `quotient_not_domain_of_not_prime`. |
| `not_domain_transferred_across_equiv` | transfer `¬ IsDomain (T/aT)` to `¬ IsDomain Bhat` | `MulEquiv.isDomain` from the ring equivalence | `done`: used in `badQuotient_completion_not_domain`. |
| `source_criteria_for_final_step` | package quotient criterion and dimension-one analytic criterion | current source criterion interfaces in `Basic.lean` | `direct`: this is already threaded through downstream statements. |

Main issue:

The previous single `badQuotient_structured_source` hole has been split into
four source-ordered targets, and then the first target was moved further
upstream to `primeGenerator_source`.  Together they produce a structured source package
`s`.  The package stores the bad quotient source data, a Jensen completion witness
`Ahat ≃ nodeRing`, a quotient completion witness equivalent to
`nodeRing ⧸ Ideal.span ({s.data.ι s.data.a} : Set nodeRing)`, and the
source quotient criterion.  The dimension-one criterion transport, flattening
of this package, identity-equivalence bookkeeping, and the proof that the target
is not a domain are no longer part of the source hole; they are checked
downstream from the nonprimality of the extended principal ideal.  A faithful
proof needs stronger data from the Jensen stage:

- `A` is a UFD;
- `Ahat` is explicitly equivalent to `nodeRing`;
- the generic formal fiber condition is expressed through that equivalence;
- `q = comap ι nodePrime`;
- `q = span {a}` for a height-one prime generator `a`.

Recommended approach:

1. Upgrade the Jensen construction output from a bare map `ι : A -> nodeRing`
   to an explicit completion equivalence `Ahat ≃+* nodeRing`.
2. Prove or interface completion commuting with the quotient by `q = span {a}`.
3. Use those equivalences to justify the source fields of
   `BadQuotientStructuredSource`.

## Priority Plan

1. Refactor data packages: done.
   `primeGenerator`, `badQuotient`, and the bad-quotient completion package now
   keep `A`, `ι`, `q`, `q = comap ι nodePrime`, and `q = span {a}` together.

2. Attack `extendedPrincipal_not_prime`: done.
   Lean now checks the map/span identity, injectivity/nonzero step, principal
   height bound, and nested height-one-prime contradiction.

3. Add or prove the completion-of-quotient bridge: in progress.
   identify the completion of `A/q` with a quotient of `nodeRing` by the
   extended principal ideal `Ideal.span {ι a}`.  The downstream non-domain
   transfer and identity target selection are now checked, so the remaining
   bridge is purely the source criteria/completion equivalence.

4. Add a source-interface lemma for completion commuting with quotient.
   Full formalization should eventually use `Mathlib.RingTheory.AdicCompletion`
   exactness, but that is a larger task.

5. Leave `completeDomainChoice` for a dedicated node-ring formalization pass.
   It contains multiple serious formalization projects: power-series
   substitution kernel, hypersurface dimension, and Nakayama nonprincipality.

## Summary for Advisor Discussion

The current `sorry`s are not small gaps.  They are source-level mathematical
packages:

1. concrete algebra of the node hypersurface ring;
2. Jensen/UFD production of the prime-generator package;
3. identification of `Ahat` with the node ring;
4. completion of the bad quotient as an explicit quotient of the node ring;
5. the quotient criterion for quasi-completeness.

The bad-quotient package has now been expanded enough that the
quotient-domain/equivalence transfer lemmas are discharged, and
`BadQuotientStructuredSource` is now assembled by checked Lean code from four
source targets.  The next technically honest step is to prove one of those
targets, starting with `badQuotient_sourceData_from_jensen` if continuing the
paper order.  The node-ring package should be handled as a separate
source-level formalization pass.
