# Strategy

## Goal

Formalize `Run202608192034.andersonProblem8a`: there exists a Noetherian local ring that is weakly quasi-complete but not quasi-complete, with no axioms or unresolved proof obligations.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Definitions and quotient criterion | ACTIVE | 2 | ~250–600 | ideals, local rings, quotients, infima, powers | quotient/intersection transport remains mostly unproved |
| Completion and formal-fiber criteria | NEXT | 6 | ~900–2,000 | adic completion, spectra, contraction, minimal primes | Farley's criterion has no known Mathlib analogue |
| Explicit complete node T | NEXT | 6 | ~700–1,500 | multivariate power series, quotients, dimension, Cohen--Macaulay facts | power-series quotient infrastructure may be sparse |
| Jensen N-subring extension lemmas | ACTIVE | 8 | ~1,800–4,500 | cardinal avoidance, associated primes, localization | source interfaces now typecheck, but witness construction and full N-subring fields remain to be formalized |
| Jensen transfinite saturation | NEXT | 14 | ~3,500–9,000 | ordinal recursion, directed unions, completion criterion | current saturated-union and completion nodes are witness-checkers, not full constructions |
| Jensen specialization to P = 0 | NEXT | 4 | ~500–1,200 | Cohen--Macaulay localization, associated primes | must verify every Corollary 2.4 hypothesis |
| Contraction and bad quotient | NEXT | 6 | ~700–1,600 | faithful flatness, going-down, principal ideal theorem, completion of quotients | height and completion API alignment |
| Final weak/non-quasi conclusion | NEXT | 2 | ~150–400 | one-dimensional completion facts | all upstream criteria must expose usable interfaces |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---:|---:|---|---|---|---|
| Informal route selection | 001 · 1 | 0 | `source_blueprint.md` | Jensen--Farley counterexample route | reduce failure of quasi-completeness to a bad quotient | external results must not become Lean axioms |
| Source gate and theorem skeleton | 002 · 1 | ~130 | `references/`, `Run202608192034/Basic.lean`, `Run202608192034.lean` | all five source PDFs local; `hello` removed; 42 blueprint nodes match 42 Lean declarations | strengthen statements in source order before prover loop | initial scaffold had 18 `sorry`s and several abstract placeholders; 10 now remain |
| Downstream Anderson data-flow strengthening | 003 · 1 | ~70 | `Run202608192034.lean` | node/Jensen special-case package feeds contracted-prime and bad-quotient packages; quotient Noetherian/local/domain step is proved; final theorem no longer has its own `sorry` | package hard quotient failures so the final non-quasi-complete conclusion can be derived from the quotient criterion | existence of the bad quotient remains a deep source theorem |
| Source-order statement strengthening | 004 · 1 | ~60 | `Run202608192034.lean` | node normal form proved by definition; cardinality/dimension/height and Jensen extension/chain statements are no longer `True` placeholders | keep theorem names aligned while replacing empty statements with object-level claims | N-subring fields are still abstract and need full source-backed definitions |
| Logical connector cleanup | 005 · 1 | ~35 | `Run202608192034.lean` | `jensen_local_genericFiber` and `contractedPrime_nonzero_height_one` no longer use `sorry` | derive singleton generic-fiber and prime-contraction facts from upstream packages | remaining gaps are now mostly source-level mathematics rather than connective logic |
| Bad quotient non-weakness connector | 006 · 1 | ~25 | `Run202608192034.lean` | `badQuotient_not_weaklyQuasiComplete` no longer uses `sorry` | use dimension-one weak-completeness criterion against a non-domain completion object | the non-domain completion source theorem remains open |
| Jensen second-layer interface pass | 007 · 1 | ~90 | `Run202608192034.lean` | `cardinal_prime_avoidance`, `jensen_residueField_uncountable`, `initialNSubring`, `nSubring_prime_extension`, `nSubring_ideal_extension`, `jensenUnion_isUFD`, `jensen_completion_criterion`, and `jensen_semilocal_genericFiber` no longer use `sorry`; total `sorry`s reduced from 18 to 10 | replace false or over-strong placeholders with explicit source hypotheses/witness data before attempting full construction proofs | these are interface proofs; full fidelity still requires constructing the witnesses from the paper's cardinal avoidance and transfinite recursion arguments |

## Routes

Single route: construct (T=\mathbb C[[x,y,z]]/(x^2-yz)), apply a fully formalized Jensen-style N-subring construction to obtain a two-dimensional local UFD (A) with trivial generic formal fiber, then use the contraction of (Q=(x,y)T) to produce a non-weakly-quasi-complete quotient of (A).

## Open key strategic questions

- Which existing Mathlib model of multivariate formal power series minimizes the proof burden for (T)?
- Which precise Heitmann and Loepp lemmas should be expanded first so the current Jensen witness-checking interfaces can become construction theorems?
- Can Farley's completion criterion be proved cleanly from the ideal-chain formulation without importing Noether-lattice machinery?
- Can the Codex-backed Archon loop run reliably in this sandbox, or should prover objectives be handled manually one source block at a time?

## Mathlib gaps & new material

- **Gaps to fill:** generic formal fibers and their prime correspondence; the full Jensen N-subring definition; construction of the current Jensen witnesses; Farley's completion criterion.
- **New project material:** quasi-complete predicates; analytic irreducibility wrapper; explicit node (T) and prime (Q); the constructed local UFD (A); the final counterexample theorem.
