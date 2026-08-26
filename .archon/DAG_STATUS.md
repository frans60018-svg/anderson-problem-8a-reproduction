## Status: in_progress

## Iterations completed: 1

## Last local verification

- `leandag build --html`: 63 blueprint nodes, 137 dependency edges, 0 infinity nodes.
- `leandag --plain show gaps`: 0 nodes.
- `leandag --plain show isolated`: 0 nodes.
- `leandag --plain stats`: 0 Lean-aux nodes, 0 unmatched `\lean{}` references, 5 declarations with `sorry`, 29,476 Lean chars done, 1,057 finite-effort Lean chars remaining.
- `archon dag-query ancestors --node thm:main`: 41/41 mathematical dependencies.
- `archon blueprint-doctor --json`: clean.
- `lake build`: passed.

## Remaining gaps

- Farley 2016, Jensen 2006, Loepp 1997, Heitmann 1993, and Anderson 2014 are now present under `references/` as original full-text PDFs with local text extraction.  The citation-completeness gate is satisfied.
- The prescribed blueprint-reviewer could not run in this sandbox; a local doctor/graph audit is clean, but it does not substitute for the required fresh correctness verdict.
- The Lean theorem skeleton is still partial: strengthened placeholder definitions remain and 5 declarations still use `sorry`.
- The source-ordered strengthening pass has made the basic completion definitions, Jensen special case, node cardinality/dimension/height statements, Jensen extension/chain statements, contracted-prime/bad-quotient segment, bad quotient domain/noetherian/local step, and final existence theorem nontrivial Lean statements.
- The latest Jensen-interface pass discharged eight `sorry`s by replacing over-strong placeholders with source-relevant explicit hypotheses or witness data for prime avoidance, residue-field uncountability, initial N-subring construction, prime hitting, ideal solving, saturated union, completion criterion, and semilocal generic fiber.
- The completion/formal-fiber interface pass discharged three Basic-file `sorry`s by making the quoted quotient, completion-prime, and dimension-one analytic criteria explicit source hypotheses.
- The node-ring interface pass discharged four net `sorry`s by turning `completeDomainChoice` into the single concrete node-ring source package and deriving the five individual node-ring facts from it.
- The downstream data-package pass preserves the completion map, contracted prime identity, and principal generator inside `primeGenerator`, `badQuotient`, and the bad-quotient completion package.
- The extended-principal pass discharged the height-one contradiction: `extendedPrincipal_not_prime` now uses injectivity, `Ideal.height_le_spanRank_toENat`, and `Ideal.primeHeight_strict_mono` to contradict nonprincipality of `nodePrime`.
- The bad-quotient completion pass split the remaining completion gap into a source package plus checked downstream logic.  `quotient_not_domain_of_not_prime` is proved, and `badQuotient_completion_not_domain` now derives non-domainness from `badQuotient_completion_source`.
- `badQuotient_completion_source` is now checked from the expanded `badQuotient_criteria_source` package by choosing the quotient `nodeRing ⧸ Ideal.span {ι a}` as the completion target.  The remaining bad-quotient source hole is now `badQuotient_structured_source`, after separating Jensen completion data and quotient-completion data.
- `BadQuotientSourceData.to_contractedPrime` and `BadQuotientSourceData.to_primeGenerator` are checked, so the structured source package now recovers the contracted-prime and prime-generator stages of the paper.
- `badQuotient_structured_source` is now checked as a combination proof from four finer source targets: Jensen-to-source-data, Jensen completion equivalence, quotient completion bridge, and the quasi-completeness quotient criterion.
- `badQuotient_sourceData_from_jensen` is checked from `primeGenerator_source`, so the remaining bad quotient source obligations are now the UFD generator source, Jensen completion equivalence, quotient completion bridge, and quotient criterion.

## Declared coverage so far

- `blueprint/src/chapters/Run202608192034_Basic.tex` covers `Run202608192034/Basic.lean`: definitions of quasi-completeness, weak quasi-completeness, generic formal fiber, analytic irreducibility, the quotient characterization, Farley's completion criterion, and the dimension-one criterion.
- `blueprint/src/chapters/Run202608192034.tex` covers `Run202608192034.lean`: the node ring and distinguished prime, the complete-domain package, the full Jensen N-subring/extension/saturation/completion route, the contracted height-one prime and bad quotient, and `thm:main`.
