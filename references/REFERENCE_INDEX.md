# Reference Index

This directory is the citation gate for the Archon reproduction.

Status labels:

- `full text local`: original paper/chapter full text is present locally.
- `auxiliary extract`: a focused extract from a previous assisted run is present, but not the original full text.
- `metadata only`: only bibliographic/abstract/landing-page information is local.
- `blocked`: an attempted official download returned an access-control page or failed.

## Current Status

| Reference | Needed For | Local Status | Local Files |
|---|---|---|---|
| Anderson 2014, *Quasi-complete Semilocal Rings and Modules* | quasi-complete/weakly quasi-complete definitions, quotient criterion, one-dimensional analytic irreducibility criterion | full text local | `commutative_algebra_2014_full_book.pdf`, `anderson_2014_fulltext.pdf`, `anderson_2014_fulltext.txt` |
| Farley 2016, *Quasi-completeness and localizations of polynomial domains* | weak quasi-completeness iff nonzero completion primes meet the original domain | full text local | `farley_2016_fulltext.pdf`, `farley_2016_fulltext.txt`, `farley_2016_proposition_1_extract.md` |
| Jensen 2006, *Completions of UFDs with semi-local formal fibers* | N-subrings, Lemma 2.1, Theorem 2.2, Corollary 2.4 | full text local | `jensen_2006_fulltext.pdf`, `jensen_2006_fulltext.txt`, `jensen_2006_corollary_2_4_extract.md`, `jensen_2006_tandf_403.html` |
| Heitmann 1993, *Characterization of completions of unique factorization domains* | transfinite UFD completion construction and completion criterion background | full text local | `heitmann_1993_fulltext.pdf`, `heitmann_1993_fulltext.txt`, `heitmann_1993_ams_403.html`, `heitmann_1993_jstor_landing.html` |
| Loepp 1997, *Constructing Local Generic Formal Fibers* | avoidance lemmas and transfinite generic-fiber control, especially Lemmas 2--4 and 11--16 | full text local | `loepp_1997_fulltext.pdf`, `loepp_1997_fulltext.txt`, `loepp_1997_sciencedirect_403.html` |

## Bibliographic Anchors

1. Daniel D. Anderson, "Quasi-complete Semilocal Rings and Modules", in *Commutative Algebra*, Springer, 2014, pp. 25--37. DOI: `10.1007/978-1-4939-0925-4_2`.
2. Jonathan David Farley, "Quasi-completeness and localizations of polynomial domains: A conjecture from Open Problems in Commutative Ring Theory", *Bulletin of the Korean Mathematical Society* 53(6), 2016, pp. 1613--1615. DOI: `10.4134/BKMS.b140895`.
3. David Jensen, "Completions of UFDs with semi-local formal fibers", *Communications in Algebra* 34(1), 2006, pp. 347--360. DOI: `10.1080/00927870500346321`.
4. Raymond C. Heitmann, "Characterization of completions of unique factorization domains", *Transactions of the AMS* 337(1), 1993, pp. 379--387. DOI: `10.1090/S0002-9947-1993-1102888-9`.
5. Susan Loepp, "Constructing Local Generic Formal Fibers", *Journal of Algebra* 187(1), 1997, pp. 16--38. DOI: `10.1006/jabr.1997.6768`.

## Gate Decision

The reference gate is cleared as of 2026-08-25: Anderson 2014, Farley 2016,
Jensen 2006, Heitmann 1993, and Loepp 1997 are all present locally as original
full-text PDFs with `pdftotext -layout` extractions.

Anderson 2014 arrived as the full Springer volume `commutative_algebra_2014_full_book.pdf`.
The target chapter was split out as `anderson_2014_fulltext.pdf` from physical
PDF pages 33--45, corresponding to printed pages 25--37.  Visual spot checks of
the split chapter confirm that page 1 is the chapter title/abstract page and
page 13 is the final references page.

The next gate is not source availability but blueprint/proof readiness: rerun
the blueprint checks after source-comment updates, remove the starter `hello`
scaffold, and then open Lean theorem-skeleton/prover work.
