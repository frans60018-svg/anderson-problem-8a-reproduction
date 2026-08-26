# Retrieval Log

Date: 2026-08-19

Goal: place original external references under `references/` before opening Archon prover tasks, so the reproduction follows the same source order as the paper.

## Successful Local Additions

- Copied the previous assisted Rethlas extract for Farley Proposition 1 to `farley_2016_proposition_1_extract.md`.
- Copied the previous assisted Rethlas extract for Jensen Corollary 2.4 to `jensen_2006_corollary_2_4_extract.md`.
- Downloaded Farley 2016 full text from the author's public publication page to `farley_2016_fulltext.pdf`.
- Extracted Farley 2016 full text with local `pdftotext -layout` to `farley_2016_fulltext.txt`.
- Downloaded Jensen 2006 full text from the author's public publication page to `jensen_2006_fulltext.pdf`.
- Extracted Jensen 2006 full text with local `pdftotext -layout` to `jensen_2006_fulltext.txt`.

The Farley and Jensen PDFs count as original full-text source files.

## Official / Public Entry Points Checked

| Reference | Entry Point | Result |
|---|---|---|
| Farley 2016 | `https://doi.org/10.4134/BKMS.b140895` | DOI request returned an empty server response through `curl`; KCI landing page is visible through web search/open, but local `curl` access failed with SSL error. |
| Farley 2016 | KCI landing page `https://www.kci.go.kr/kciportal/landing/article.kci?arti_id=ART002169186` | Web view confirms title, journal, pages, abstract, and Creative Commons notice; local download did not produce PDF. |
| Farley 2016 | Author publication page `https://latticetheory.net/mathematics/index.shtml` | Browser page exposed the public PDF link `https://latticetheory.net/media/pdf/openproblemsincommutativeringtheory.pdf`; download succeeded. |
| Jensen 2006 | Taylor & Francis PDF endpoint `https://www.tandfonline.com/doi/pdf/10.1080/00927870500346321` | Returned HTTP 403 HTML, saved as `jensen_2006_tandf_403.html`. |
| Jensen 2006 | Author publication page `https://www.ms.uky.edu/~dhje223/publications.html` | Browser page exposed the public PDF link under `Published_Papers`; download succeeded. |
| Loepp 1997 | ScienceDirect PDF endpoint for PII `S0021869397967685` | Returned HTTP 403 HTML, saved as `loepp_1997_sciencedirect_403.html`. |
| Loepp 1997 | Browser check of ScienceDirect article page | Page showed a CAPTCHA/human-verification barrier; no bypass attempted. |
| Heitmann 1993 | AMS PDF endpoint for DOI `10.1090/S0002-9947-1993-1102888-9` | Returned HTTP 403 HTML, saved as `heitmann_1993_ams_403.html`. |
| Heitmann 1993 | JSTOR stable PDF `https://www.jstor.org/stable/pdf/2154327.pdf` | Returned a landing/login-style HTML page, saved as `heitmann_1993_jstor_landing.html`. |
| Anderson 2014 | Springer DOI `10.1007/978-1-4939-0925-4_2` and ResearchGate page | Public metadata/abstract found; original chapter PDF not saved locally. |
| Anderson 2014 | Browser check of Springer chapter page | Page reports subscription preview and institution-login path; no public chapter PDF link exposed. |
| Anderson 2014 | Browser check of ResearchGate page | Page rendered as a blocked/minimal iframe view in the in-app browser; no reliable PDF link exposed. |

## 2026-08-25 User-Provided Full Texts

The user manually downloaded the remaining source files to `/Users/sy/Downloads`.
They were moved into this directory and normalized as follows:

| Downloaded file | Stored as | Check |
|---|---|---|
| `anderson_2014_fulltext.pdf` | `commutative_algebra_2014_full_book.pdf` | 372-page Springer book, title metadata `Commutative Algebra` |
| `loepp_1997_fulltext.pdf` | `loepp_1997_fulltext.pdf` | 23-page article, title metadata `Constructing Local Generic Formal Fibers` |
| `heitmann_1993_fulltext.pdf` | `heitmann_1993_fulltext.pdf` | 9-page article |

The Anderson file was a full book, not a chapter-only PDF.  The target chapter
was extracted from physical PDF pages 33--45 into `anderson_2014_fulltext.pdf`;
this corresponds to printed chapter pages 25--37.  Page 33 begins with
`Quasi-complete Semilocal Rings and Modules`; page 46 begins the next chapter,
so the extracted range is complete.

Local text extractions were produced with `pdftotext -layout`:

- `anderson_2014_fulltext.txt`
- `loepp_1997_fulltext.txt`
- `heitmann_1993_fulltext.txt`

Spot checks:

- Anderson: title at line 1, Definition 1 at lines 68--76, Theorem 4 at
  lines 170--262, Corollary 2 at lines 307--339, Theorem 9 at lines 672--692,
  references begin at line 708.
- Loepp: title at line 7, Proposition 1 at lines 141--144, Lemmas 2--4 at
  lines 153--167, Lemmas 13--15 at lines 802--977, Theorem 16 at lines
  978--1033.
- Heitmann: Lemmas 2--4 at lines 98--148, Lemmas 5--7 at lines 250--331,
  Theorem 8 at lines 332--353, references begin at line 401.

## Consequence

The citation-completeness bottleneck recorded on 2026-08-19 is resolved.  The
old 403/landing HTML files remain in the directory only as retrieval history and
must not be used as mathematical source text.  The next work is to align
blueprint `SOURCE` comments to these local text files, rerun Archon/Lean checks,
remove the starter `hello` scaffold, and create the mathematical Lean theorem
skeleton before prover work.
