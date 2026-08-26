# Source Files Resolution

The previously missing source files have been resolved as of 2026-08-25.

All original PDFs should remain in this directory:

`/Users/sy/Desktop/Anderson论文复现/03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/references`

## Resolved Files

| Local File | Reference | Use |
|---|---|---|
| `commutative_algebra_2014_full_book.pdf` | Daniel D. Anderson chapter in *Commutative Algebra*, Springer, 2014, DOI `10.1007/978-1-4939-0925-4_2` | Full volume supplied by user; retained as provenance for the chapter extraction. |
| `anderson_2014_fulltext.pdf` and `anderson_2014_fulltext.txt` | Daniel D. Anderson, "Quasi-complete Semilocal Rings and Modules" | Chapter split from physical PDF pages 33--45, printed pages 25--37. |
| `loepp_1997_fulltext.pdf` and `loepp_1997_fulltext.txt` | Susan Loepp, "Constructing Local Generic Formal Fibers", *Journal of Algebra* 187(1), 1997, DOI `10.1006/jabr.1997.6768` | Original source for avoidance lemmas and transfinite generic-fiber control. |
| `heitmann_1993_fulltext.pdf` and `heitmann_1993_fulltext.txt` | Raymond C. Heitmann, "Characterization of completions of unique factorization domains", *Transactions of the AMS* 337(1), 1993, DOI `10.1090/S0002-9947-1993-1102888-9` | Original source for the UFD completion criterion and transfinite construction background. |

## Already Local

| File | Reference |
|---|---|
| `farley_2016_fulltext.pdf` and `farley_2016_fulltext.txt` | Jonathan David Farley, "Quasi-completeness and localizations of polynomial domains", 2016. |
| `jensen_2006_fulltext.pdf` and `jensen_2006_fulltext.txt` | David Jensen, "Completions of UFDs with semi-local formal fibers", 2006. |

## Next Checks

```bash
/Users/sy/Desktop/Anderson论文复现/03_full_pipeline_reproduction/tools/Archon/.venv/bin/leandag build --html
/Users/sy/Desktop/Anderson论文复现/03_full_pipeline_reproduction/tools/Archon/.venv/bin/archon blueprint-doctor --json
lake build
```

After these pass, remove the starter `hello` scaffold and open Lean theorem-skeleton/prover work.
