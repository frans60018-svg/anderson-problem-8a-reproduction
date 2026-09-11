# Project Progress

## Current Stage

canonical strict formalization complete; local verification complete

## Stages

- [x] source and citation collection
- [x] Rethlas informal proof reconstruction
- [x] Archon 257-node paper-relative decomposition
- [x] elimination of every actual Archon-track `sorry`
- [x] explicit audit of the old external boundaries
- [x] exact-statement repair using the maximal ideal
- [x] integration of the complete zero-custom-axiom proof modules
- [x] canonical theorem dependency audit
- [x] local build and CI regression gate configuration
- [ ] remote execution of the newly configured strict CI gate confirmed
- [x] documentation and provenance update

## Canonical Snapshot

- Canonical theorem: `Run202608192034.andersonProblem8a`
- Complete proof modules: 42
- Complete proof source size: approximately 19,448 Lean lines
- Canonical source proof holes: 0
- Canonical source custom axioms: 0
- Canonical theorem custom axiom dependencies: 0
- Logical dependencies: `propext`, `Classical.choice`, `Quot.sound`
- `lake build`: passed, 8255 jobs
- Exact statement audit: passed
- Strict regression script: passed

## Mathematical Coverage

The canonical `Anderson/` track internally proves the node-ring package,
adic completion local/Noetherian structure, Anderson's quasi-completeness
criteria, the Jensen/Heitmann N-subring and transfinite construction, the
generic-formal-fiber result, the bad quotient, and the final contradiction.

## Historical Snapshot

The earlier Archon track remains available with 257 aligned blueprint nodes,
487 edges, and zero `sorry`. Its five named source boundaries are retained
only for process comparison and do not enter the canonical theorem.

## Remaining Work

The integrated upstream proof passes local checks. Independent historical
formalization still has five custom axioms (four in its main theorem closure).
Canonical declaration-level DAG, sentence-level paper mapping and a
self-contained Comparator replay in this repository remain unfinished.
Publication was authorized on 2026-09-11; remote CI results must be checked
against the published commit rather than inferred from local success.
See `docs/CURRENT_STATUS.md` for the current scope.
