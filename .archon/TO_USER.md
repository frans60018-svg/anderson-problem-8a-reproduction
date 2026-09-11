# User-Facing Status

The canonical Anderson 8(a) reproduction now matches the strictness of the
published Lean formalization.

- canonical theorem: `Run202608192034.andersonProblem8a`;
- exact local-ring/maximal-ideal statement;
- 0 canonical `sorry` / `admit`;
- 0 canonical custom axioms;
- only `propext`, `Classical.choice`, and `Quot.sound` in the axiom closure;
- full build passed with 8255 jobs;
- CI has an exact-statement and axiom-boundary gate.

The 257-node Archon graph remains a historical decomposition track. It must not
be presented as the dependency graph of the complete 19,448-line canonical
proof.

Read `README.md`, `TRUST_BOUNDARY.md`, and `UPSTREAM_PROVENANCE.md` for
the public explanation. Publication was authorized on 2026-09-11.
Current limitations and publication checks are recorded in `docs/CURRENT_STATUS.md`.
