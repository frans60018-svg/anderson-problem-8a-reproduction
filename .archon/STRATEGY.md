# Strategy

## Objective

Provide a theorem whose statement and kernel-checked proof have the same
strictness as the published Anderson Problem 8(a) formalization.

## Acceptance Criteria

- [x] Quasi-completeness uses `IsLocalRing.maximalIdeal`, not an arbitrary ideal.
- [x] The final theorem has the same proposition as the published challenge.
- [x] No `sorry` or `admit` occurs in the canonical proof tree.
- [x] No project-defined axiom occurs in the canonical theorem closure.
- [x] Jensen's strong N-subring invariants and transfinite construction are code.
- [x] Node-ring and Anderson/Farley facts are code rather than source axioms.
- [x] The complete source builds on the pinned Lean/Mathlib revision.
- [x] CI gate configured to reject statement, hole, and axiom-boundary regressions.
- [ ] Remote execution of that gate confirmed for the publication commit.
- [x] Upstream source and license are explicit.

## Implemented Architecture

1. `Anderson/` is the canonical, fully internalized proof tree.
2. `Run202608192034.andersonProblem8a` is the public theorem alias.
3. `StatementAudit.lean` independently restates the required proposition.
4. `StrictAxiomAudit.lean` exposes the kernel dependency closure.
5. `scripts/verify-strict.sh` enforces these checks locally and in CI.
6. The old `Run202608192034.TODO` tree and Archon DAG remain as historical
   decomposition artifacts, not as the acceptance target.

## Trust Discipline

Do not infer proof completeness from a zero-`sorry` scan alone. The canonical
claim requires all three checks: exact statement, source-hole scan, and
`#print axioms`. The historical theorem is always named with its full
`TODO` namespace when discussed.
