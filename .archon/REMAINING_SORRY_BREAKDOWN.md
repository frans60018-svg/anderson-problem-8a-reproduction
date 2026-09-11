# Remaining Proof Work

## Canonical Track

There are no remaining proof holes or custom mathematical assumptions.

```text
Anderson/**/*.lean
Anderson.lean

sorry / admit          0
custom axiom / opaque  0
```

The canonical theorem depends only on:

```text
propext
Classical.choice
Quot.sound
```

The exact statement and closure are checked by:

```bash
bash scripts/verify-strict.sh
```

## Historical Archon Track

The old source files have zero `sorry`, but retain five named axiom
declarations. They document the earlier paper-relative stopping point:

| Boundary | Old theorem uses it? | Canonical theorem uses it? |
|---|---:|---:|
| `nodeRing_standard_facts_external` | yes | no |
| `jensen_corollary_2_4_construction_external` | yes | no |
| `anderson_corollary2_part1_external` | yes | no |
| `anderson_corollary2_part3_external` | yes | no |
| `adicCompletion_quotient_hausdorff_external` | no | no |

Their fully internalized replacements are in `Anderson/CompleteDomain/`,
`Anderson/Jensen/`, `Anderson/QuasiCompleteRing/`,
`Anderson/AdicNoetherian.lean`, and `Anderson/AdicLocal.lean`.

## Completion Interpretation

There is no longer a separate future zero-axiom phase for reproducing the
published result. That phase is complete in the canonical track. Further work
would be refactoring, documentation, upstream contribution, or extending the
theorem, rather than closing a logical gap in the integrated canonical theorem.
An independent implementation of the five historical axioms is still unfinished.
Canonical DAG, sentence-level paper mapping and remote verification limitations
are tracked in `docs/CURRENT_STATUS.md`.
