# DAG Status

## Canonical Status: strict_complete

The canonical proof is the vendored `Anderson/` module tree culminating in
`main_theorem` and `Run202608192034.andersonProblem8a`. Its acceptance is
based on Lean imports, exact-statement elaboration, full build, and axiom
closure, not on the historical LeandAG graph.

| Canonical metric | Value |
|---|---:|
| Proof modules | 42 |
| Approximate Lean lines | 19,448 |
| Proof holes | 0 |
| Source custom axioms | 0 |
| Theorem custom axiom dependencies | 0 |
| Build jobs | 8255 passed |

## Historical Archon DAG

Date of last historical graph verification: 2026-09-09.

| Metric | Value |
|---|---:|
| Blueprint nodes | 257 |
| Lean declarations | 257 |
| Dependency edges | 487 |
| Lean-aux nodes | 0 |
| Unmatched Lean pins | 0 |
| Declarations with `sorry` | 0 |
| Graph-tool gaps (axioms counted as declarations) | 0 |
| Isolated nodes | 0 |
| Graph-tool finite effort remaining (not mathematical work) | 0 |
| Old main dependency closure | 213/213 |

The historical graph covers `Run202608192034.TODO` and its custom blueprint.
It does not claim declaration-level coverage of `Anderson/`. The old graph's
five explicit axiom declarations remain correct historical data; four are in
the old theorem closure and none are in the canonical theorem closure.

## Canonical Audit

```bash
bash scripts/verify-strict.sh
```

This is authoritative for current completion status.
