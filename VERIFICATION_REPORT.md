# Strict Verification Report

Verification date: 2026-09-10

Documentation and local strict-check replay: 2026-09-11.
`bash scripts/verify-strict.sh` again passed with 8255 build jobs and the
expected three logical axioms. No proof code was changed during this cleanup.
The Comparator result below is the earlier run in the separate upstream
checkout, not a self-contained Comparator run in this repository.
Remote CI must be checked for the published commit in GitHub Actions.

The last pre-publication remote run, `33354091298`, finished with failure
after 6h0m3s on 2026-08-31. It checked the older commit, not this integrated
canonical source. No remote success is inferred from that run.

## Canonical Theorem

```lean
Run202608192034.andersonProblem8a :
  ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
    (_ : IsNoetherianRing R),
    IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R
```

## Integrated Source Identity

The 42 files under `Anderson/` and the umbrella `Anderson.lean` were compared
against FrenzyMath `Anderson-Conjecture` commit `b8bd37b`:

```text
diff -qr Anderson <upstream>/Anderson
  [no output]

cmp Anderson.lean <upstream>/Anderson.lean
  exit status 0
```

The integrated canonical source is therefore byte-identical to the locally
checked upstream proof at that commit.

## Full Build

```text
Build completed successfully (8255 jobs).
```

The isolated canonical target also builds without importing the historical
Archon module:

```text
lake build StrictReproduction
Build completed successfully (2705 jobs).
```

## Statement and Axiom Audit

`StatementAudit.lean` elaborates an independent copy of the challenge
proposition using `Run202608192034.andersonProblem8a`.

```text
'Run202608192034.andersonProblem8a' depends on axioms:
[propext, Classical.choice, Quot.sound]

'StatementAudit.exactChallengeStatement' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The canonical source scan found no `sorry`, `admit`, custom `axiom`, or
custom `opaque` declarations.

## Comparator Replay

The published project's own `verify-local.sh` was run against the byte-identical
source with its official challenge and Comparator configuration. Final output:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Comparator checked:

1. `main_theorem` proves the exact challenge statement;
2. the only permitted axioms are `propext`, `Quot.sound`, and
   `Classical.choice`;
3. the Lean default kernel accepts the exported proof.

## Reproduction Command

For this repository's self-contained checks:

```bash
bash scripts/verify-strict.sh
```

Expected final line:

```text
Strict reproduction checks passed.
```
