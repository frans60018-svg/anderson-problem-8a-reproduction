# Reproduction Run Manifest

Run id: `run-20260819-2034`

- Paper-relative Archon track closed: 2026-09-09
- Canonical zero-custom-axiom track verified: 2026-09-10

## Inputs

- Rethlas verified blueprint:
  `../../../02_rethlas_runs/results/run-20260819-194710/blueprint_verified.md`
- Source-ordered Archon blueprint: `source_blueprint.md`
- Anderson, Farley, Jensen, Loepp, and Heitmann sources under `references/`
- Canonical proof source: FrenzyMath `Anderson-Conjecture`, commit
  `b8bd37b`, Apache License 2.0

## Environment

- Lean: `leanprover/lean4:v4.29.0-rc8`
- Mathlib: `v4.29.0-rc8`
- Archon: `0.3.3`
- Harness: Codex

## Canonical Outputs

- Complete source tree: `Anderson/`
- Upstream umbrella module: `Anderson.lean`
- Canonical entry isolated from historical imports: `StrictReproduction.lean`
- Canonical theorem: `Run202608192034.andersonProblem8a`
- Final assembly: `Anderson/Main.lean:main_theorem`
- Statement check: `StatementAudit.lean`
- Canonical axiom check: `StrictAxiomAudit.lean`
- Combined canonical/legacy audit: `AxiomAudit.lean`
- CI gate: `scripts/verify-strict.sh`
- Provenance: `UPSTREAM_PROVENANCE.md`
- Trust audit: `TRUST_BOUNDARY.md`

## Canonical Verification

| Command | Result |
|---|---|
| `lake build` | passed, 8255 jobs |
| `lake env lean StatementAudit.lean` | passed |
| `lake env lean StrictAxiomAudit.lean` | only `propext`, `Classical.choice`, `Quot.sound` |
| strict source scan | 0 `sorry`, 0 `admit`, 0 custom `axiom`/`opaque` |
| `bash scripts/verify-strict.sh` | passed |
| upstream Comparator | Lean default kernel accepted; solution okay |

The canonical theorem has no project-defined mathematical assumptions.

## Historical Archon Outputs

- `Run202608192034.TODO.andersonProblem8a`
- `Run202608192034/Basic.lean`
- `blueprint/src/chapters/`
- `.leandag/dag.json` and `.leandag/graph.html`

The historical graph has 257 blueprint declarations and 487 edges. It records
the independent decomposition process, but its old main theorem depends on four
explicit source boundaries. It is not the canonical acceptance target.

## Publication Policy

Downloaded PDFs and full-text extractions remain excluded from GitHub. The
canonical Lean source is publishable under its bundled Apache 2.0 license.
Publication was explicitly authorized on 2026-09-11. This publication includes
previously completed source changes; the document-organization pass does not
change proof code. See `docs/CURRENT_STATUS.md` for remaining verification work.
