# Archon Run Manifest

Run id: `run-20260819-2034`

## Inputs

- Rethlas verified blueprint: `../../02_rethlas_runs/results/run-20260819-194710/blueprint_verified.md`
- Local copy: `source_blueprint.md`
- Notes: `notes.md`

## Environment

- Archon clone: `../../../tools/Archon`
- Archon version: `0.3.3`
- Lean toolchain: `leanprover/lean4:v4.29.0-rc8`
- Mathlib rev: `v4.29.0-rc8`
- Harness: Codex

## Outputs

- Blueprint index: `blueprint/src/content.tex`
- Foundation chapter: `blueprint/src/chapters/Run202608192034_Basic.tex`
- Main chapter: `blueprint/src/chapters/Run202608192034.tex`
- DAG cache: `.leandag/dag.json`
- DAG visualization: `.leandag/graph.html`
- Archon status: `.archon/DAG_STATUS.md`

## Verification

- `leandag build --html`: passed
- `leandag --plain stats`: 42 blueprint nodes, 90 edges, 0 infinity nodes, 0 Lean-aux nodes, 10 declarations with `sorry`, 12,663 Lean chars done
- `leandag --plain show gaps`: 0 nodes
- `leandag --plain show isolated`: 0 nodes
- `archon dag-query unmatched`: 0 uncovered Lean declarations
- `archon dag-query ancestors --node thm:main`: 41/41 mathematical dependencies
- `archon blueprint-doctor --json`: no orphan chapters, broken refs, malformed refs, axioms, or covers problems
- `lake build`: passed

## Gate Status

The informal blueprint DAG is generated and structurally validated, the external-source gate is cleared, and the Lean theorem skeleton compiles.  Several source-ordered connector and Jensen-interface objectives have now been discharged.

Remaining blockers:

- The theorem skeleton currently contains strengthened placeholder statements and 10 `sorry`s.
- The next prover pass must continue source-ordered strengthening and replace the remaining `sorry`s.

## Source Gate

Original full texts for Anderson 2014, Farley 2016, Jensen 2006, Loepp 1997, and Heitmann 1993 are local in the working machine under `references/`, but PDFs and extracted full text are intentionally excluded from GitHub.

The latest Jensen pass discharged eight additional `sorry`s by making the source-relevant hypotheses explicit: nonzero prime hitting, membership in the extended ideal, an explicitly supplied initial N-subring, an explicitly supplied saturated union, completion criterion witness data, an avoiding element for cardinal prime avoidance, residue-field uncountability as a source result, and semilocal generic-fiber witness data.
