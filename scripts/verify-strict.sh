#!/usr/bin/env bash
set -euo pipefail

lake build
lake env lean StatementAudit.lean

audit_output="$(lake env lean StrictAxiomAudit.lean 2>&1)"
printf '%s\n' "$audit_output"

expected="'Run202608192034.andersonProblem8a' depends on axioms: [propext, Classical.choice, Quot.sound]"
if [[ "$audit_output" != "$expected" ]]; then
  printf 'Unexpected canonical axiom closure.\n' >&2
  exit 1
fi

if grep -R -n -E \
    '^[[:space:]]*(axiom|opaque)[[:space:]]|^[[:space:]]*sorry[[:space:]]*$|by[[:space:]]+sorry|(^|[[:space:]])admit([[:space:]]|$)' \
    --include='*.lean' Anderson Anderson.lean StrictReproduction.lean \
    StatementAudit.lean StrictAxiomAudit.lean; then
  printf 'Found a proof hole or custom axiom in the canonical source tree.\n' >&2
  exit 1
fi

printf 'Strict reproduction checks passed.\n'
