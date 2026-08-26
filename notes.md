# Archon Input Notes

Goal: formalize Anderson Problem 8a in Lean 4 from the Rethlas-verified informal blueprint.

Primary input:

- `source_blueprint.md`

Desired mathematical route:

1. Define quasi-complete and weakly quasi-complete Noetherian local rings.
2. Build the complete local domain `T = C[[x,y,z]]/(x^2-yz)`.
3. Prove the key properties of `T`: complete, local, Noetherian, domain, dimension two, and containing the nonprincipal height-one prime `Q=(x,y)T`.
4. Use Jensen's theorem to obtain a two-dimensional Noetherian local UFD `A` whose completion is `T` and whose generic formal fiber has only `(0)`.
5. Use Farley's criterion to prove that `A` is weakly quasi-complete.
6. Contract `Q` to a height-one prime `q=aA`; prove `T/aT` is not a domain.
7. Use the dimension-one analytic-irreducibility criterion to prove that `A/aA` is not weakly quasi-complete.
8. Use Anderson's quotient characterization to conclude that `A` is not quasi-complete.

Reproduction policy:

- Do not read or import the official `Anderson-Conjecture` Lean files during generation unless a fallback is explicitly recorded.
- Keep theorem names and module structure close to the informal blueprint.
- If a large external theorem is not realistically formalizable in this run, introduce it as a named theorem/axiom only after recording the fallback and isolating the boundary.
- Prefer a small compiling Lean scaffold first, then refine proof bodies.
