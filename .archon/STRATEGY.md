# Strategy

## Goal

Formalize `Run202608192034.andersonProblem8a`: there exists a Noetherian local ring that is weakly quasi-complete but not quasi-complete, with no axioms or unresolved proof obligations.

## Route

Construct

\[
T = \mathbb C[[x,y,z]]/(x^2-yz),
\]

apply a Jensen-style N-subring construction to obtain a two-dimensional local UFD `A` with trivial generic formal fiber, then use the contraction of `Q=(x,y)T` to produce a quotient of `A` that is not weakly quasi-complete.  The quotient characterization then shows that `A` is weakly quasi-complete but not quasi-complete.

## Current Phase Estimates

| Phase | Status | Main risk |
|---|---|---|
| Definitions and quotient criterion | active | quotient/intersection transport remains mostly unproved |
| Completion and formal-fiber criteria | next | Farley's criterion has no known direct Mathlib analogue |
| Explicit complete node `T` | next | multivariate power-series quotient infrastructure is sparse |
| Jensen N-subring extension lemmas | active | interfaces typecheck, but witness construction and full N-subring fields remain |
| Jensen transfinite saturation | next | current saturated-union and completion nodes are witness-checkers |
| Contraction and bad quotient | next | height and completion API alignment |

## Completed Milestones

- Built a source-ordered blueprint covering 42 nodes.
- Removed the starter `hello` scaffold.
- Added Lean definitions for quasi-completeness, weak quasi-completeness, generic formal fibers, and analytic irreducibility.
- Added the explicit node ring `T` and distinguished prime candidate `Q`.
- Proved connector lemmas that route the final Anderson conclusion through the bad quotient package.
- Reduced remaining `sorry`s from 18 to 10 in the latest Jensen-interface pass.

## Next High-Value Step

Replace the lightweight `NSubring` scaffold with Jensen's full definition: quasi-local UFD, cardinal bound, associated-prime contraction, and height control for associated primes of `T / tT`.  After that, the current Jensen witness-checking lemmas can be strengthened into actual construction lemmas following Jensen, Loepp, and Heitmann.
