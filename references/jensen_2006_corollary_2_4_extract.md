# Relevant extract: Jensen, Corollary 2.4

Source: D. Jensen, “Completions of UFDs with Semi-Local Formal Fibers,”
Communications in Algebra 34 (2006), 347–360,
DOI `10.1080/00927870500346321`, Corollary 2.4.

Terminology from the paper:

- A “local ring” is Noetherian and has one maximal ideal.
- For a local domain `A`, the generic formal fiber is
  `Spec(Ahat tensor_A Frac(A))`; its points correspond exactly to primes of
  `Ahat` contracting to `(0)` in `A`.
- Saying this fiber is local with maximal ideal `P` means that `P` is the unique
  maximal prime of `Ahat` contracting to zero.

Precise statement (faithful paraphrase).  Let `(T,M)` be a complete local ring
with `|T/M|=|T|`, and let `P` be a prime of `T`.  There is a local UFD `A` whose
completion is `T` and whose generic formal fiber is local with maximal prime
`P` exactly in either of these cases:

1. `T` is a field or a DVR and `P=(0)`; or
2. `depth(T)>=2`, `P` is nonmaximal and contains every associated prime of
   `T`, `P` meets the prime subring only in zero, and every prime `J` satisfying
   `ht(J)>depth(T_J)=1` is contained in `P`.

Proof context read from the paper: the result is the local specialization of
Theorem 2.2.  Its sufficiency direction constructs a directed union of
quasi-local UFD subrings (“N-subrings”) inside `T`.  Transcendence choices and
cardinality avoidance preserve zero contraction for the prescribed primes,
force every other prime to meet the union, preserve prime elements, and ensure
the ideal-contraction identities needed for the union to be Noetherian with
completion `T`.  The depth and associated-prime hypotheses are what permit the
N-subring construction; the cardinality equality is used in the transfinite
adjoining step.

The original PDF was inspected through the web tool’s PDF text extraction;
direct shell download was blocked by workspace network DNS.
