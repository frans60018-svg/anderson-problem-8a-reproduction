# definition def:quasi_complete

## statement

Let \((R,M)\) be a Noetherian local ring.  The ring \(R\) is **quasi-complete**
if, for every decreasing sequence of ideals
\[
A_1\supseteq A_2\supseteq A_3\supseteq\cdots
\]
and every natural number \(k\), there is an index \(s_k\) such that
\[
A_{s_k}\subseteq \left(\bigcap_{n\geq 1}A_n\right)+M^k.
\]

# definition def:weakly_quasi_complete

## statement

Let \((R,M)\) be a Noetherian local ring.  The ring \(R\) is **weakly
quasi-complete** if, for every decreasing sequence of ideals \((A_n)_{n\geq1}\)
with \(\bigcap_{n\geq1}A_n=0\), and every natural number \(k\), there is an
index \(s_k\) such that
\[
A_{s_k}\subseteq M^k.
\]

# definition def:formal_fiber_and_analytic_irreducibility

## statement

If \((A,\mathfrak m)\) is a Noetherian local domain, \(K=\operatorname{Frac}(A)\),
and \(\widehat A\) is its \(\mathfrak m\)-adic completion, its **generic formal
fiber** is
\[
\operatorname{Spec}(\widehat A\otimes_A K).
\]
Its points correspond to the prime ideals \(P\subseteq\widehat A\) satisfying
\(P\cap A=(0)\).  The domain \(A\) is **analytically irreducible** if
\(\widehat A\) is a domain.

# lemma lem:complete_domain_choice

## statement

Let
\[
T=\mathbb C[[x,y,z]]/(x^2-yz),\qquad
\mathfrak M=(x,y,z)T,
\]
where the same letters denote the residue classes in \(T\).  Then:

1. \((T,\mathfrak M)\) is a complete two-dimensional Cohen--Macaulay local
   domain;
2. \(|T|=|T/\mathfrak M|=|\mathbb C|\); and
3. \(Q=(x,y)T\) is a nonprincipal height-one prime ideal.

## proof

Put \(S=\mathbb C[[x,y,z]]\).  Consider the continuous homomorphism
\[
\Phi:S\longrightarrow\mathbb C[[u,v]],\qquad
x\longmapsto uv,\quad y\longmapsto u^2,\quad z\longmapsto v^2.
\]
Formal division by the monic polynomial \(x^2-yz\), viewed as a polynomial in
\(x\) over \(\mathbb C[[y,z]]\), gives a unique expression
\[
F=A(y,z)+xB(y,z)+(x^2-yz)H
\]
for every \(F\in S\), with \(A,B\in\mathbb C[[y,z]]\).  The image of the
remainder is
\[
A(u^2,v^2)+uvB(u^2,v^2).
\]
The first summand contains only monomials whose two exponents are even, and
the second only monomials whose two exponents are odd.  Hence their sum can be
zero only when \(A=B=0\).  It follows that
\(\ker\Phi=(x^2-yz)\), so
\[
T\cong\mathbb C[[u^2,uv,v^2]]\subseteq\mathbb C[[u,v]].
\]
Thus \(T\) is a domain.

The ring \(S\) is a complete regular local ring of dimension three, and the
nonzero element \(x^2-yz\) is a nonzerodivisor.  Therefore its quotient \(T\)
is a complete Cohen--Macaulay hypersurface of dimension two.

There are countably many monomials in three variables, so
\[
|S|=|\mathbb C|^{\aleph_0}.
\]
Since \(|\mathbb C|=2^{\aleph_0}\), cardinal arithmetic gives
\[
|\mathbb C|^{\aleph_0}
=(2^{\aleph_0})^{\aleph_0}
=2^{\aleph_0\cdot\aleph_0}
=2^{\aleph_0}
=|\mathbb C|.
\]
The constants embed in \(T\), while \(T\) is a quotient of \(S\); hence
\(|T|=|\mathbb C|\).  Also \(T/\mathfrak M\cong\mathbb C\), proving the
cardinality assertion.

Finally,
\[
T/Q\cong\mathbb C[[z]],
\]
so \(Q\) is prime and is not maximal.  Since \(T\) is a two-dimensional
domain and
\((0)\subsetneq Q\subsetneq\mathfrak M\), its height is one.  The defining
equation lies in \((x,y,z)^2\), so the classes of \(x,y,z\) form a
\(\mathbb C\)-basis of \(\mathfrak M/\mathfrak M^2\).  Because
\(\mathfrak M Q\subseteq\mathfrak M^2\), the classes of \(x\) and \(y\) in
\(Q/\mathfrak M Q\) are linearly independent.  Consequently
\[
\mu_T(Q)=\dim_{T/\mathfrak M}(Q/\mathfrak M Q)\geq2.
\]
A nonzero principal ideal in a local ring needs at most one generator, so
\(Q\) is not principal.  ∎

# lemma lem:jensen_special_case

## statement

There exists a two-dimensional Noetherian local UFD \(A\) such that
\(\widehat A\cong T\) and the only prime ideal of \(\widehat A\) contracting to
\((0)\) in \(A\) is \((0)\).

## proof

We use the following external existence theorem, with its terminology expanded
before applying it.

**Complete cited statement (Jensen).**  D. Jensen, *Completions of UFDs with
Semi-Local Formal Fibers*, Communications in Algebra 34 (2006), 347--360
(paper_id: `10.1080/00927870500346321`; theorem_id: `Corollary 2.4`; arXiv id:
none): Let \((T,\mathfrak M)\) be a complete local ring satisfying
\(|T/\mathfrak M|=|T|\), and let \(P\in\operatorname{Spec}T\).  There exists a
local UFD \(A\) such that \(\widehat A\cong T\) and the generic formal fiber of
\(A\) is local with maximal prime \(P\) if and only if either

1. \(T\) is a field or a DVR and \(P=(0)\); or
2. \(\operatorname{depth}T\geq2\), \(P\) is nonmaximal and contains every
   associated prime of \(T\), \(P\) has zero intersection with the prime
   subring of \(T\), and every \(J\in\operatorname{Spec}T\) satisfying
   \(\operatorname{ht}J>\operatorname{depth}(T_J)=1\) is contained in \(P\).

In Jensen's paper, “local ring” means a Noetherian ring with one maximal ideal.
The assertion that the generic formal fiber is local with maximal prime \(P\)
means that \(P\) is the unique maximal member among the primes of \(T\)
contracting to zero in \(A\).  Jensen proves the sufficiency direction by a
transfinite construction of quasi-local UFD subrings (called N-subrings), using
the cardinality hypothesis to make transcendence choices and imposing ideal
contraction identities that make the final union Noetherian with completion
\(T\).  Thus the theorem's notions of UFD, completion, and generic formal fiber
are exactly the ones used here.

Apply the second case with the ring in Lemma
\(\ref{lem:complete_domain_choice}\) and with \(P=(0)\).  Completeness,
\(|T/\mathfrak M|=|T|\), and \(\operatorname{depth}T=2\) were proved there.
Because \(T\) is a domain, \(\operatorname{Ass}T=\{(0)\}\).  The prime
\((0)\) is nonmaximal and of course meets the prime subring only in zero.

It remains to check Jensen's last condition.  A localization of a
Cohen--Macaulay ring is Cohen--Macaulay.  Hence, for every prime \(J\) of \(T\),
\[
\operatorname{depth}(T_J)=\dim T_J=\operatorname{ht}J.
\]
There is therefore no \(J\) for which
\(\operatorname{ht}J>\operatorname{depth}(T_J)=1\), so the condition is
vacuous.  Jensen's corollary supplies a Noetherian local UFD \(A\) with
\(\widehat A\cong T\) whose generic formal fiber is local with maximal prime
\((0)\).

The Krull intersection theorem gives
\(\ker(A\to\widehat A)=\bigcap_{n\geq1}\mathfrak m_A^n=(0)\).  Fixing the
completion isomorphism \(\widehat A\cong T\), we may therefore identify \(A\)
with its image in \(T\); all contractions below use this fixed identification.

Primes in the generic formal fiber are exactly the primes of \(T\) contracting
to zero in \(A\).  Since \((0)\) is contained in every prime and is already the
maximal prime of this fiber, it is its only prime.  Finally, completion preserves
the dimension of a Noetherian local ring, so
\(\dim A=\dim\widehat A=\dim T=2\).  ∎

# lemma lem:a_is_weak_and_has_bad_quotient

## statement

For the ring \(A\) of Lemma \(\ref{lem:jensen_special_case}\):

1. \(A\) is weakly quasi-complete; and
2. there is a prime element \(a\in A\) such that \(A/aA\) is a
   one-dimensional Noetherian local domain that is not weakly quasi-complete.

## proof

First invoke the following completion criterion.

**Complete cited statement (Farley).**  J. D. Farley,
*Quasi-completeness and localizations of polynomial domains: A conjecture from
“Open Problems in Commutative Ring Theory”*, Bulletin of the Korean
Mathematical Society 53 (2016), 1613--1615
(paper_id: `BKMS.b140895`, DOI `10.4134/BKMS.b140895`; theorem_id:
`Proposition 1`; arXiv id: none): A Noetherian local integral domain \(R\) is
weakly quasi-complete if and only if
\[
P\cap R\neq(0)
\]
for every nonzero prime ideal \(P\) of its completion \(\widehat R\).

The ring \(A\) is a Noetherian local domain, and Lemma
\(\ref{lem:jensen_special_case}\) says that every nonzero prime of
\(\widehat A\cong T\) has nonzero contraction to \(A\).  Farley's proposition
therefore proves that \(A\) is weakly quasi-complete.

Now let \(Q=(x,y)T\) be the nonprincipal height-one prime from Lemma
\(\ref{lem:complete_domain_choice}\), and set
\[
q=Q\cap A.
\]
Since \(Q\neq(0)\) and \((0)\) is the only completion prime contracting to
zero, \(q\neq(0)\).  The completion map \(A\to\widehat A\cong T\) is faithfully
flat.  Flat going-down gives
\[
\operatorname{ht}q\leq\operatorname{ht}Q=1.
\]
On the other hand, a nonzero prime in the domain \(A\) has height at least one.
Thus \(\operatorname{ht}q=1\).  Every height-one prime of a UFD is generated by
a prime element, so
\[
q=aA
\]
for some prime element \(a\in A\).

We claim that \(aT\) is not prime.  The just-established injection
\(A\hookrightarrow T\) shows that \(a\neq0\) in \(T\), while
\(a\in q\subseteq Q\) gives the proper inclusion \(aT\subseteq Q\).  If
\(aT\) were prime, the principal ideal theorem would give
\(\operatorname{ht}(aT)\leq1\); nonzeroness in the domain \(T\) gives the
reverse inequality, so \(\operatorname{ht}(aT)=1\).  The inclusion of the
height-one primes \(aT\subseteq Q\) would then be equality, contradicting the
fact that \(Q\) is not principal.  Hence the proper ideal \(aT\) is not prime
and \(T/aT\) is not a domain.

Put \(B=A/aA\).  Because \(aA=q\) is prime, \(B\) is a Noetherian local
domain.  The ring \(A\) has dimension two and \(q\) is a nonmaximal
height-one prime, so \(\dim B=1\): the chain \(q\subsetneq\mathfrak m_A\)
gives the lower bound, while a longer chain above \(q\), preceded by
\((0)\subsetneq q\), would contradict \(\dim A=2\).  Completion commutes with
quotient by the finitely generated ideal \(aA\), and therefore
\[
\widehat B
\cong \widehat A/a\widehat A
\cong T/aT.
\]
This completion is not a domain, so \(B\) is not analytically irreducible.

We finish with the dimension-one criterion supplied in the problem, recorded
with its source.

**Complete cited statement (Anderson, dimension one).**  D. D. Anderson,
*Quasi-complete Semilocal Rings and Modules*, in *Commutative Algebra: Recent
Advances in Commutative Rings, Integer-Valued Polynomials, and Polynomial
Functions*, Springer, 2014, pp. 25--37
(paper_id: `10.1007/978-1-4939-0925-4_2`; theorem_id: `Corollary 2.2`; arXiv
id: none): A one-dimensional Noetherian local domain is weakly quasi-complete
if and only if it is analytically irreducible.  (The same criterion also
characterizes quasi-completeness in dimension one.)

The criterion applies to \(B\) and shows that \(B=A/aA\) is not weakly
quasi-complete.  ∎

# theorem thm:main

## statement

**Anderson Problem 8a: Weakly Quasi-Complete vs Quasi-Complete**

**Problem**

Prove that there exists a Noetherian local ring that is weakly quasi-complete but not quasi-complete.

Equivalently, answer in the negative the question:

> Is every weakly quasi-complete Noetherian local ring quasi-complete?

**Definitions**

Let `(R, M)` be a Noetherian local ring.

`R` is quasi-complete if, for every decreasing sequence of ideals

```text
A_1 ⊇ A_2 ⊇ A_3 ⊇ ...
```

and for every natural number `k`, there exists an index `s_k` such that

```text
A_{s_k} ⊆ (⋂_n A_n) + M^k.
```

`R` is weakly quasi-complete if the same condition holds for every decreasing sequence of ideals with zero intersection:

```text
⋂_n A_n = 0,
```

in which case the condition becomes

```text
A_{s_k} ⊆ M^k.
```

**Background Facts Allowed**

The following facts are allowed to be used if relevant. They are part of the mathematical context of the problem.

1. If a Noetherian local ring is complete, then it is quasi-complete.

2. Quasi-complete implies weakly quasi-complete.

3. A Noetherian local ring `R` is quasi-complete if and only if every homomorphic image of `R` is weakly quasi-complete.

4. A one-dimensional Noetherian local domain is weakly quasi-complete if and only if it is analytically irreducible.

5. A one-dimensional Noetherian local domain is quasi-complete if and only if it is analytically irreducible.

6. A Noetherian local domain `R` is weakly quasi-complete if and only if every nonzero prime ideal of its completion has nonzero contraction to `R`.

**Expected Output**

Produce a rigorous informal proof blueprint. The blueprint should include:

1. The construction of a Noetherian local ring `R`.
2. A proof that `R` is weakly quasi-complete.
3. A proof that `R` is not quasi-complete.
4. Clear references to any external commutative algebra results used.
5. Enough detail that the argument could later be translated into Lean 4.

**Constraints**

Do not assume the desired counterexample exists without construction. If an external existence theorem is used, state the theorem precisely enough to check that its hypotheses apply.

## proof

Let \(A\) be the two-dimensional Noetherian local UFD constructed in Lemma
\(\ref{lem:jensen_special_case}\).  By Lemma
\(\ref{lem:a_is_weak_and_has_bad_quotient}\), \(A\) is weakly
quasi-complete.  The same lemma produces a prime element \(a\in A\) for which
the homomorphic image \(A/aA\) is not weakly quasi-complete.

We apply the following quotient characterization, which is also Background
Fact 3 in the problem.

**Complete cited statement (Anderson, quotients).**  D. D. Anderson,
*Quasi-complete Semilocal Rings and Modules*, Springer, 2014
(paper_id: `10.1007/978-1-4939-0925-4_2`; theorem_id: `Theorem 1.3`; arXiv id:
none): A Noetherian local ring \(R\) is quasi-complete if and only if every
homomorphic image \(R/I\) is weakly quasi-complete.

Since the homomorphic image \(A/aA\) is not weakly quasi-complete, this
criterion shows that \(A\) is not quasi-complete.  Thus \(A\) is a Noetherian
local ring that is weakly quasi-complete but not quasi-complete.  ∎
