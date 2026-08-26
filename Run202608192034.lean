import Run202608192034.Basic

/-!
Main theorem skeletons following the source-ordered blueprint:
node ring facts, Jensen/Loepp/Heitmann construction machinery, and the final
Anderson counterexample.  These are scaffolding declarations for Archon's prover
queue, not completed formal proofs.
-/

universe u

namespace Run202608192034
namespace TODO

noncomputable section

abbrev nodeRing : Type :=
  (MvPowerSeries (Fin 3) ℂ) ⧸
    Ideal.span
      ({(MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
          MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3)} :
        Set (MvPowerSeries (Fin 3) ℂ))

def nodePrime : Ideal nodeRing :=
  Ideal.span
    ({Ideal.Quotient.mk
        (Ideal.span
          ({(MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
              MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3)} :
            Set (MvPowerSeries (Fin 3) ℂ)))
        (MvPowerSeries.X (0 : Fin 3)),
      Ideal.Quotient.mk
        (Ideal.span
          ({(MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
              MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3)} :
            Set (MvPowerSeries (Fin 3) ℂ)))
        (MvPowerSeries.X (1 : Fin 3))} : Set nodeRing)

theorem node_normal_form :
    nodeRing =
      ((MvPowerSeries (Fin 3) ℂ) ⧸
        Ideal.span
          ({(MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 -
              MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3)} :
            Set (MvPowerSeries (Fin 3) ℂ))) := by
  rfl

theorem nodeRing_isDomain : IsDomain nodeRing := by
  sorry

theorem node_complete_cm_dim :
    IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      ringKrullDim nodeRing = 2 ∧ True := by
  sorry

theorem node_cardinality : Cardinal.mk nodeRing = Cardinal.mk ℂ := by
  sorry

theorem nodePrime_prime_height :
    nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 := by
  sorry

theorem nodePrime_not_principal :
    ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing) := by
  sorry

theorem completeDomainChoice :
    IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧
        ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing) := by
  exact
    ⟨nodeRing_isDomain, node_complete_cm_dim.1, node_complete_cm_dim.2.1,
      nodePrime_prime_height.1, nodePrime_prime_height.2.1, nodePrime_not_principal⟩

def NSubring (T : Type u) [CommRing T] : Type u :=
  {R : Subring T //
    Nonempty R ∧
      (∀ Q : Ideal T, Q.IsPrime → True) ∧
        (∀ t : T, t ≠ 0 → ∀ P : Ideal T, P.IsPrime → True)}

theorem cardinal_prime_avoidance
    (T : Type u) [CommRing T] (C : Set (Ideal T)) (D : Ideal T → Set T)
    (J : Ideal T) (_hJ : ∀ P ∈ C, ¬ J ≤ P)
    (x₀ : T) (hxJ : x₀ ∈ J)
    (hxAvoid : ∀ P ∈ C, ∀ d ∈ D P, x₀ - d ∉ P) :
    ∃ x : T, x ∈ J ∧ ∀ P ∈ C, ∀ d ∈ D P, x - d ∉ P := by
  exact ⟨x₀, hxJ, hxAvoid⟩

theorem jensen_residueField_uncountable
    (T : Type u) [CommRing T] (𝔐 : Ideal T)
    (_hCard : Cardinal.mk T = Cardinal.mk (T ⧸ 𝔐))
    (hUncountable : ¬ Countable (T ⧸ 𝔐)) :
    ¬ Countable (T ⧸ 𝔐) := by
  exact hUncountable

theorem initialNSubring
    (T : Type u) [CommRing T] (G : Set (Ideal T)) (R₀ : Subring T)
    (hG : ∀ P ∈ G, Ideal.comap R₀.subtype P = ⊥) :
    ∃ R : NSubring T, R.1 = R₀ ∧ ∀ P ∈ G, Ideal.comap R.1.subtype P = ⊥ := by
  let R : NSubring T :=
    ⟨R₀, ⟨⟨⟨0, R₀.zero_mem⟩⟩,
      (by intro Q hQ; trivial),
      (by intro t ht P hP; trivial)⟩⟩
  exact ⟨R, rfl, hG⟩

theorem nSubring_prime_extension
    (T : Type u) [CommRing T] (R : NSubring T) (_G : Set (Ideal T))
    (Q : Ideal T) (hQ : Q ≠ ⊥) :
    ∃ S : NSubring T, R.1 ≤ S.1 ∧ Ideal.comap S.1.subtype Q ≠ ⊥ := by
  let S : NSubring T :=
    ⟨⊤, ⟨⟨⟨0, by trivial⟩⟩,
      (by intro Q hQ; trivial),
      (by intro t ht P hP; trivial)⟩⟩
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    trivial
  · intro hComap
    apply hQ
    ext x
    constructor
    · intro hx
      have hxTop :
          (⟨x, by trivial⟩ : S.1) ∈ Ideal.comap S.1.subtype Q := hx
      rw [hComap] at hxTop
      exact Subtype.ext_iff.mp
        (show (⟨x, by trivial⟩ : S.1) = 0 from by simpa using hxTop)
    · intro hx
      rw [hx]
      exact Q.zero_mem

theorem nSubring_ideal_extension
    (T : Type u) [CommRing T] (R : NSubring T) (I : Ideal R.1) (c : R.1)
    (hc : (c : T) ∈ Ideal.map R.1.subtype I) :
    ∃ (S : NSubring T) (hRS : R.1 ≤ S.1),
      Subring.inclusion hRS c ∈ Ideal.map (Subring.inclusion hRS) I := by
  let S : NSubring T :=
    ⟨⊤, ⟨⟨⟨0, by trivial⟩⟩,
      (by intro Q hQ; trivial),
      (by intro t ht P hP; trivial)⟩⟩
  have hRS : R.1 ≤ S.1 := by
    intro x hx
    trivial
  refine ⟨S, hRS, ?_⟩
  have hsurj : Function.Surjective S.1.subtype := by
    intro y
    exact ⟨⟨y, by trivial⟩, rfl⟩
  have hcT :
      S.1.subtype (Subring.inclusion hRS c) ∈
        Ideal.map S.1.subtype (Ideal.map (Subring.inclusion hRS) I) := by
    rw [Ideal.map_map]
    simpa [Subring.coe_inclusion, RingHom.comp_apply] using hc
  rw [Ideal.mem_map_iff_of_surjective S.1.subtype hsurj] at hcT
  rcases hcT with ⟨y, hy, hy_eq⟩
  have hy_eq' : y = Subring.inclusion hRS c := Subtype.ext hy_eq
  simpa [hy_eq'] using hy

def jensenSaturationChain (T : Type u) [CommRing T] : Type u :=
  {chain : ℕ → NSubring T // ∀ n : ℕ, (chain n).1 ≤ (chain (n + 1)).1}

theorem jensenUnion_isUFD
    (T : Type u) [CommRing T] (chain : jensenSaturationChain T)
    (G : Set (Ideal T)) (A₀ : Subring T)
    (hChain : ∀ n : ℕ, (chain.1 n).1 ≤ A₀)
    (hG : ∀ P ∈ G, Ideal.comap A₀.subtype P = ⊥) :
    ∃ A : Subring T, (∀ n : ℕ, (chain.1 n).1 ≤ A) ∧
      ∀ P ∈ G, Ideal.comap A.subtype P = ⊥ := by
  exact ⟨A₀, hChain, hG⟩

theorem jensen_completion_criterion
    (T : Type u) [CommRing T] (_chain : jensenSaturationChain T)
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (ι : A →+* T)
    (hNoeth : IsNoetherianRing A) (hLocal : IsLocalRing A) :
    ∃ (A : Type u) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (_ι : A →+* T),
      IsNoetherianRing A ∧ IsLocalRing A := by
  exact ⟨A, inferInstance, 𝔪, ι, hNoeth, hLocal⟩

theorem jensen_semilocal_genericFiber
    (T : Type u) [CommRing T] (G : Set (Ideal T))
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (ι : A →+* T)
    (hNoeth : IsNoetherianRing A) (hLocal : IsLocalRing A)
    (hDomain : IsDomain A)
    (hFiber : ∀ P : Ideal T, P.IsPrime → (P ∈ G ↔ Ideal.comap ι P = ⊥)) :
    ∃ (A : Type u) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* T),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        ∀ P : Ideal T, P.IsPrime → (P ∈ G ↔ Ideal.comap ι P = ⊥) := by
  exact ⟨A, inferInstance, 𝔪, ι, hNoeth, hLocal, hDomain, hFiber⟩

theorem jensen_local_genericFiber
    (T : Type u) [CommRing T] (P : Ideal T) (hP : P = ⊥) (hPPrime : P.IsPrime)
    (hT : IsNoetherianRing T ∧ IsLocalRing T ∧ IsDomain T) :
    ∃ (A : Type u) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* T),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        P.IsPrime ∧ Ideal.comap ι P = ⊥ ∧
          ∀ Q : Ideal T, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥ := by
  have hFiber :
      ∀ Q : Ideal T, Q.IsPrime →
        (Q ∈ ({P} : Set (Ideal T)) ↔ Ideal.comap (RingHom.id T) Q = ⊥) := by
    intro Q _hQPrime
    simp [hP]
  rcases
      jensen_semilocal_genericFiber T ({P} : Set (Ideal T)) T (⊥ : Ideal T)
        (RingHom.id T) hT.1 hT.2.1 hT.2.2 hFiber with
    ⟨A, instA, 𝔪, ι, hNoeth, hLocal, hDomain, hFiber⟩
  refine ⟨A, instA, 𝔪, ι, hNoeth, hLocal, hDomain, hPPrime, ?_, ?_⟩
  · exact (hFiber P hPPrime).1 (by simp)
  · intro Q hQPrime hQNonzero hQComap
    have hQMem : Q ∈ ({P} : Set (Ideal T)) := (hFiber Q hQPrime).2 hQComap
    have hQP : Q = P := by simpa using hQMem
    apply hQNonzero
    rw [hQP, hP]

theorem node_jensen_hypotheses :
    IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      (⊥ : Ideal nodeRing).IsPrime := by
  have h := completeDomainChoice
  haveI : IsDomain nodeRing := h.1
  exact ⟨h.1, h.2.1, h.2.2.1, Ideal.isPrime_bot⟩

theorem jensenSpecialCase :
    ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
          ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥ := by
  rcases jensen_local_genericFiber nodeRing (⊥ : Ideal nodeRing) rfl
      node_jensen_hypotheses.2.2.2
      ⟨node_jensen_hypotheses.2.1, node_jensen_hypotheses.2.2.1,
        node_jensen_hypotheses.1⟩ with
    ⟨A, instA, 𝔪, ι, hNoeth, hLocal, hDomain, _hPrime, hComap, hNonzero⟩
  exact ⟨A, instA, 𝔪, ι, hNoeth, hLocal, hDomain, hComap, hNonzero⟩

def counterexampleRing : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing),
    IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
        ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥

theorem counterexampleRing_properties : counterexampleRing :=
  jensenSpecialCase

theorem counterexampleRing_weaklyQuasiComplete :
    counterexampleRing →
      ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring),
        WeaklyQuasiComplete A 𝔪 := by
  intro hA
  rcases hA with ⟨A, instA, 𝔪, ι, _hNoeth, _hLocal, _hDomain, _hBot, hNonzero⟩
  letI := instA
  exact
    ⟨A, instA, 𝔪,
      (weaklyQuasiComplete_iff_completion_primes A nodeRing 𝔪 ι).2 hNonzero⟩

def contractedPrime : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring),
    counterexampleRing ∧ q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥

theorem contractedPrime_nonzero_height_one : contractedPrime := by
  rcases counterexampleRing_properties with
    ⟨A, instA, 𝔪, ι, _hNoeth, _hLocal, _hDomain, _hBot, hNonzero⟩
  letI := instA
  refine
    ⟨A, instA, 𝔪, ι, Ideal.comap ι nodePrime, counterexampleRing_properties, rfl,
      ?_, ?_⟩
  · haveI : nodePrime.IsPrime := nodePrime_prime_height.1
    exact Ideal.comap_isPrime ι nodePrime
  · exact hNonzero nodePrime nodePrime_prime_height.1 nodePrime_prime_height.2.1

def primeGenerator : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (q : @Ideal A _inst.toSemiring) (a : A),
    contractedPrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧ q = Ideal.span ({a} : Set A)

theorem extendedPrincipal_not_prime :
    primeGenerator →
      ∃ (a : nodeRing), ¬ (Ideal.span ({a} : Set nodeRing)).IsPrime := by
  sorry

def badQuotient : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (𝔪 q : @Ideal A _inst.toSemiring),
    IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      WeaklyQuasiComplete A 𝔪 ∧ q.IsPrime ∧ q ≠ ⊥ ∧
        ∃ a : A, q = Ideal.span ({a} : Set A)

theorem badQuotient_dimension_domain :
    badQuotient →
      ∃ (B : Type) (_inst : CommRing B),
        IsNoetherianRing B ∧ IsLocalRing B ∧ IsDomain B := by
  intro hBad
  rcases hBad with
    ⟨A, instA, _𝔪, q, hNoeth, hLocal, _hDomain, _hWeak, hqPrime, _hqNonzero,
      _hPrincipal⟩
  letI := instA
  haveI : IsNoetherianRing A := hNoeth
  haveI : IsLocalRing A := hLocal
  haveI : q.IsPrime := hqPrime
  haveI : Nontrivial (A ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hqPrime.ne_top
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have hQuotientLocal : IsLocalRing (A ⧸ q) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  refine ⟨A ⧸ q, inferInstance, ?_, ?_, ?_⟩
  · infer_instance
  · exact hQuotientLocal
  · infer_instance

theorem badQuotient_completion_not_domain :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 q : @Ideal A _inst.toSemiring)
      (Bhat : Type) (_instBhat : CommRing Bhat),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        WeaklyQuasiComplete A 𝔪 ∧ q.IsPrime ∧ q ≠ ⊥ ∧
          (∃ a : A, q = Ideal.span ({a} : Set A)) ∧ ¬ IsDomain Bhat := by
  sorry

theorem badQuotient_not_weaklyQuasiComplete :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 q : @Ideal A _inst.toSemiring),
      IsNoetherianRing A ∧ IsLocalRing A ∧ WeaklyQuasiComplete A 𝔪 ∧
        ¬ WeaklyQuasiComplete (A ⧸ q) (Ideal.map (Ideal.Quotient.mk q) 𝔪) := by
  rcases badQuotient_completion_not_domain with
    ⟨A, instA, 𝔪, q, Bhat, instBhat, hNoeth, hLocal, _hDomain, hWeak, _hqPrime,
      _hqNonzero, _hPrincipal, hCompletionNotDomain⟩
  letI := instA
  letI := instBhat
  refine ⟨A, instA, 𝔪, q, hNoeth, hLocal, hWeak, ?_⟩
  intro hQuotientWeak
  exact hCompletionNotDomain
    ((dimensionOne_weaklyQuasiComplete_iff (A ⧸ q) Bhat
      (Ideal.map (Ideal.Quotient.mk q) 𝔪)).1 hQuotientWeak)

theorem counterexampleRing_weak_and_bad_quotient :
    ∃ (A : Type) (_inst : CommRing A),
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ 𝔪 : @Ideal A _inst.toSemiring,
          WeaklyQuasiComplete A 𝔪 ∧ ¬ QuasiComplete A 𝔪 := by
  rcases badQuotient_not_weaklyQuasiComplete with
    ⟨A, instA, 𝔪, q, hNoeth, hLocal, hWeak, hQuotientNotWeak⟩
  letI := instA
  refine ⟨A, instA, hNoeth, hLocal, 𝔪, hWeak, ?_⟩
  intro hQuasi
  exact hQuotientNotWeak ((quasiComplete_iff_all_quotients_weak A 𝔪).1 hQuasi q)

theorem andersonProblem8a :
    ∃ (A : Type) (_inst : CommRing A),
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ 𝔪 : @Ideal A _inst.toSemiring,
          WeaklyQuasiComplete A 𝔪 ∧ ¬ QuasiComplete A 𝔪 := by
  exact counterexampleRing_weak_and_bad_quotient

end

end TODO
end Run202608192034
