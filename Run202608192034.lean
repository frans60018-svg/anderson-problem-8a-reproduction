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

theorem completeDomainChoice :
    IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      ringKrullDim nodeRing = 2 ∧ Cardinal.mk nodeRing = Cardinal.mk ℂ ∧
        nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 ∧
          ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing) := by
  sorry

theorem nodeRing_isDomain : IsDomain nodeRing := by
  exact completeDomainChoice.1

theorem node_complete_cm_dim :
    IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      ringKrullDim nodeRing = 2 ∧ True := by
  rcases completeDomainChoice with
    ⟨_hDomain, hNoeth, hLocal, hDim, _hCard, _hPrime, _hNonzero, _hHeight,
      _hNotPrincipal⟩
  exact ⟨hNoeth, hLocal, hDim, trivial⟩

theorem node_cardinality : Cardinal.mk nodeRing = Cardinal.mk ℂ := by
  rcases completeDomainChoice with
    ⟨_hDomain, _hNoeth, _hLocal, _hDim, hCard, _hPrime, _hNonzero, _hHeight,
      _hNotPrincipal⟩
  exact hCard

theorem nodePrime_prime_height :
    nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 := by
  rcases completeDomainChoice with
    ⟨_hDomain, _hNoeth, _hLocal, _hDim, _hCard, hPrime, hNonzero, hHeight,
      _hNotPrincipal⟩
  exact ⟨hPrime, hNonzero, hHeight⟩

theorem nodePrime_not_principal :
    ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing) := by
  rcases completeDomainChoice with
    ⟨_hDomain, _hNoeth, _hLocal, _hDim, _hCard, _hPrime, _hNonzero, _hHeight,
      hNotPrincipal⟩
  exact hNotPrincipal

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
    (∀ (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing),
      WeaklyQuasiComplete A 𝔪 ↔
        ∀ P : Ideal nodeRing, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥) →
    counterexampleRing →
      ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring),
        WeaklyQuasiComplete A 𝔪 := by
  intro hCriterion hA
  rcases hA with ⟨A, instA, 𝔪, ι, _hNoeth, _hLocal, _hDomain, _hBot, hNonzero⟩
  letI := instA
  exact
    ⟨A, instA, 𝔪,
      (weaklyQuasiComplete_iff_completion_primes A nodeRing 𝔪 ι
        (hCriterion A 𝔪 ι)).2 hNonzero⟩

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
  ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A),
    counterexampleRing ∧ IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      WeaklyQuasiComplete A 𝔪 ∧ Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
        (∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥) ∧
          q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
            q = Ideal.span ({a} : Set A)

theorem primeGenerator_source : primeGenerator := by
  sorry

theorem extendedPrincipal_not_prime_of_generator_data
    (A : Type u) [CommRing A] (ι : A →+* nodeRing) (q : Ideal A) (a : A)
    (hBot : Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥)
    (hqComap : q = Ideal.comap ι nodePrime)
    (hqNonzero : q ≠ ⊥)
    (hqPrincipal : q = Ideal.span ({a} : Set A)) :
    ¬ (Ideal.span ({ι a} : Set nodeRing)).IsPrime := by
  have hMapPrincipal :
      Ideal.map ι q = Ideal.span ({ι a} : Set nodeRing) := by
    calc
      Ideal.map ι q = Ideal.map ι (Ideal.span ({a} : Set A)) := by
        rw [hqPrincipal]
      _ = Ideal.span (ι '' ({a} : Set A)) := Ideal.map_span ι ({a} : Set A)
      _ = Ideal.span ({ι a} : Set nodeRing) := by simp
  have hMapLeNodePrime : Ideal.map ι q ≤ nodePrime := by
    rw [hqComap]
    exact Ideal.map_comap_le
  have hPrincipalLeNodePrime : Ideal.span ({ι a} : Set nodeRing) ≤ nodePrime := by
    simpa [hMapPrincipal] using hMapLeNodePrime
  intro hPrincipalPrime
  have hNodePrime : nodePrime.IsPrime := nodePrime_prime_height.1
  have hNodeHeight : nodePrime.height = 1 := nodePrime_prime_height.2.2
  have hNodeNotPrincipal :
      ¬ ∃ b : nodeRing, nodePrime = Ideal.span ({b} : Set nodeRing) :=
    nodePrime_not_principal
  haveI : IsDomain nodeRing := nodeRing_isDomain
  haveI : IsNoetherianRing nodeRing := node_complete_cm_dim.1
  have hInjective : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact hBot
  have hMapNonzero : Ideal.map ι q ≠ ⊥ := by
    intro hMapBot
    exact hqNonzero ((Ideal.map_eq_bot_iff_of_injective hInjective).mp hMapBot)
  have hPrincipalNonzero :
      Ideal.span ({ι a} : Set nodeRing) ≠ ⊥ := by
    simpa [hMapPrincipal] using hMapNonzero
  have hPrincipalProper :
      Ideal.span ({ι a} : Set nodeRing) ≠ ⊤ := by
    intro hTop
    exact hNodePrime.ne_top
      (top_le_iff.mp (by simpa [hTop] using hPrincipalLeNodePrime))
  have hPrincipalHeightLe :
      (Ideal.span ({ι a} : Set nodeRing)).height ≤ 1 := by
    have hRankLe :
        Cardinal.toENat
            (Submodule.spanRank (Ideal.span ({ι a} : Set nodeRing))) ≤
          (1 : ℕ∞) := by
      calc
        Cardinal.toENat
            (Submodule.spanRank (Ideal.span ({ι a} : Set nodeRing))) ≤
            Cardinal.toENat (Cardinal.mk ({ι a} : Set nodeRing)) :=
          Cardinal.toENat.monotone'
            (Submodule.spanRank_span_le_card ({ι a} : Set nodeRing))
        _ = (1 : ℕ∞) := by simp
    exact (Ideal.height_le_spanRank_toENat
      (Ideal.span ({ι a} : Set nodeRing)) hPrincipalProper).trans hRankLe
  have hBotLtPrincipal :
      (⊥ : Ideal nodeRing) < Ideal.span ({ι a} : Set nodeRing) := by
    exact bot_lt_iff_ne_bot.mpr hPrincipalNonzero
  have hPrincipalHeightPos :
      0 < (Ideal.span ({ι a} : Set nodeRing)).height := by
    have hStrict :
        (⊥ : Ideal nodeRing).height <
          (Ideal.span ({ι a} : Set nodeRing)).height :=
      Ideal.height_strict_mono_of_is_prime hBotLtPrincipal
    simpa [Ideal.height_bot] using hStrict
  have hPrincipalHeightEq :
      (Ideal.span ({ι a} : Set nodeRing)).height = 1 := by
    refine le_antisymm hPrincipalHeightLe ?_
    exact ENat.one_le_iff_ne_zero.mpr (ne_of_gt hPrincipalHeightPos)
  have hPrincipalEqNode : Ideal.span ({ι a} : Set nodeRing) = nodePrime := by
    by_contra hNe
    have hLt : Ideal.span ({ι a} : Set nodeRing) < nodePrime :=
      lt_of_le_of_ne hPrincipalLeNodePrime hNe
    have hPrimeHeightLt :
        (Ideal.span ({ι a} : Set nodeRing)).primeHeight < nodePrime.primeHeight :=
      Ideal.primeHeight_strict_mono hLt
    have hPrincipalPrimeHeight :
        (Ideal.span ({ι a} : Set nodeRing)).primeHeight = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hPrincipalHeightEq
    have hNodePrimeHeight : nodePrime.primeHeight = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hNodeHeight
    rw [hPrincipalPrimeHeight, hNodePrimeHeight] at hPrimeHeightLt
    exact (lt_irrefl (1 : ℕ∞)) hPrimeHeightLt
  exact hNodeNotPrincipal ⟨ι a, hPrincipalEqNode.symm⟩

theorem extendedPrincipal_not_prime :
    primeGenerator →
      ∃ (a : nodeRing), ¬ (Ideal.span ({a} : Set nodeRing)).IsPrime := by
  intro hGen
  rcases hGen with
    ⟨A, instA, _𝔪, ι, q, a, _hCounter, _hNoeth, _hLocal, _hDomain, _hWeak,
      hBot, _hNonzeroContraction, hqComap, _hqPrime, _hqNonzero,
      hqPrincipal⟩
  letI := instA
  exact
    ⟨ι a,
      extendedPrincipal_not_prime_of_generator_data A ι q a hBot hqComap
        _hqNonzero hqPrincipal⟩

def badQuotient : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A),
    IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      WeaklyQuasiComplete A 𝔪 ∧
        Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
          q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
            q = Ideal.span ({a} : Set A)

structure BadQuotientSourceData where
  A : Type
  [instA : CommRing A]
  𝔪 : Ideal A
  ι : A →+* nodeRing
  q : Ideal A
  a : A
  hCounter : counterexampleRing
  hNoeth : IsNoetherianRing A
  hLocal : IsLocalRing A
  hDomain : IsDomain A
  hWeak : WeaklyQuasiComplete A 𝔪
  hBot : Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥
  hNonzeroContraction :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥
  hqComap : q = Ideal.comap ι nodePrime
  hqPrime : q.IsPrime
  hqNonzero : q ≠ ⊥
  hqPrincipal : q = Ideal.span ({a} : Set A)

attribute [instance] BadQuotientSourceData.instA

def BadQuotientSourceData.QuasiCriterion
    (d : BadQuotientSourceData) : Prop :=
  QuasiComplete d.A d.𝔪 ↔
    ∀ J : Ideal d.A,
      WeaklyQuasiComplete (d.A ⧸ J) (Ideal.map (Ideal.Quotient.mk J) d.𝔪)

def BadQuotientSourceData.DimensionCriterion
    (d : BadQuotientSourceData) : Prop :=
  WeaklyQuasiComplete (d.A ⧸ d.q)
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
      AnalyticallyIrreducible (d.A ⧸ d.q)
        (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing))

structure JensenCompletionWitness
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing) where
  Ahat : Type
  [instAhat : CommRing Ahat]
  completionMap : A →+* Ahat
  completionEquiv : Ahat ≃+* nodeRing
  map_compatible : ι = completionEquiv.toRingHom.comp completionMap
  weakCriterion :
    WeaklyQuasiComplete A 𝔪 ↔
      ∀ P : Ideal nodeRing, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥

attribute [instance] JensenCompletionWitness.instAhat

structure QuotientCompletionWitness (d : BadQuotientSourceData) where
  Bhat : Type
  [instBhat : CommRing Bhat]
  quotientCompletionEquiv :
    Bhat ≃+* (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing))
  analyticCriterionOnBhat :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q) Bhat

attribute [instance] QuotientCompletionWitness.instBhat

theorem QuotientCompletionWitness.dimensionCriterion
    {d : BadQuotientSourceData} (w : QuotientCompletionWitness d) :
    d.DimensionCriterion := by
  dsimp [BadQuotientSourceData.DimensionCriterion] at *
  constructor
  · intro hWeak
    have hBhatDomain :
        AnalyticallyIrreducible (d.A ⧸ d.q) w.Bhat :=
      w.analyticCriterionOnBhat.1 hWeak
    dsimp [AnalyticallyIrreducible] at hBhatDomain ⊢
    haveI : IsDomain w.Bhat := hBhatDomain
    exact MulEquiv.isDomain w.Bhat w.quotientCompletionEquiv.symm.toMulEquiv
  · intro hNodeDomain
    apply w.analyticCriterionOnBhat.2
    dsimp [AnalyticallyIrreducible] at hNodeDomain ⊢
    haveI : IsDomain
        (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing)) := hNodeDomain
    exact MulEquiv.isDomain
      (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing))
      w.quotientCompletionEquiv.toMulEquiv

structure BadQuotientStructuredSource where
  data : BadQuotientSourceData
  jensenCompletion :
    JensenCompletionWitness data.A data.𝔪 data.ι
  quotientCompletion : QuotientCompletionWitness data
  quasiCriterion : data.QuasiCriterion

theorem BadQuotientSourceData.to_badQuotient
    (d : BadQuotientSourceData) : badQuotient := by
  exact
    ⟨d.A, d.instA, d.𝔪, d.ι, d.q, d.a, d.hNoeth, d.hLocal, d.hDomain,
      d.hWeak, d.hBot, d.hqComap, d.hqPrime, d.hqNonzero, d.hqPrincipal⟩

theorem BadQuotientSourceData.to_contractedPrime
    (d : BadQuotientSourceData) : contractedPrime := by
  exact
    ⟨d.A, d.instA, d.𝔪, d.ι, d.q, d.hCounter, d.hqComap, d.hqPrime,
      d.hqNonzero⟩

theorem BadQuotientSourceData.to_primeGenerator
    (d : BadQuotientSourceData) : primeGenerator := by
  exact
    ⟨d.A, d.instA, d.𝔪, d.ι, d.q, d.a, d.hCounter, d.hNoeth, d.hLocal,
      d.hDomain, d.hWeak, d.hBot, d.hNonzeroContraction, d.hqComap,
      d.hqPrime, d.hqNonzero, d.hqPrincipal⟩

theorem badQuotient_dimension_domain :
    badQuotient →
      ∃ (B : Type) (_inst : CommRing B),
        IsNoetherianRing B ∧ IsLocalRing B ∧ IsDomain B := by
  intro hBad
  rcases hBad with
    ⟨A, instA, _𝔪, _ι, q, _a, hNoeth, hLocal, _hDomain, _hWeak, _hBot,
      _hqComap, hqPrime, _hqNonzero, _hqPrincipal⟩
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

theorem quotient_not_domain_of_not_prime
    {R : Type u} [CommRing R] (I : Ideal R) (hI : ¬ I.IsPrime) :
    ¬ IsDomain (R ⧸ I) := by
  intro hDomain
  haveI : IsDomain (R ⧸ I) := hDomain
  exact hI (by simpa [Ideal.mk_ker] using
    (RingHom.ker_isPrime (Ideal.Quotient.mk I)))

theorem badQuotient_sourceData_from_jensen :
    ∃ _ : BadQuotientSourceData, True := by
  rcases primeGenerator_source with
    ⟨A, instA, 𝔪, ι, q, a, hCounter, hNoeth, hLocal, hDomain, hWeak, hBot,
      hNonzeroContraction, hqComap, hqPrime, hqNonzero, hqPrincipal⟩
  letI := instA
  exact
    ⟨⟨A, 𝔪, ι, q, a, hCounter, hNoeth, hLocal, hDomain, hWeak, hBot,
      hNonzeroContraction, hqComap, hqPrime, hqNonzero, hqPrincipal⟩,
      trivial⟩

noncomputable def jensenCompletionWitness_source
    (d : BadQuotientSourceData) :
    JensenCompletionWitness d.A d.𝔪 d.ι := by
  sorry

noncomputable def quotientCompletionWitness_source
    (d : BadQuotientSourceData)
    (_w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    QuotientCompletionWitness d := by
  sorry

theorem badQuotient_quasiCriterion_source
    (d : BadQuotientSourceData)
    (_w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    d.QuasiCriterion := by
  sorry

theorem badQuotient_structured_source :
    ∃ _ : BadQuotientStructuredSource, True := by
  rcases badQuotient_sourceData_from_jensen with ⟨d, _hd⟩
  let w : JensenCompletionWitness d.A d.𝔪 d.ι :=
    jensenCompletionWitness_source d
  let qw : QuotientCompletionWitness d :=
    quotientCompletionWitness_source d w
  let hQuasi : d.QuasiCriterion :=
    badQuotient_quasiCriterion_source d w
  exact ⟨⟨d, w, qw, hQuasi⟩, trivial⟩

theorem badQuotient_structured_criteria_source :
    ∃ d : BadQuotientSourceData,
      d.QuasiCriterion ∧ d.DimensionCriterion := by
  rcases badQuotient_structured_source with ⟨s, _hs⟩
  exact
    ⟨s.data, s.quasiCriterion,
      s.quotientCompletion.dimensionCriterion⟩

theorem badQuotient_criteria_source :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        WeaklyQuasiComplete A 𝔪 ∧
          Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
            q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
              q = Ideal.span ({a} : Set A) ∧
                (QuasiComplete A 𝔪 ↔
                  ∀ J : Ideal A,
                    WeaklyQuasiComplete (A ⧸ J)
                      (Ideal.map (Ideal.Quotient.mk J) 𝔪)) ∧
                  (WeaklyQuasiComplete (A ⧸ q)
                    (Ideal.map (Ideal.Quotient.mk q) 𝔪) ↔
                      AnalyticallyIrreducible (A ⧸ q)
                        (nodeRing ⧸ Ideal.span ({ι a} : Set nodeRing))) := by
  rcases badQuotient_structured_criteria_source with
    ⟨d, hQuasiCriterion, hDimensionCriterion⟩
  exact
    ⟨d.A, d.instA, d.𝔪, d.ι, d.q, d.a, d.hNoeth, d.hLocal, d.hDomain,
      d.hWeak, d.hBot, d.hqComap, d.hqPrime, d.hqNonzero, d.hqPrincipal,
      hQuasiCriterion, hDimensionCriterion⟩

theorem badQuotient_completion_source :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A)
      (Bhat : Type) (_instBhat : CommRing Bhat)
      (_e : (nodeRing ⧸ Ideal.span ({ι a} : Set nodeRing)) ≃+* Bhat),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        WeaklyQuasiComplete A 𝔪 ∧
          Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
            q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
              q = Ideal.span ({a} : Set A) ∧
                (QuasiComplete A 𝔪 ↔
                  ∀ J : Ideal A,
                    WeaklyQuasiComplete (A ⧸ J)
                      (Ideal.map (Ideal.Quotient.mk J) 𝔪)) ∧
                  (WeaklyQuasiComplete (A ⧸ q)
                    (Ideal.map (Ideal.Quotient.mk q) 𝔪) ↔
                      AnalyticallyIrreducible (A ⧸ q) Bhat) := by
  rcases badQuotient_criteria_source with
    ⟨A, instA, 𝔪, ι, q, a, hNoeth, hLocal, hDomain, hWeak, hBot, hqComap,
      hqPrime, hqNonzero, hqPrincipal, hQuasiCriterion, hDimensionCriterion⟩
  letI := instA
  exact
    ⟨A, instA, 𝔪, ι, q, a,
      nodeRing ⧸ Ideal.span ({ι a} : Set nodeRing), inferInstance,
      RingEquiv.refl (nodeRing ⧸ Ideal.span ({ι a} : Set nodeRing)),
      hNoeth, hLocal, hDomain, hWeak, hBot, hqComap, hqPrime, hqNonzero,
      hqPrincipal, hQuasiCriterion, hDimensionCriterion⟩

theorem badQuotient_completion_not_domain :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A)
      (Bhat : Type) (_instBhat : CommRing Bhat),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        WeaklyQuasiComplete A 𝔪 ∧
          Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
            q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
              q = Ideal.span ({a} : Set A) ∧
                (QuasiComplete A 𝔪 ↔
                  ∀ J : Ideal A,
                    WeaklyQuasiComplete (A ⧸ J)
                      (Ideal.map (Ideal.Quotient.mk J) 𝔪)) ∧
                  (WeaklyQuasiComplete (A ⧸ q)
                    (Ideal.map (Ideal.Quotient.mk q) 𝔪) ↔
                      AnalyticallyIrreducible (A ⧸ q) Bhat) ∧
                      ¬ IsDomain Bhat := by
  rcases badQuotient_completion_source with
    ⟨A, instA, 𝔪, ι, q, a, Bhat, instBhat, e, hNoeth, hLocal, hDomain, hWeak,
      hBot, hqComap, hqPrime, hqNonzero, hqPrincipal, hQuasiCriterion,
      hDimensionCriterion⟩
  letI := instA
  letI := instBhat
  have hExtendedNotPrime :
      ¬ (Ideal.span ({ι a} : Set nodeRing)).IsPrime :=
    extendedPrincipal_not_prime_of_generator_data A ι q a hBot hqComap
      hqNonzero hqPrincipal
  have hCompletionNotDomain : ¬ IsDomain Bhat := by
    intro hBhatDomain
    haveI : IsDomain Bhat := hBhatDomain
    have hQuotientDomain :
        IsDomain (nodeRing ⧸ Ideal.span ({ι a} : Set nodeRing)) :=
      MulEquiv.isDomain Bhat e.toMulEquiv
    exact quotient_not_domain_of_not_prime
      (Ideal.span ({ι a} : Set nodeRing)) hExtendedNotPrime hQuotientDomain
  exact
    ⟨A, instA, 𝔪, ι, q, a, Bhat, instBhat, hNoeth, hLocal, hDomain, hWeak,
      hBot, hqComap, hqPrime, hqNonzero, hqPrincipal, hQuasiCriterion,
      hDimensionCriterion, hCompletionNotDomain⟩

theorem badQuotient_not_weaklyQuasiComplete :
    ∃ (A : Type) (_inst : CommRing A) (𝔪 q : @Ideal A _inst.toSemiring),
      IsNoetherianRing A ∧ IsLocalRing A ∧ WeaklyQuasiComplete A 𝔪 ∧
        (QuasiComplete A 𝔪 ↔
          ∀ J : Ideal A,
            WeaklyQuasiComplete (A ⧸ J)
              (Ideal.map (Ideal.Quotient.mk J) 𝔪)) ∧
          ¬ WeaklyQuasiComplete (A ⧸ q) (Ideal.map (Ideal.Quotient.mk q) 𝔪) := by
  rcases badQuotient_completion_not_domain with
    ⟨A, instA, 𝔪, _ι, q, _a, Bhat, instBhat, hNoeth, hLocal, _hDomain, hWeak,
      _hBot, _hqComap, _hqPrime, _hqNonzero, _hqPrincipal, hQuasiCriterion,
        hDimensionCriterion, hCompletionNotDomain⟩
  letI := instA
  letI := instBhat
  refine ⟨A, instA, 𝔪, q, hNoeth, hLocal, hWeak, hQuasiCriterion, ?_⟩
  intro hQuotientWeak
  exact hCompletionNotDomain
    ((dimensionOne_weaklyQuasiComplete_iff (A ⧸ q) Bhat
      (Ideal.map (Ideal.Quotient.mk q) 𝔪) hDimensionCriterion).1 hQuotientWeak)

theorem counterexampleRing_weak_and_bad_quotient :
    ∃ (A : Type) (_inst : CommRing A),
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ 𝔪 : @Ideal A _inst.toSemiring,
          WeaklyQuasiComplete A 𝔪 ∧ ¬ QuasiComplete A 𝔪 := by
  rcases badQuotient_not_weaklyQuasiComplete with
    ⟨A, instA, 𝔪, q, hNoeth, hLocal, hWeak, hQuasiCriterion, hQuotientNotWeak⟩
  letI := instA
  refine ⟨A, instA, hNoeth, hLocal, 𝔪, hWeak, ?_⟩
  intro hQuasi
  exact hQuotientNotWeak
    ((quasiComplete_iff_all_quotients_weak A 𝔪 hQuasiCriterion).1 hQuasi q)

theorem andersonProblem8a :
    ∃ (A : Type) (_inst : CommRing A),
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ 𝔪 : @Ideal A _inst.toSemiring,
          WeaklyQuasiComplete A 𝔪 ∧ ¬ QuasiComplete A 𝔪 := by
  exact counterexampleRing_weak_and_bad_quotient

end

end TODO
end Run202608192034
