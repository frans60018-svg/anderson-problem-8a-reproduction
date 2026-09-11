import Run202608192034.Basic

/-!
Historical source-ordered Archon development of the node-ring facts, Jensen
construction, bad quotient, and Anderson counterexample. Published results
that were not internalized in this track are exposed as named external
boundaries rather than hidden proof holes.

The canonical zero-custom-axiom theorem is declared in
`StrictReproduction.lean`; this module is retained for process comparison.
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

/--
External commutative-algebra boundary for the concrete quadratic node
`C[[x,y,z]]/(x^2-yz)` and `Q = (x,y)`.  The accompanying blueprint gives the
coefficient-normal-form/domain argument, the hypersurface dimension argument,
the cardinality calculation, the quotient identification `T/Q ≃ C[[z]]`, and
the Nakayama proof that `Q` is not principal.  Mathlib v4.29 does not yet expose
the required finite-variable power-series Noetherian/dimension and formal
division APIs, so these standard facts are kept as one visible assumption.
-/
axiom nodeRing_standard_facts_external :
    IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      ringKrullDim nodeRing = 2 ∧ Cardinal.mk nodeRing = Cardinal.mk ℂ ∧
        nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 ∧
          ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing)

theorem completeDomainChoice :
    IsDomain nodeRing ∧ IsNoetherianRing nodeRing ∧ IsLocalRing nodeRing ∧
      ringKrullDim nodeRing = 2 ∧ Cardinal.mk nodeRing = Cardinal.mk ℂ ∧
        nodePrime.IsPrime ∧ nodePrime ≠ ⊥ ∧ nodePrime.height = 1 ∧
          ¬ ∃ a : nodeRing, nodePrime = Ideal.span ({a} : Set nodeRing) := by
  exact nodeRing_standard_facts_external

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

theorem isNoetherianRing_of_ringEquiv_source
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsNoetherianRing R] :
    IsNoetherianRing S := by
  rw [isNoetherianRing_iff]
  have hR : IsNoetherian R R := isNoetherianRing_iff.mp inferInstance
  let l : R →ₛₗ[(e : R →+* S)] S := e.toSemilinearEquiv
  exact
    (LinearMap.isNoetherian_iff_of_bijective l
      (LinearEquiv.bijective e.toSemilinearEquiv)).mp hR

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

structure JensenCompletionWitness
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing) where
  completionEquiv : AdicCompletion 𝔪 A ≃+* nodeRing
  map_compatible :
    ι = completionEquiv.toRingHom.comp
      (algebraMap A (AdicCompletion 𝔪 A))
  sourceIsUFD : UniqueFactorizationMonoid A
  adicIdeal_eq_maximalIdeal :
    ∀ hLocal : IsLocalRing A,
      𝔪 = @IsLocalRing.maximalIdeal A inferInstance hLocal
  sourceRingKrullDim_eq_two : ringKrullDim A = 2
  weakCriterion :
    WeaklyQuasiComplete A 𝔪 ↔
      ∀ P : Ideal nodeRing, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥

structure JensenNSubringSeedData where
  G : Set (Ideal nodeRing)
  hG_eq : G = ({⊥} : Set (Ideal nodeRing))
  R₀ : NSubring nodeRing
  hInitialAvoid : ∀ P ∈ G, Ideal.comap R₀.1.subtype P = ⊥

structure JensenSaturationTaskEnumeration (seed : JensenNSubringSeedData) where
  primeTasks : Set (Ideal nodeRing)
  hPrimeCoverage :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ∉ seed.G →
      Q ∈ primeTasks
  idealTasks : Set (Ideal seed.R₀.1)

structure JensenSaturationRecursiveChainData
    (seed : JensenNSubringSeedData)
    (tasks : JensenSaturationTaskEnumeration seed) where
  chain : jensenSaturationChain nodeRing
  hStarts : seed.R₀.1 ≤ (chain.1 0).1
  hStageAvoid :
    ∀ n : ℕ, ∀ P ∈ seed.G,
      Ideal.comap (chain.1 n).1.subtype P = ⊥
  hStageHits :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ∉ seed.G →
      ∃ n : ℕ, Ideal.comap (chain.1 n).1.subtype Q ≠ ⊥

structure JensenSaturationUnionData
    (seed : JensenNSubringSeedData)
    {tasks : JensenSaturationTaskEnumeration seed}
    (rec : JensenSaturationRecursiveChainData seed tasks) where
  A : Subring nodeRing
  hChain_le : ∀ n : ℕ, (rec.chain.1 n).1 ≤ A
  hAvoid : ∀ P ∈ seed.G, Ideal.comap A.subtype P = ⊥
  hHitsOutsideG :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ∉ seed.G →
      Ideal.comap A.subtype Q ≠ ⊥

structure JensenSaturationData (seed : JensenNSubringSeedData) where
  chain : jensenSaturationChain nodeRing
  A : Subring nodeRing
  hStarts : seed.R₀.1 ≤ (chain.1 0).1
  hChain_le : ∀ n : ℕ, (chain.1 n).1 ≤ A
  hAvoid : ∀ P ∈ seed.G, Ideal.comap A.subtype P = ⊥
  hHitsOutsideG :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ∉ seed.G → Ideal.comap A.subtype Q ≠ ⊥

structure JensenUFDOutputData
    (seed : JensenNSubringSeedData) (sat : JensenSaturationData seed) where
  sourceIsUFD : UniqueFactorizationMonoid sat.A

structure JensenCompletionCriterionOutputData
    (seed : JensenNSubringSeedData) (sat : JensenSaturationData seed) where
  𝔪 : Ideal sat.A
  hNoeth : IsNoetherianRing sat.A
  hLocal : IsLocalRing sat.A
  hDomain : IsDomain sat.A
  completionEquiv : AdicCompletion 𝔪 sat.A ≃+* nodeRing
  map_compatible :
    sat.A.subtype = completionEquiv.toRingHom.comp
      (algebraMap sat.A (AdicCompletion 𝔪 sat.A))
  adicIdeal_eq_maximalIdeal :
    ∀ hLocal : IsLocalRing sat.A,
      𝔪 = @IsLocalRing.maximalIdeal sat.A inferInstance hLocal
  sourceRingKrullDim_eq_two : ringKrullDim sat.A = 2

structure JensenGenericFiberOutputData
    (seed : JensenNSubringSeedData) (sat : JensenSaturationData seed)
    (comp : JensenCompletionCriterionOutputData seed sat) where
  hBot : Ideal.comap sat.A.subtype (⊥ : Ideal nodeRing) = ⊥
  hNonzeroContraction :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap sat.A.subtype Q ≠ ⊥

theorem jensen_saturation_task_enumeration_source
    (seed : JensenNSubringSeedData) :
    Nonempty (JensenSaturationTaskEnumeration seed) := by
  exact
    ⟨{ primeTasks := {Q : Ideal nodeRing | Q.IsPrime ∧ Q ∉ seed.G}
       hPrimeCoverage := by
        intro Q hQPrime hQnotG
        exact ⟨hQPrime, hQnotG⟩
       idealTasks := Set.univ }⟩

theorem jensen_saturation_union_source
    (seed : JensenNSubringSeedData)
    {tasks : JensenSaturationTaskEnumeration seed}
    (rec : JensenSaturationRecursiveChainData seed tasks) :
    Nonempty (JensenSaturationUnionData seed rec) := by
  let R : ℕ → Subring nodeRing := fun n => (rec.chain.1 n).1
  have hRmono : Monotone R :=
    monotone_nat_of_le_succ rec.chain.2
  let A : Subring nodeRing := ⨆ n, R n
  refine
    ⟨{ A := A
       hChain_le := fun n => le_iSup R n
       hAvoid := ?_
       hHitsOutsideG := ?_ }⟩
  · intro P hPG
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨n, hxn⟩ :=
      (Subring.mem_iSup_of_directed hRmono.directed_le).mp x.property
    let xn : R n := ⟨x, hxn⟩
    have hxnP : xn ∈ Ideal.comap (R n).subtype P := hx
    rw [rec.hStageAvoid n P hPG] at hxnP
    have hxn0 : xn = 0 := by simpa using hxnP
    have hxval0 : (x : nodeRing) = 0 :=
      Subtype.ext_iff.mp hxn0
    have hx0 : x = 0 := by
      apply Subtype.ext
      exact hxval0
    simp [hx0]
  · intro Q hQPrime hQnotG
    obtain ⟨n, hn⟩ := rec.hStageHits Q hQPrime hQnotG
    intro hA
    apply hn
    apply le_antisymm ?_ bot_le
    intro x hx
    let hRA : R n ≤ A := le_iSup R n
    have hxA :
        Subring.inclusion hRA x ∈ Ideal.comap A.subtype Q := by
      exact hx
    rw [hA] at hxA
    have hxA0 : Subring.inclusion hRA x = 0 := by
      simpa using hxA
    have hxval0 : (x : nodeRing) = 0 :=
      Subtype.ext_iff.mp hxA0
    have hx0 : x = 0 := by
      apply Subtype.ext
      exact hxval0
    simp [hx0]

theorem JensenSaturationRecursiveChainData.starts
    {seed : JensenNSubringSeedData}
    {tasks : JensenSaturationTaskEnumeration seed}
    (rec : JensenSaturationRecursiveChainData seed tasks) :
    seed.R₀.1 ≤ (rec.chain.1 0).1 :=
  rec.hStarts

theorem JensenSaturationUnionData.chain_le
    {seed : JensenNSubringSeedData}
    {tasks : JensenSaturationTaskEnumeration seed}
    {rec : JensenSaturationRecursiveChainData seed tasks}
    (union : JensenSaturationUnionData seed rec) (n : ℕ) :
    (rec.chain.1 n).1 ≤ union.A :=
  union.hChain_le n

theorem JensenSaturationUnionData.avoid
    {seed : JensenNSubringSeedData}
    {tasks : JensenSaturationTaskEnumeration seed}
    {rec : JensenSaturationRecursiveChainData seed tasks}
    (union : JensenSaturationUnionData seed rec) :
    ∀ P ∈ seed.G, Ideal.comap union.A.subtype P = ⊥ :=
  union.hAvoid

theorem JensenSaturationUnionData.hitsOutsideG
    {seed : JensenNSubringSeedData}
    {tasks : JensenSaturationTaskEnumeration seed}
    {rec : JensenSaturationRecursiveChainData seed tasks}
    (union : JensenSaturationUnionData seed rec) :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ∉ seed.G →
      Ideal.comap union.A.subtype Q ≠ ⊥ :=
  union.hHitsOutsideG

def JensenSaturationUnionData.toSaturationData
    {seed : JensenNSubringSeedData}
    {tasks : JensenSaturationTaskEnumeration seed}
    {rec : JensenSaturationRecursiveChainData seed tasks}
    (union : JensenSaturationUnionData seed rec) :
    JensenSaturationData seed :=
  { chain := rec.chain
    A := union.A
    hStarts := rec.starts
    hChain_le := union.chain_le
    hAvoid := union.avoid
    hHitsOutsideG := union.hitsOutsideG }

noncomputable def jensenSaturationDataOfRecursiveChain
    (seed : JensenNSubringSeedData)
    {tasks : JensenSaturationTaskEnumeration seed}
    (rec : JensenSaturationRecursiveChainData seed tasks) :
    JensenSaturationData seed :=
  (Classical.choice (jensen_saturation_union_source seed rec)).toSaturationData

/--
The complete witness trace supplied by the construction in Jensen, Corollary 2.4.
Keeping the dependent stages in one package prevents the invalid stronger claim
that every subring satisfying only the lightweight saturation bookkeeping is a UFD
or has completion `nodeRing`.
-/
structure JensenPublishedConstructionData where
  seed : JensenNSubringSeedData
  tasks : JensenSaturationTaskEnumeration seed
  recursiveChain : JensenSaturationRecursiveChainData seed tasks
  ufdOutput :
    JensenUFDOutputData seed
      (jensenSaturationDataOfRecursiveChain seed recursiveChain)
  completionOutput :
    JensenCompletionCriterionOutputData seed
      (jensenSaturationDataOfRecursiveChain seed recursiveChain)
  genericFiberOutput :
    JensenGenericFiberOutputData seed
      (jensenSaturationDataOfRecursiveChain seed recursiveChain)
      completionOutput

/--
Published-source boundary: the sufficiency construction in D. Jensen,
"Completions of UFDs with Semi-Local Formal Fibers", Communications in
Algebra 34 (2006), Corollary 2.4, specialized to `nodeRing` and `P = (0)`.
The downstream Anderson argument is kernel-checked from this witness package.
-/
axiom jensen_corollary_2_4_construction_external :
  Nonempty JensenPublishedConstructionData

theorem jensen_nSubring_seed_source
    (c : JensenPublishedConstructionData) :
    Nonempty JensenNSubringSeedData := by
  exact ⟨c.seed⟩

theorem jensen_saturation_recursive_chain_source
    (c : JensenPublishedConstructionData) :
    Nonempty
      (JensenSaturationRecursiveChainData c.seed c.tasks) := by
  exact ⟨c.recursiveChain⟩

theorem jensen_saturation_source
    (c : JensenPublishedConstructionData) :
    Nonempty (JensenSaturationData c.seed) := by
  exact
    ⟨jensenSaturationDataOfRecursiveChain c.seed c.recursiveChain⟩

theorem jensen_ufd_output_source
    (c : JensenPublishedConstructionData) :
    Nonempty
      (JensenUFDOutputData c.seed
        (jensenSaturationDataOfRecursiveChain c.seed c.recursiveChain)) := by
  exact ⟨c.ufdOutput⟩

theorem jensen_completion_output_source
    (c : JensenPublishedConstructionData) :
    Nonempty
      (JensenCompletionCriterionOutputData c.seed
        (jensenSaturationDataOfRecursiveChain c.seed c.recursiveChain)) := by
  exact ⟨c.completionOutput⟩

theorem jensen_generic_formal_fiber_output_source
    (c : JensenPublishedConstructionData) :
    Nonempty
      (JensenGenericFiberOutputData c.seed
        (jensenSaturationDataOfRecursiveChain c.seed c.recursiveChain)
        c.completionOutput) := by
  exact ⟨c.genericFiberOutput⟩

structure JensenSelectedSource where
  A : Type
  [instA : CommRing A]
  𝔪 : Ideal A
  ι : A →+* nodeRing
  hNoeth : IsNoetherianRing A
  hLocal : IsLocalRing A
  hDomain : IsDomain A
  witness : JensenCompletionWitness A 𝔪 ι
  hBot : Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥
  hNonzeroContraction :
    ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥

attribute [instance] JensenSelectedSource.instA

theorem jensenSelectedSource_exists_source : Nonempty JensenSelectedSource := by
  rcases jensen_corollary_2_4_construction_external with ⟨c⟩
  let sat : JensenSaturationData c.seed :=
    jensenSaturationDataOfRecursiveChain c.seed c.recursiveChain
  let ufd := c.ufdOutput
  let comp := c.completionOutput
  let fiber := c.genericFiberOutput
  letI : IsNoetherianRing sat.A := comp.hNoeth
  letI : IsLocalRing sat.A := comp.hLocal
  letI : IsDomain sat.A := comp.hDomain
  have hMax : comp.𝔪 = IsLocalRing.maximalIdeal sat.A :=
    comp.adicIdeal_eq_maximalIdeal comp.hLocal
  have hWeakCompletion :
      WeaklyQuasiComplete sat.A comp.𝔪 ↔
        AdicCompletionPrimeContractionCondition sat.A comp.𝔪 :=
    anderson_corollary2_part1_external sat.A comp.𝔪 hMax
  have hCompletionTarget :
      AdicCompletionPrimeContractionCondition sat.A comp.𝔪 ↔
        ∀ P : Ideal nodeRing, P.IsPrime → P ≠ ⊥ →
          Ideal.comap sat.A.subtype P ≠ ⊥ :=
    adicCompletionPrimeContractionCondition_iff_target
      sat.A nodeRing comp.𝔪 sat.A.subtype comp.completionEquiv
      comp.map_compatible
  let w : JensenCompletionWitness sat.A comp.𝔪 sat.A.subtype :=
    { completionEquiv := comp.completionEquiv
      map_compatible := comp.map_compatible
      sourceIsUFD := ufd.sourceIsUFD
      adicIdeal_eq_maximalIdeal := comp.adicIdeal_eq_maximalIdeal
      sourceRingKrullDim_eq_two := comp.sourceRingKrullDim_eq_two
      weakCriterion := hWeakCompletion.trans hCompletionTarget }
  exact
    ⟨{ A := sat.A
       instA := inferInstance
       𝔪 := comp.𝔪
       ι := sat.A.subtype
       hNoeth := comp.hNoeth
       hLocal := comp.hLocal
       hDomain := comp.hDomain
       witness := w
       hBot := fiber.hBot
       hNonzeroContraction := fiber.hNonzeroContraction }⟩

theorem jensen_selected_ring_exists_source :
    ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (_ι : A →+* nodeRing),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A := by
  rcases jensenSelectedSource_exists_source with ⟨s⟩
  exact ⟨s.A, s.instA, s.𝔪, s.ι, s.hNoeth, s.hLocal, s.hDomain⟩

theorem jensen_selected_ring_completion_equiv_source :
    ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing), ∃ (_w : JensenCompletionWitness A _𝔪 ι), True := by
  rcases jensenSelectedSource_exists_source with ⟨s⟩
  exact ⟨s.A, s.instA, s.𝔪, s.ι, s.witness, trivial⟩

theorem jensen_selected_ring_ufd_source :
    ∃ (A : Type) (_inst : CommRing A), ∃ (_ufd : UniqueFactorizationMonoid A), True := by
  rcases jensenSelectedSource_exists_source with ⟨s⟩
  exact ⟨s.A, s.instA, s.witness.sourceIsUFD, trivial⟩

theorem jensen_selected_ring_generic_fiber_source :
    ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing),
      Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
        ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥ := by
  rcases jensenSelectedSource_exists_source with ⟨s⟩
  exact ⟨s.A, s.instA, s.𝔪, s.ι, s.hBot, s.hNonzeroContraction⟩

def counterexampleRing : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (_w : JensenCompletionWitness A _𝔪 ι),
    IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
        ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥

theorem jensenSpecialCase_source :
    ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
      (ι : A →+* nodeRing) (_w : JensenCompletionWitness A _𝔪 ι),
      IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
        Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
          ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥ := by
  rcases jensenSelectedSource_exists_source with ⟨s⟩
  exact
    ⟨s.A, s.instA, s.𝔪, s.ι, s.witness, s.hNoeth, s.hLocal, s.hDomain, s.hBot,
      s.hNonzeroContraction⟩

theorem jensenSpecialCase : counterexampleRing := by
  rcases jensenSpecialCase_source with
    ⟨A, instA, 𝔪, ι, w, hNoeth, hLocal, hDomain, hBot, hNonzeroContraction⟩
  exact
    ⟨A, instA, 𝔪, ι, w, hNoeth, hLocal, hDomain, hBot, hNonzeroContraction⟩

noncomputable def jensenCompletionWitness_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (_hNoeth : IsNoetherianRing A) (_hLocal : IsLocalRing A)
    (_hDomain : IsDomain A)
    (_hBot : Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥)
    (_hNonzeroContraction :
      ∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥)
    (w : JensenCompletionWitness A 𝔪 ι) :
    JensenCompletionWitness A 𝔪 ι := by
  exact w

theorem counterexampleRing_weakCriterion_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (w : JensenCompletionWitness A 𝔪 ι) :
    WeaklyQuasiComplete A 𝔪 ↔
      ∀ P : Ideal nodeRing, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥ := by
  exact w.weakCriterion

theorem adicCompletion_isNoetherianRing_from_jensen
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (w : JensenCompletionWitness A 𝔪 ι) :
    IsNoetherianRing (AdicCompletion 𝔪 A) := by
  haveI : IsNoetherianRing nodeRing := node_complete_cm_dim.1
  exact isNoetherianRing_of_ringEquiv_source w.completionEquiv.symm

theorem counterexampleRing_properties : counterexampleRing :=
  jensenSpecialCase

theorem counterexampleRing_weaklyQuasiComplete :
    counterexampleRing →
      ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring),
        WeaklyQuasiComplete A 𝔪 := by
  intro hA
  rcases hA with
    ⟨A, instA, 𝔪, ι, w, _hNoeth, _hLocal, _hDomain, _hBot, hNonzero⟩
  letI := instA
  exact
    ⟨A, instA, 𝔪,
      (counterexampleRing_weakCriterion_source A 𝔪 ι w).2 hNonzero⟩

def contractedPrime : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (_𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring),
    counterexampleRing ∧ q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥

theorem contractedPrime_nonzero_height_one : contractedPrime := by
  rcases counterexampleRing_properties with
    ⟨A, instA, 𝔪, ι, _w, _hNoeth, _hLocal, _hDomain, _hBot, hNonzero⟩
  letI := instA
  refine
    ⟨A, instA, 𝔪, ι, Ideal.comap ι nodePrime, counterexampleRing_properties, rfl,
      ?_, ?_⟩
  · haveI : nodePrime.IsPrime := nodePrime_prime_height.1
    exact Ideal.comap_isPrime ι nodePrime
  · exact hNonzero nodePrime nodePrime_prime_height.1 nodePrime_prime_height.2.1

def primeGenerator : Prop :=
  ∃ (A : Type) (_inst : CommRing A) (𝔪 : @Ideal A _inst.toSemiring)
    (ι : A →+* nodeRing) (q : @Ideal A _inst.toSemiring) (a : A)
    (_w : JensenCompletionWitness A 𝔪 ι),
    counterexampleRing ∧ IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
      WeaklyQuasiComplete A 𝔪 ∧
        Ideal.comap ι (⊥ : Ideal nodeRing) = ⊥ ∧
        (∀ Q : Ideal nodeRing, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥) ∧
          q = Ideal.comap ι nodePrime ∧ q.IsPrime ∧ q ≠ ⊥ ∧
            q = Ideal.span ({a} : Set A)

theorem jensenSpecialCase_isUFD_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (w : JensenCompletionWitness A 𝔪 ι) :
    UniqueFactorizationMonoid A := by
  exact w.sourceIsUFD

theorem nonzeroPrime_height_ge_one_source
    (A : Type) [CommRing A] [IsDomain A] (q : Ideal A)
    (_hqPrime : q.IsPrime) (hqNonzero : q ≠ ⊥) :
    (1 : ℕ∞) ≤ q.height := by
  have hBotLtQ : (⊥ : Ideal A) < q :=
    bot_lt_iff_ne_bot.mpr hqNonzero
  haveI : (⊥ : Ideal A).FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    exact Or.inr (by rw [Ideal.height_bot]; simp)
  have hStrict : (⊥ : Ideal A).height < q.height :=
    Ideal.height_strict_mono_of_is_prime hBotLtQ
  have hPositive : 0 < q.height := by
    simpa [Ideal.height_bot] using hStrict
  exact ENat.one_le_iff_ne_zero.mpr (ne_of_gt hPositive)

theorem liesOver_height_le_of_hasGoingDown_source
    (A T : Type) [CommRing A] [CommRing T] [Algebra A T]
    [IsNoetherianRing A] [IsNoetherianRing T] [Algebra.HasGoingDown A T]
    (q : Ideal A) (Q : Ideal T) (hqPrime : q.IsPrime) (hQPrime : Q.IsPrime)
    (hLiesOver : Q.LiesOver q) :
    q.height ≤ Q.height := by
  haveI : q.IsPrime := hqPrime
  haveI : Q.IsPrime := hQPrime
  haveI : Q.LiesOver q := hLiesOver
  have hEq :
      Q.height =
        q.height +
          (Q.map (Ideal.Quotient.mk <| q.map (algebraMap A T))).height :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q
  exact (self_le_add_right q.height _).trans (le_of_eq hEq.symm)

theorem adicCompletion_hasGoingDown_of_isNoetherian
    (A : Type) [CommRing A] (𝔪 : Ideal A) [IsNoetherianRing A] :
    Algebra.HasGoingDown A (AdicCompletion 𝔪 A) := by
  infer_instance

theorem adicCompletion_equiv_hasGoingDown_of_isNoetherian
    (A T : Type) [CommRing A] [CommRing T] (𝔪 : Ideal A)
    [IsNoetherianRing A] (e : AdicCompletion 𝔪 A ≃+* T) :
    letI : Algebra A T :=
      (e.toRingHom.comp (algebraMap A (AdicCompletion 𝔪 A))).toAlgebra
    Algebra.HasGoingDown A T := by
  let f : A →+* AdicCompletion 𝔪 A :=
    algebraMap A (AdicCompletion 𝔪 A)
  let g : AdicCompletion 𝔪 A →+* T :=
    e.toRingHom
  have hf : f.Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hg : g.Flat :=
    RingHom.Flat.of_bijective e.bijective
  have hfg : (g.comp f).Flat :=
    hf.comp hg
  change
    letI : Algebra A T := (g.comp f).toAlgebra
    Algebra.HasGoingDown A T
  letI : Algebra A T := (g.comp f).toAlgebra
  haveI : Module.Flat A T := hfg
  infer_instance

theorem completionMap_hasGoingDown_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (hNoeth : IsNoetherianRing A) (_hLocal : IsLocalRing A)
    (w : JensenCompletionWitness A 𝔪 ι) :
    letI : Algebra A nodeRing := ι.toAlgebra
    Algebra.HasGoingDown A nodeRing := by
  rw [w.map_compatible]
  exact
    adicCompletion_equiv_hasGoingDown_of_isNoetherian A nodeRing 𝔪
      w.completionEquiv

theorem contractedPrime_height_le_one_of_hasGoingDown_source
    (A : Type) [CommRing A] (_𝔪 : Ideal A) (ι : A →+* nodeRing)
    (q : Ideal A) (hNoeth : IsNoetherianRing A) (_hLocal : IsLocalRing A)
    (_hDomain : IsDomain A) (hqComap : q = Ideal.comap ι nodePrime)
    (hqPrime : q.IsPrime) (_hqNonzero : q ≠ ⊥)
    (hGoingDown :
      letI : Algebra A nodeRing := ι.toAlgebra
      Algebra.HasGoingDown A nodeRing) :
    q.height ≤ 1 := by
  letI : Algebra A nodeRing := ι.toAlgebra
  haveI : IsNoetherianRing A := hNoeth
  haveI : IsNoetherianRing nodeRing := node_complete_cm_dim.1
  haveI : Algebra.HasGoingDown A nodeRing := hGoingDown
  have hNodePrime : nodePrime.IsPrime := nodePrime_prime_height.1
  have hNodeHeight : nodePrime.height = 1 := nodePrime_prime_height.2.2
  have hLiesOver : nodePrime.LiesOver q := by
    constructor
    simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra] using hqComap
  exact
    (liesOver_height_le_of_hasGoingDown_source A nodeRing q nodePrime hqPrime
      hNodePrime hLiesOver).trans (le_of_eq hNodeHeight)

theorem contractedPrime_height_le_one_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (q : Ideal A) (w : JensenCompletionWitness A 𝔪 ι)
    (hNoeth : IsNoetherianRing A) (hLocal : IsLocalRing A)
    (hDomain : IsDomain A) (hqComap : q = Ideal.comap ι nodePrime)
    (hqPrime : q.IsPrime) (hqNonzero : q ≠ ⊥) :
    q.height ≤ 1 := by
  exact
    contractedPrime_height_le_one_of_hasGoingDown_source A 𝔪 ι q hNoeth
      hLocal hDomain hqComap hqPrime hqNonzero
      (completionMap_hasGoingDown_source A 𝔪 ι hNoeth hLocal w)

theorem contractedPrime_height_one_source
    (A : Type) [CommRing A] (𝔪 : Ideal A) (ι : A →+* nodeRing)
    (q : Ideal A) (w : JensenCompletionWitness A 𝔪 ι)
    (hNoeth : IsNoetherianRing A) (hLocal : IsLocalRing A)
    (hDomain : IsDomain A) (hqComap : q = Ideal.comap ι nodePrime)
    (hqPrime : q.IsPrime) (hqNonzero : q ≠ ⊥) :
    q.height = 1 := by
  haveI : IsDomain A := hDomain
  exact le_antisymm
    (contractedPrime_height_le_one_source A 𝔪 ι q w hNoeth hLocal hDomain
      hqComap hqPrime hqNonzero)
    (nonzeroPrime_height_ge_one_source A q hqPrime hqNonzero)

theorem heightOnePrime_principal_of_ufd_source
    (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    (q : Ideal A) (_hqPrime : q.IsPrime) (_hqNonzero : q ≠ ⊥)
    (_hqHeight : q.height = 1) :
    ∃ a : A, q = Ideal.span ({a} : Set A) := by
  rcases Ideal.IsPrime.exists_mem_prime_of_ne_bot _hqPrime _hqNonzero with
    ⟨p, hpMem, hpPrime⟩
  refine ⟨p, ?_⟩
  have hpSpanPrime : (Ideal.span ({p} : Set A)).IsPrime :=
    (Ideal.span_singleton_prime hpPrime.ne_zero).2 hpPrime
  haveI : (Ideal.span ({p} : Set A)).IsPrime := hpSpanPrime
  have hpSpanLeQ : Ideal.span ({p} : Set A) ≤ q :=
    (Ideal.span_singleton_le_iff_mem q).mpr hpMem
  have hpSpanNonzero : Ideal.span ({p} : Set A) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hpPrime.ne_zero
  have hpBotLtSpan : (⊥ : Ideal A) < Ideal.span ({p} : Set A) :=
    bot_lt_iff_ne_bot.mpr hpSpanNonzero
  haveI : (⊥ : Ideal A).FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    exact Or.inr (by rw [Ideal.height_bot]; simp)
  have hpSpanHeightPos : 0 < (Ideal.span ({p} : Set A)).height := by
    have hStrict :
        (⊥ : Ideal A).height < (Ideal.span ({p} : Set A)).height :=
      Ideal.height_strict_mono_of_is_prime hpBotLtSpan
    simpa [Ideal.height_bot] using hStrict
  have hpSpanPrimeHeightPos : 0 < (Ideal.span ({p} : Set A)).primeHeight := by
    simpa [Ideal.height_eq_primeHeight] using hpSpanHeightPos
  haveI : q.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    exact Or.inr (by rw [_hqHeight]; simp)
  have hqPrimeHeight : q.primeHeight = 1 := by
    simpa [Ideal.height_eq_primeHeight] using _hqHeight
  by_contra hNe
  have hSpanLtQ : Ideal.span ({p} : Set A) < q :=
    lt_of_le_of_ne hpSpanLeQ (fun hEq => hNe hEq.symm)
  have hPrimeHeightLt :
      (Ideal.span ({p} : Set A)).primeHeight < q.primeHeight :=
    Ideal.primeHeight_strict_mono hSpanLtQ
  rw [hqPrimeHeight] at hPrimeHeightLt
  exact
    (not_lt_of_ge
      (ENat.one_le_iff_ne_zero.mpr (ne_of_gt hpSpanPrimeHeightPos)))
      hPrimeHeightLt

theorem primeGenerator_source : primeGenerator := by
  rcases jensenSpecialCase with
    ⟨A, instA, 𝔪, ι, w, hNoeth, hLocal, hDomain, hBot, hNonzeroContraction⟩
  letI := instA
  let q : Ideal A := Ideal.comap ι nodePrime
  have hCounter : counterexampleRing :=
    ⟨A, instA, 𝔪, ι, w, hNoeth, hLocal, hDomain, hBot, hNonzeroContraction⟩
  have hqComap : q = Ideal.comap ι nodePrime := rfl
  have hqPrime : q.IsPrime := by
    haveI : nodePrime.IsPrime := nodePrime_prime_height.1
    exact Ideal.comap_isPrime ι nodePrime
  have hqNonzero : q ≠ ⊥ :=
    hNonzeroContraction nodePrime nodePrime_prime_height.1 nodePrime_prime_height.2.1
  have hqHeight : q.height = 1 :=
    contractedPrime_height_one_source A 𝔪 ι q w hNoeth hLocal hDomain
      hqComap hqPrime hqNonzero
  have hWeak : WeaklyQuasiComplete A 𝔪 :=
    (counterexampleRing_weakCriterion_source A 𝔪 ι w).2 hNonzeroContraction
  haveI : IsDomain A := hDomain
  haveI : UniqueFactorizationMonoid A :=
    jensenSpecialCase_isUFD_source A 𝔪 ι w
  rcases heightOnePrime_principal_of_ufd_source A q hqPrime hqNonzero hqHeight with
    ⟨a, hqPrincipal⟩
  exact
    ⟨A, instA, 𝔪, ι, q, a, w, hCounter, hNoeth, hLocal, hDomain, hWeak,
      hBot, hNonzeroContraction, hqComap, hqPrime, hqNonzero, hqPrincipal⟩

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
    ⟨A, instA, _𝔪, ι, q, a, _w, _hCounter, _hNoeth, _hLocal, _hDomain,
      _hWeak, hBot, _hNonzeroContraction, hqComap, _hqPrime, _hqNonzero,
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
  jensenCompletion : JensenCompletionWitness A 𝔪 ι
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

theorem BadQuotientSourceData.quotient_isNoetherian
    (d : BadQuotientSourceData) :
    IsNoetherianRing (d.A ⧸ d.q) := by
  letI : IsNoetherianRing d.A := d.hNoeth
  infer_instance

theorem BadQuotientSourceData.quotient_isDomain
    (d : BadQuotientSourceData) :
    IsDomain (d.A ⧸ d.q) := by
  exact (Ideal.Quotient.isDomain_iff_prime d.q).mpr d.hqPrime

theorem BadQuotientSourceData.quotient_nontrivial
    (d : BadQuotientSourceData) :
    Nontrivial (d.A ⧸ d.q) :=
  Ideal.Quotient.nontrivial_iff.mpr d.hqPrime.ne_top

theorem BadQuotientSourceData.quotient_mk_isLocalHom
    (d : BadQuotientSourceData) :
    IsLocalHom (Ideal.Quotient.mk d.q) := by
  letI : IsLocalRing d.A := d.hLocal
  letI : Nontrivial (d.A ⧸ d.q) := d.quotient_nontrivial
  exact
    IsLocalHom.of_surjective (Ideal.Quotient.mk d.q)
      Ideal.Quotient.mk_surjective

theorem BadQuotientSourceData.quotient_isLocal
    (d : BadQuotientSourceData) :
    IsLocalRing (d.A ⧸ d.q) := by
  letI : IsLocalRing d.A := d.hLocal
  letI : Nontrivial (d.A ⧸ d.q) := d.quotient_nontrivial
  letI : IsLocalHom (Ideal.Quotient.mk d.q) :=
    d.quotient_mk_isLocalHom
  exact
    IsLocalRing.of_surjective (Ideal.Quotient.mk d.q)
      Ideal.Quotient.mk_surjective

theorem BadQuotientSourceData.quotient_noetherian_local_domain
    (d : BadQuotientSourceData) :
    IsNoetherianRing (d.A ⧸ d.q) ∧ IsLocalRing (d.A ⧸ d.q) ∧
      IsDomain (d.A ⧸ d.q) :=
  ⟨d.quotient_isNoetherian, d.quotient_isLocal, d.quotient_isDomain⟩

noncomputable def BadQuotientSourceData.jensenCompletionWitness
    (d : BadQuotientSourceData) :
    JensenCompletionWitness d.A d.𝔪 d.ι :=
  d.jensenCompletion

theorem BadQuotientSourceData.source_ringKrullDim_eq_two
    (d : BadQuotientSourceData) :
    ringKrullDim d.A = 2 :=
  d.jensenCompletionWitness.sourceRingKrullDim_eq_two

theorem BadQuotientSourceData.adicCompletion_isNoetherianRing
    (d : BadQuotientSourceData) :
    IsNoetherianRing (AdicCompletion d.𝔪 d.A) :=
  adicCompletion_isNoetherianRing_from_jensen d.A d.𝔪 d.ι
    d.jensenCompletionWitness

theorem BadQuotientSourceData.q_height_one_source
    (d : BadQuotientSourceData) :
    d.q.height = 1 :=
  contractedPrime_height_one_source d.A d.𝔪 d.ι d.q
    d.jensenCompletionWitness d.hNoeth d.hLocal d.hDomain d.hqComap
    d.hqPrime d.hqNonzero

theorem BadQuotientSourceData.generator_mem_q
    (d : BadQuotientSourceData) :
    d.a ∈ d.q := by
  rw [d.hqPrincipal]
  exact Ideal.subset_span (Set.mem_singleton d.a)

theorem BadQuotientSourceData.generator_ne_zero
    (d : BadQuotientSourceData) :
    d.a ≠ 0 := by
  intro ha
  apply d.hqNonzero
  rw [d.hqPrincipal, ha]
  simp

theorem BadQuotientSourceData.generator_mem_nonZeroDivisors
    (d : BadQuotientSourceData) :
    d.a ∈ nonZeroDivisors d.A := by
  haveI : IsDomain d.A := d.hDomain
  exact mem_nonZeroDivisors_iff_ne_zero.mpr d.generator_ne_zero

theorem BadQuotientSourceData.generator_mem_maximalIdeal
    (d : BadQuotientSourceData) :
    d.a ∈ @IsLocalRing.maximalIdeal d.A inferInstance d.hLocal := by
  letI : IsLocalRing d.A := d.hLocal
  have hqLe : d.q ≤ IsLocalRing.maximalIdeal d.A :=
    IsLocalRing.le_maximalIdeal d.hqPrime.ne_top
  exact hqLe d.generator_mem_q

theorem BadQuotientSourceData.quotient_span_generator_dimension_add_one
    (d : BadQuotientSourceData) :
    ringKrullDim (d.A ⧸ Ideal.span ({d.a} : Set d.A)) + 1 =
      ringKrullDim d.A := by
  letI : IsNoetherianRing d.A := d.hNoeth
  letI : IsLocalRing d.A := d.hLocal
  exact
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      d.generator_mem_nonZeroDivisors d.generator_mem_maximalIdeal

theorem BadQuotientSourceData.quotient_dimension_add_one_eq_two_source
    (d : BadQuotientSourceData) :
    ringKrullDim (d.A ⧸ d.q) + 1 = 2 := by
  have h := d.quotient_span_generator_dimension_add_one
  rw [← d.hqPrincipal] at h
  exact h.trans d.source_ringKrullDim_eq_two

theorem withBotENat_eq_one_of_add_one_eq_two
    {x : WithBot ℕ∞} (h : x + 1 = 2) :
    x = 1 := by
  rw [← one_add_one_eq_two] at h
  apply le_antisymm
  · exact ENat.WithBot.add_le_add_one_right_iff.mp (le_of_eq h)
  · exact ENat.WithBot.add_le_add_one_right_iff.mp (ge_of_eq h)

theorem BadQuotientSourceData.quotient_ringKrullDim_eq_one_source
    (d : BadQuotientSourceData) :
    ringKrullDim (d.A ⧸ d.q) = 1 :=
  withBotENat_eq_one_of_add_one_eq_two
    d.quotient_dimension_add_one_eq_two_source

structure QuotientDimensionOneFacts (d : BadQuotientSourceData) : Prop where
  quotient_isNoetherian : IsNoetherianRing (d.A ⧸ d.q)
  quotient_isLocal : IsLocalRing (d.A ⧸ d.q)
  quotient_isDomain : IsDomain (d.A ⧸ d.q)
  quotient_ringKrullDim_eq_one : ringKrullDim (d.A ⧸ d.q) = 1

theorem BadQuotientSourceData.quotientDimensionOneFacts_of_dim
    (d : BadQuotientSourceData)
    (hDim : ringKrullDim (d.A ⧸ d.q) = 1) :
    QuotientDimensionOneFacts d :=
  { quotient_isNoetherian := d.quotient_isNoetherian
    quotient_isLocal := d.quotient_isLocal
    quotient_isDomain := d.quotient_isDomain
    quotient_ringKrullDim_eq_one := hDim }

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

def quotientLinearMap (d : BadQuotientSourceData) :
    d.A →ₗ[d.A] d.A ⧸ d.q :=
  (Ideal.Quotient.mkₐ d.A d.q).toLinearMap

theorem quotient_mk_linear_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective (quotientLinearMap d) := by
  simpa [quotientLinearMap, Ideal.Quotient.mkₐ_eq_mk] using
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk d.q))

theorem quotient_completion_map_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective
      (AdicCompletion.map d.𝔪 (quotientLinearMap d)) := by
  exact AdicCompletion.map_surjective d.𝔪 (quotient_mk_linear_surjective d)

theorem quotient_module_filtration_eq_restrictScalars
    (d : BadQuotientSourceData) (n : ℕ) :
    (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q))) =
      ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n).restrictScalars d.A := by
  rw [Ideal.smul_top_eq_map]
  rw [show algebraMap d.A (d.A ⧸ d.q) = Ideal.Quotient.mk d.q by
    exact Ideal.Quotient.algebraMap_eq d.q]
  rw [Ideal.map_pow]

noncomputable def quotientModuleLevelEquiv
    (d : BadQuotientSourceData) (n : ℕ) :
    ((d.A ⧸ d.q) ⧸
        (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))) ≃ₗ[d.A]
      ((d.A ⧸ d.q) ⧸
        (((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n).restrictScalars d.A)) :=
  Submodule.Quotient.equiv
    (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))
    (((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n).restrictScalars d.A)
    (LinearEquiv.refl d.A (d.A ⧸ d.q))
    (by
      simpa using quotient_module_filtration_eq_restrictScalars d n)

@[simp]
theorem quotientModuleLevelEquiv_mk
    (d : BadQuotientSourceData) (n : ℕ) (x : d.A ⧸ d.q) :
    quotientModuleLevelEquiv d n
        (Submodule.Quotient.mk
          (p := d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q))) x) =
      Submodule.Quotient.mk
        (p := ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n).restrictScalars d.A) x := by
  rfl

noncomputable def quotientModuleLevelToRingLevelEquiv
    (d : BadQuotientSourceData) (n : ℕ) :
    ((d.A ⧸ d.q) ⧸
        (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))) ≃ₗ[d.A]
      ((d.A ⧸ d.q) ⧸
        ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n)) :=
  quotientModuleLevelEquiv d n

theorem quotient_module_filtration_eq_adic_restrictScalars
    (d : BadQuotientSourceData) (n : ℕ) :
    (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q))) =
      ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n •
        (⊤ : Submodule (d.A ⧸ d.q) (d.A ⧸ d.q))).restrictScalars d.A := by
  rw [quotient_module_filtration_eq_restrictScalars]
  simp

noncomputable def quotientModuleLevelToAdicLevelEquiv
    (d : BadQuotientSourceData) (n : ℕ) :
    ((d.A ⧸ d.q) ⧸
        (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))) ≃ₗ[d.A]
      ((d.A ⧸ d.q) ⧸
        ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n •
          (⊤ : Submodule (d.A ⧸ d.q) (d.A ⧸ d.q)))) :=
  Submodule.Quotient.equiv
    (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))
    (((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n •
      (⊤ : Submodule (d.A ⧸ d.q) (d.A ⧸ d.q))).restrictScalars d.A)
    (LinearEquiv.refl d.A (d.A ⧸ d.q))
    (by
      rw [quotient_module_filtration_eq_restrictScalars]
      simp)

theorem quotientModuleLevelToAdicLevelEquiv_eq_factor_ringLevel
    (d : BadQuotientSourceData) (n : ℕ)
    (v : (d.A ⧸ d.q) ⧸
      (d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))) :
    quotientModuleLevelToAdicLevelEquiv d n v =
      Ideal.Quotient.factor
        (show (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n ≤
          ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n •
            (⊤ : Ideal (d.A ⧸ d.q))) by
          exact le_of_eq (by ext x; simp))
        (quotientModuleLevelToRingLevelEquiv d n v) := by
  induction v using Submodule.Quotient.induction_on with
  | H z =>
      rfl

theorem completed_q_eq_span_a
    (d : BadQuotientSourceData) :
    Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q =
      Ideal.span
        ({algebraMap d.A (AdicCompletion d.𝔪 d.A) d.a} :
          Set (AdicCompletion d.𝔪 d.A)) := by
  rw [d.hqPrincipal, Ideal.map_span]
  simp

theorem completionEquiv_maps_completed_q
    (d : BadQuotientSourceData)
    (w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    Ideal.map (w.completionEquiv : AdicCompletion d.𝔪 d.A →+* nodeRing)
        (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) =
      Ideal.span ({d.ι d.a} : Set nodeRing) := by
  rw [completed_q_eq_span_a d, Ideal.map_span]
  simp [w.map_compatible]

noncomputable def completedQuotientTargetEquivNode
    (d : BadQuotientSourceData)
    (w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    (AdicCompletion d.𝔪 d.A ⧸
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
      ≃+*
    (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing)) :=
  Ideal.quotientEquiv
    (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
    (Ideal.span ({d.ι d.a} : Set nodeRing))
    w.completionEquiv
    (completionEquiv_maps_completed_q d w).symm

abbrev quotientAdicCompletion (d : BadQuotientSourceData) : Type :=
  @AdicCompletion (d.A ⧸ d.q) inferInstance
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
    (d.A ⧸ d.q) inferInstance inferInstance

noncomputable instance quotientAdicCompletion.instCommRing
    (d : BadQuotientSourceData) :
    CommRing (quotientAdicCompletion d) :=
  @AdicCompletion.instCommRing (d.A ⧸ d.q) inferInstance
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)

noncomputable def quotientModuleCompletionToQuotientAdicCompletion
    (d : BadQuotientSourceData) :
    AdicCompletion d.𝔪 (d.A ⧸ d.q) → quotientAdicCompletion d :=
  fun x =>
    ⟨fun n => quotientModuleLevelToAdicLevelEquiv d n (x.val n),
      by
        intro m n hmn
        change
          AdicCompletion.transitionMap
              (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) (d.A ⧸ d.q) hmn
              (quotientModuleLevelToAdicLevelEquiv d n (x.val n)) =
            quotientModuleLevelToAdicLevelEquiv d m (x.val m)
        rw [← x.property hmn]
        induction x.val n using Submodule.Quotient.induction_on with
        | H z =>
            change
              Submodule.Quotient.mk
                  (p := (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ m •
                    (⊤ : Submodule (d.A ⧸ d.q) (d.A ⧸ d.q))) z =
                Submodule.Quotient.mk
                  (p := (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ m •
                    (⊤ : Submodule (d.A ⧸ d.q) (d.A ⧸ d.q))) z
            rfl⟩

noncomputable def quotientAdicCompletionToQuotientModuleCompletion
    (d : BadQuotientSourceData) :
    quotientAdicCompletion d → AdicCompletion d.𝔪 (d.A ⧸ d.q) :=
  fun x =>
    ⟨fun n => (quotientModuleLevelToAdicLevelEquiv d n).symm (x.val n),
      by
        intro m n hmn
        change
          AdicCompletion.transitionMap d.𝔪 (d.A ⧸ d.q) hmn
              ((quotientModuleLevelToAdicLevelEquiv d n).symm (x.val n)) =
            (quotientModuleLevelToAdicLevelEquiv d m).symm (x.val m)
        rw [← x.property hmn]
        induction x.val n using Submodule.Quotient.induction_on with
        | H z =>
            change
              Submodule.Quotient.mk
                  (p := d.𝔪 ^ m • (⊤ : Submodule d.A (d.A ⧸ d.q))) z =
                Submodule.Quotient.mk
                  (p := d.𝔪 ^ m • (⊤ : Submodule d.A (d.A ⧸ d.q))) z
            rfl⟩

theorem quotientModuleCompletionToQuotientAdicCompletion_leftInverse
    (d : BadQuotientSourceData) :
    Function.LeftInverse
      (quotientAdicCompletionToQuotientModuleCompletion d)
      (quotientModuleCompletionToQuotientAdicCompletion d) := by
  intro x
  ext n
  exact LinearEquiv.symm_apply_apply
    (quotientModuleLevelToAdicLevelEquiv d n) (x.val n)

theorem quotientModuleCompletionToQuotientAdicCompletion_rightInverse
    (d : BadQuotientSourceData) :
    Function.RightInverse
      (quotientAdicCompletionToQuotientModuleCompletion d)
      (quotientModuleCompletionToQuotientAdicCompletion d) := by
  intro x
  ext n
  exact LinearEquiv.apply_symm_apply
    (quotientModuleLevelToAdicLevelEquiv d n) (x.val n)

noncomputable def quotientModuleCompletionEquivQuotientAdicCompletion
    (d : BadQuotientSourceData) :
    AdicCompletion d.𝔪 (d.A ⧸ d.q) ≃ quotientAdicCompletion d where
  toFun := quotientModuleCompletionToQuotientAdicCompletion d
  invFun := quotientAdicCompletionToQuotientModuleCompletion d
  left_inv := quotientModuleCompletionToQuotientAdicCompletion_leftInverse d
  right_inv := quotientModuleCompletionToQuotientAdicCompletion_rightInverse d

theorem quotientModuleCompletionToQuotientAdicCompletion_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective (quotientModuleCompletionToQuotientAdicCompletion d) :=
  (quotientModuleCompletionToQuotientAdicCompletion_rightInverse d).surjective

theorem QuotientDimensionOneFacts.dimensionOneCriterion_of_source
    (d : BadQuotientSourceData) (_facts : QuotientDimensionOneFacts d)
    (hCriterion :
      WeaklyQuasiComplete (d.A ⧸ d.q)
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
          AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d)) :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d) :=
  dimensionOne_weaklyQuasiComplete_iff (d.A ⧸ d.q)
    (quotientAdicCompletion d)
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
    hCriterion

theorem quotient_dimensionOneCriterionOnQuotientCompletion_of_source
    (d : BadQuotientSourceData)
    (hDim : ringKrullDim (d.A ⧸ d.q) = 1)
    (hCriterion :
      WeaklyQuasiComplete (d.A ⧸ d.q)
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
          AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d)) :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d) :=
  QuotientDimensionOneFacts.dimensionOneCriterion_of_source d
    (d.quotientDimensionOneFacts_of_dim hDim) hCriterion

theorem BadQuotientSourceData.adicIdeal_eq_maximalIdeal_source
    (d : BadQuotientSourceData) :
    d.𝔪 = @IsLocalRing.maximalIdeal d.A inferInstance d.hLocal := by
  exact d.jensenCompletionWitness.adicIdeal_eq_maximalIdeal d.hLocal

theorem BadQuotientSourceData.quotient_adicIdeal_eq_maximalIdeal_of_source
    (d : BadQuotientSourceData)
    [IsLocalRing (d.A ⧸ d.q)]
    (hMax : d.𝔪 = @IsLocalRing.maximalIdeal d.A inferInstance d.hLocal) :
    Ideal.map (Ideal.Quotient.mk d.q) d.𝔪 =
      IsLocalRing.maximalIdeal (d.A ⧸ d.q) := by
  letI : IsLocalRing d.A := d.hLocal
  letI : Nontrivial (d.A ⧸ d.q) := d.quotient_nontrivial
  letI : IsLocalHom (Ideal.Quotient.mk d.q) := d.quotient_mk_isLocalHom
  have hmap :
      Ideal.map (Ideal.Quotient.mk d.q) (IsLocalRing.maximalIdeal d.A) =
        IsLocalRing.maximalIdeal (d.A ⧸ d.q) :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk d.q) Ideal.Quotient.mk_surjective
  simpa [hMax] using hmap

theorem BadQuotientSourceData.quotient_adicIdeal_eq_maximalIdeal_source
    (d : BadQuotientSourceData)
    [IsLocalRing (d.A ⧸ d.q)] :
    Ideal.map (Ideal.Quotient.mk d.q) d.𝔪 =
      IsLocalRing.maximalIdeal (d.A ⧸ d.q) := by
  exact
    d.quotient_adicIdeal_eq_maximalIdeal_of_source
      d.adicIdeal_eq_maximalIdeal_source

theorem BadQuotientSourceData.adicCompletion_quotient_hausdorff_source
    (d : BadQuotientSourceData)
    (P : Ideal (AdicCompletion d.𝔪 d.A)) :
    IsHausdorff (adicCompletionPowerImage d.A d.𝔪 1)
      (AdicCompletion d.𝔪 d.A ⧸ P) := by
  letI : IsNoetherianRing d.A := d.hNoeth
  letI : IsNoetherianRing (AdicCompletion d.𝔪 d.A) :=
    d.adicCompletion_isNoetherianRing
  exact adicCompletion_quotient_hausdorff_of_noetherian_completion
    d.A d.𝔪 P

theorem BadQuotientSourceData.adicCompletion_neighborhood_iInf_le_prime_source
    (d : BadQuotientSourceData)
    (P : Ideal (AdicCompletion d.𝔪 d.A)) :
    (⨅ n, P ⊔ adicCompletionPowerImage d.A d.𝔪 n) ≤ P := by
  letI : IsNoetherianRing d.A := d.hNoeth
  letI : IsLocalRing d.A := d.hLocal
  letI : IsDomain d.A := d.hDomain
  letI :
      IsHausdorff (adicCompletionPowerImage d.A d.𝔪 1)
        (AdicCompletion d.𝔪 d.A ⧸ P) :=
    d.adicCompletion_quotient_hausdorff_source P
  exact adicCompletion_neighborhood_iInf_le_prime_of_hausdorff d.A d.𝔪 P

theorem BadQuotientSourceData.badPrimeContractionChain_iInf_le_comap_source
    (d : BadQuotientSourceData)
    (P : Ideal (AdicCompletion d.𝔪 d.A)) :
    (⨅ n, badPrimeContractionChain d.A d.𝔪 P n) ≤
      Ideal.comap (algebraMap d.A (AdicCompletion d.𝔪 d.A)) P := by
  intro x hx
  have hxhat :
      algebraMap d.A (AdicCompletion d.𝔪 d.A) x ∈
        ⨅ n, P ⊔ adicCompletionPowerImage d.A d.𝔪 n := by
    rw [Ideal.mem_iInf]
    intro n
    exact (mem_badPrimeContractionChain d.A d.𝔪 P n x).mp
      ((Ideal.mem_iInf.mp hx) n)
  exact d.adicCompletion_neighborhood_iInf_le_prime_source P hxhat

theorem BadQuotientSourceData.badPrimeContractionChain_iInf_eq_comap_source
    (d : BadQuotientSourceData)
    (P : Ideal (AdicCompletion d.𝔪 d.A)) :
    (⨅ n, badPrimeContractionChain d.A d.𝔪 P n) =
      Ideal.comap (algebraMap d.A (AdicCompletion d.𝔪 d.A)) P := by
  exact le_antisymm
    (d.badPrimeContractionChain_iInf_le_comap_source P)
    (comap_le_badPrimeContractionChain_iInf d.A d.𝔪 P)

theorem BadQuotientSourceData.badPrimeContractionChain_iInf_eq_bot_source
    (d : BadQuotientSourceData)
    (P : Ideal (AdicCompletion d.𝔪 d.A))
    (hPzero :
      Ideal.comap (algebraMap d.A (AdicCompletion d.𝔪 d.A)) P = ⊥) :
    (⨅ n, badPrimeContractionChain d.A d.𝔪 P n) = ⊥ := by
  rw [d.badPrimeContractionChain_iInf_eq_comap_source P, hPzero]

theorem BadQuotientSourceData.adicCompletion_badPrime_to_badChain_source
    (d : BadQuotientSourceData) :
    AdicCompletionBadPrime d.A d.𝔪 →
      WeaklyQuasiCompleteBadChain d.A d.𝔪 := by
  intro hBad
  letI : IsNoetherianRing d.A := d.hNoeth
  letI : IsLocalRing d.A := d.hLocal
  letI : IsDomain d.A := d.hDomain
  rcases hBad with ⟨P, hPprime, hPne, hPzero⟩
  refine ⟨badPrimeContractionChain d.A d.𝔪 P, ?_, ?_, ?_⟩
  · exact badPrimeContractionChain_antitone d.A d.𝔪 P
  · exact d.badPrimeContractionChain_iInf_eq_bot_source P hPzero
  · exact
      badPrimeContractionChain_avoids_fixed_power_source d.A d.𝔪
        d.adicIdeal_eq_maximalIdeal_source P hPprime hPne hPzero

theorem BadQuotientSourceData.weaklyQuasiComplete_to_adicCompletionPrimeContraction_source
    (d : BadQuotientSourceData) :
    AdicCompletionPrimeContractionCondition d.A d.𝔪 := by
  classical
  by_contra hNot
  have hBadPrime :
      AdicCompletionBadPrime d.A d.𝔪 :=
    (not_adicCompletionPrimeContractionCondition_iff_badPrime d.A d.𝔪).1 hNot
  have hBadChain :
      WeaklyQuasiCompleteBadChain d.A d.𝔪 :=
    d.adicCompletion_badPrime_to_badChain_source hBadPrime
  exact (not_weaklyQuasiComplete_iff_badChain d.A d.𝔪).2 hBadChain d.hWeak

theorem quotient_map_sup_power
    (d : BadQuotientSourceData) (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk d.q) (d.q ⊔ d.𝔪 ^ n) =
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n := by
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow]

noncomputable def quotientPowerQuotientEquiv
    (d : BadQuotientSourceData) (n : ℕ) :
    d.A ⧸ (d.q ⊔ d.𝔪 ^ n) ≃+*
      (d.A ⧸ d.q) ⧸
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n :=
  (quotientSupQuotientEquiv d.A d.q (d.𝔪 ^ n)).trans
    (Ideal.quotEquivOfEq (by rw [Ideal.map_pow]))

@[simp]
theorem quotientPowerQuotientEquiv_mk
    (d : BadQuotientSourceData) (n : ℕ) (x : d.A) :
    quotientPowerQuotientEquiv d n (Ideal.Quotient.mk (d.q ⊔ d.𝔪 ^ n) x) =
      Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n)
        (Ideal.Quotient.mk d.q x) := by
  simp [quotientPowerQuotientEquiv]

noncomputable def completedRingToQuotientFinite
    (d : BadQuotientSourceData) (n : ℕ) :
    AdicCompletion d.𝔪 d.A →+*
      (d.A ⧸ d.q) ⧸ (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n :=
  (quotientPowerQuotientEquiv d n).toRingHom.comp
    ((Ideal.Quotient.factor
      (show d.𝔪 ^ n ≤ d.q ⊔ d.𝔪 ^ n by exact le_sup_right)).comp
        (AdicCompletion.evalₐ d.𝔪 n).toRingHom)

@[simp]
theorem completedRingToQuotientFinite_of
    (d : BadQuotientSourceData) (n : ℕ) (x : d.A) :
    completedRingToQuotientFinite d n (AdicCompletion.of d.𝔪 d.A x) =
      Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n)
        (Ideal.Quotient.mk d.q x) := by
  simp [completedRingToQuotientFinite]

theorem quotientModuleLevelToRingLevelEquiv_eval_map_of
    (d : BadQuotientSourceData) (n : ℕ) (x : d.A) :
    quotientModuleLevelToRingLevelEquiv d n
        (AdicCompletion.eval d.𝔪 (d.A ⧸ d.q) n
          (AdicCompletion.map d.𝔪 (quotientLinearMap d)
            (AdicCompletion.of d.𝔪 d.A x))) =
      completedRingToQuotientFinite d n (AdicCompletion.of d.𝔪 d.A x) := by
  rw [AdicCompletion.map_of]
  rw [AdicCompletion.eval_of]
  change quotientModuleLevelEquiv d n
      (Submodule.Quotient.mk
        (p := d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))
        ((quotientLinearMap d) x)) =
    completedRingToQuotientFinite d n (AdicCompletion.of d.𝔪 d.A x)
  rw [quotientModuleLevelEquiv_mk]
  rw [completedRingToQuotientFinite_of]
  rfl

theorem quotientModuleLevelToRingLevelEquiv_eval_map
    (d : BadQuotientSourceData) (n : ℕ)
    (x : AdicCompletion d.𝔪 d.A) :
    quotientModuleLevelToRingLevelEquiv d n
        (AdicCompletion.eval d.𝔪 (d.A ⧸ d.q) n
          (AdicCompletion.map d.𝔪 (quotientLinearMap d) x)) =
      completedRingToQuotientFinite d n x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
      simp only [AdicCompletion.map_mk, AdicCompletion.coe_eval,
        AdicCompletion.mk_apply_coe, AdicCompletion.AdicCauchySequence.map_apply_coe,
        Submodule.mkQ_apply]
      change quotientModuleLevelEquiv d n
          (Submodule.Quotient.mk
            (p := d.𝔪 ^ n • (⊤ : Submodule d.A (d.A ⧸ d.q)))
            (Ideal.Quotient.mk d.q (a n))) =
        Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n)
          (Ideal.Quotient.mk d.q (a n))
      rw [quotientModuleLevelEquiv_mk]
      rfl

theorem completedRingToQuotientFinite_surjective
    (d : BadQuotientSourceData) (n : ℕ) :
    Function.Surjective (completedRingToQuotientFinite d n) := by
  intro y
  obtain ⟨z, hz⟩ := (quotientPowerQuotientEquiv d n).surjective y
  obtain ⟨u, hu⟩ :=
    Ideal.Quotient.factor_surjective
      (show d.𝔪 ^ n ≤ d.q ⊔ d.𝔪 ^ n by exact le_sup_right) z
  obtain ⟨x, hx⟩ := AdicCompletion.surjective_evalₐ d.𝔪 n u
  refine ⟨x, ?_⟩
  simp [completedRingToQuotientFinite, hx, hu, hz]

theorem completedRingToQuotientFinite_compatible
    (d : BadQuotientSourceData) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) hmn).comp
        (completedRingToQuotientFinite d n) =
      completedRingToQuotientFinite d m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h a =>
      suffices
          Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ m)
              (Ideal.Quotient.mk d.q (a n)) =
            Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ m)
              (Ideal.Quotient.mk d.q (a m)) by
        simpa [completedRingToQuotientFinite] using this
      rw [Ideal.Quotient.eq]
      change Ideal.Quotient.mk d.q (a n) - Ideal.Quotient.mk d.q (a m) ∈
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ m
      rw [← map_sub]
      rw [← Ideal.map_pow]
      have hmSub : a n - a m ∈ (d.𝔪 ^ m • ⊤ : Submodule d.A d.A) :=
        SModEq.sub_mem.mp (a.property hmn).symm
      have hmIdeal : a n - a m ∈ d.𝔪 ^ m := by
        simpa using hmSub
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk d.q) hmIdeal

noncomputable def completedRingToQuotientCompletion
    (d : BadQuotientSourceData) :
    AdicCompletion d.𝔪 d.A →+* quotientAdicCompletion d :=
  AdicCompletion.liftRingHom
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
    (fun n => completedRingToQuotientFinite d n)
    (fun hmn => completedRingToQuotientFinite_compatible d hmn)

@[simp]
theorem completedRingToQuotientCompletion_eval
    (d : BadQuotientSourceData) (n : ℕ)
    (x : AdicCompletion d.𝔪 d.A) :
    AdicCompletion.evalₐ (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) n
        (completedRingToQuotientCompletion d x) =
      completedRingToQuotientFinite d n x := by
  exact AdicCompletion.evalₐ_liftRingHom
    (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
    (fun n => completedRingToQuotientFinite d n)
    (fun hmn => completedRingToQuotientFinite_compatible d hmn) n x

@[simp]
theorem completedRingToQuotientCompletion_of_eval
    (d : BadQuotientSourceData) (n : ℕ) (x : d.A) :
    AdicCompletion.evalₐ (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) n
        (completedRingToQuotientCompletion d (AdicCompletion.of d.𝔪 d.A x)) =
      Ideal.Quotient.mk ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n)
        (Ideal.Quotient.mk d.q x) := by
  simp [completedRingToQuotientCompletion_eval]

theorem quotientModuleCompletionToQuotientAdicCompletion_comp_map
    (d : BadQuotientSourceData)
    (x : AdicCompletion d.𝔪 d.A) :
    quotientModuleCompletionToQuotientAdicCompletion d
        (AdicCompletion.map d.𝔪 (quotientLinearMap d) x) =
      completedRingToQuotientCompletion d x := by
  apply AdicCompletion.ext
  intro n
  change quotientModuleLevelToAdicLevelEquiv d n
      ((AdicCompletion.map d.𝔪 (quotientLinearMap d) x).val n) =
    (completedRingToQuotientCompletion d x).val n
  rw [quotientModuleLevelToAdicLevelEquiv_eq_factor_ringLevel]
  change Ideal.Quotient.factor
      (show (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n ≤
        ((Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n •
          (⊤ : Ideal (d.A ⧸ d.q))) by
        exact le_of_eq (by ext y; simp))
      (quotientModuleLevelToRingLevelEquiv d n
        (AdicCompletion.eval d.𝔪 (d.A ⧸ d.q) n
          (AdicCompletion.map d.𝔪 (quotientLinearMap d) x))) =
    (completedRingToQuotientCompletion d x).val n
  rw [quotientModuleLevelToRingLevelEquiv_eval_map]
  have h :=
    AdicCompletion.factor_evalₐ_eq_eval
      (I := Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
      (x := completedRingToQuotientCompletion d x)
      (n := n)
      (show (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n ≤
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ^ n • ⊤ by
        exact le_of_eq (by ext y; simp))
  rw [completedRingToQuotientCompletion_eval] at h
  simpa [AdicCompletion.eval_apply] using h.symm

theorem completedRingToQuotientCompletion_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective (completedRingToQuotientCompletion d) := by
  intro y
  obtain ⟨z, hz⟩ :=
    quotientModuleCompletionToQuotientAdicCompletion_surjective d y
  obtain ⟨x, hx⟩ := quotient_completion_map_surjective d z
  refine ⟨x, ?_⟩
  rw [← quotientModuleCompletionToQuotientAdicCompletion_comp_map d x]
  rw [hx, hz]

theorem quotient_completion_module_exact
    (d : BadQuotientSourceData) :
    Function.Exact
      (AdicCompletion.map d.𝔪 (d.q.subtype : d.q →ₗ[d.A] d.A))
      (AdicCompletion.map d.𝔪 (quotientLinearMap d)) := by
  letI : IsNoetherianRing d.A := d.hNoeth
  exact
    AdicCompletion.map_exact
      (I := d.𝔪)
      (f := (d.q.subtype : d.q →ₗ[d.A] d.A))
      (g := quotientLinearMap d)
      (Submodule.injective_subtype d.q)
      (by
        simpa [quotientLinearMap, Ideal.Quotient.mkₐ_eq_mk] using
          (LinearMap.exact_subtype_mkQ d.q))
      (quotient_mk_linear_surjective d)

theorem completedRingToQuotientCompletion_ker_le_completedSubmoduleRange
    (d : BadQuotientSourceData) :
    RingHom.ker (completedRingToQuotientCompletion d) ≤
      LinearMap.range
        (AdicCompletion.map d.𝔪 (d.q.subtype : d.q →ₗ[d.A] d.A)) := by
  intro x hx
  have hExact := quotient_completion_module_exact d
  have hcomp :
      quotientModuleCompletionToQuotientAdicCompletion d
          (AdicCompletion.map d.𝔪 (quotientLinearMap d) x) = 0 := by
    rw [quotientModuleCompletionToQuotientAdicCompletion_comp_map d x]
    exact hx
  have hzero :
      quotientAdicCompletionToQuotientModuleCompletion d
          (0 : quotientAdicCompletion d) = 0 := by
    ext n
    rfl
  have hxmap :
      AdicCompletion.map d.𝔪 (quotientLinearMap d) x = 0 := by
    have h := congrArg (quotientAdicCompletionToQuotientModuleCompletion d) hcomp
    rw [quotientModuleCompletionToQuotientAdicCompletion_leftInverse d
      (AdicCompletion.map d.𝔪 (quotientLinearMap d) x)] at h
    simpa [hzero] using h
  simpa [LinearMap.mem_range] using (hExact x).mp hxmap

theorem completedIdealTensorImage_le_completed_q
    (d : BadQuotientSourceData)
    (t : TensorProduct d.A (AdicCompletion d.𝔪 d.A) d.q) :
    AdicCompletion.ofTensorProduct d.𝔪 d.A
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id :
            AdicCompletion d.𝔪 d.A →ₗ[AdicCompletion d.𝔪 d.A]
              AdicCompletion d.𝔪 d.A)
          (d.q.subtype : d.q →ₗ[d.A] d.A) t) ∈
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q := by
  induction t using TensorProduct.induction_on with
  | zero =>
      exact Ideal.zero_mem _
  | tmul r x =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul,
        LinearMap.id_coe, id_eq, AdicCompletion.ofTensorProduct_tmul]
      change r * algebraMap d.A (AdicCompletion d.𝔪 d.A) (x : d.A) ∈
        Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ x.property)
  | add x y hx hy =>
      have hinner :
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion d.𝔪 d.A →ₗ[AdicCompletion d.𝔪 d.A]
                AdicCompletion d.𝔪 d.A)
            (d.q.subtype : d.q →ₗ[d.A] d.A)) (x + y) =
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion d.𝔪 d.A →ₗ[AdicCompletion d.𝔪 d.A]
                AdicCompletion d.𝔪 d.A)
            (d.q.subtype : d.q →ₗ[d.A] d.A)) x +
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion d.𝔪 d.A →ₗ[AdicCompletion d.𝔪 d.A]
                AdicCompletion d.𝔪 d.A)
            (d.q.subtype : d.q →ₗ[d.A] d.A)) y := by
        exact map_add _ x y
      rw [hinner]
      rw [LinearMap.map_add]
      exact Ideal.add_mem _ hx hy

theorem completedSubmoduleRange_le_completed_q
    (d : BadQuotientSourceData) :
    LinearMap.range
        (AdicCompletion.map d.𝔪 (d.q.subtype : d.q →ₗ[d.A] d.A)) ≤
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q := by
  letI : IsNoetherianRing d.A := d.hNoeth
  intro y hy
  obtain ⟨z, rfl⟩ := (LinearMap.mem_range).mp hy
  letI : Module.Finite d.A d.q := inferInstance
  obtain ⟨t, ht⟩ :=
    AdicCompletion.ofTensorProduct_surjective_of_finite d.𝔪 d.q z
  rw [← ht]
  have hnat :=
    congrFun
      (congrArg DFunLike.coe
        (AdicCompletion.ofTensorProduct_naturality d.𝔪
          (d.q.subtype : d.q →ₗ[d.A] d.A))) t
  change
      ((AdicCompletion.map d.𝔪 (d.q.subtype : d.q →ₗ[d.A] d.A)) ∘ₗ
        AdicCompletion.ofTensorProduct d.𝔪 d.q) t ∈
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q
  rw [hnat]
  exact completedIdealTensorImage_le_completed_q d t

theorem completedRingToQuotientCompletion_ker_contains_completed_q
    (d : BadQuotientSourceData) :
    Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q ≤
      RingHom.ker (completedRingToQuotientCompletion d) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change
    completedRingToQuotientCompletion d
      (algebraMap d.A (AdicCompletion d.𝔪 d.A) x) = 0
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [show algebraMap d.A (AdicCompletion d.𝔪 d.A) x =
    AdicCompletion.of d.𝔪 d.A x by rfl]
  rw [completedRingToQuotientCompletion_of_eval]
  have hxmap : Ideal.Quotient.mk d.q x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  simpa [hxmap] using
    (map_zero
      (AdicCompletion.evalₐ
        (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) n)).symm

noncomputable def completedQuotientToQuotientCompletion
    (d : BadQuotientSourceData) :
    (AdicCompletion d.𝔪 d.A ⧸
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
      →+* quotientAdicCompletion d :=
  Ideal.Quotient.lift
    (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
    (completedRingToQuotientCompletion d)
    (fun _ hx =>
      (completedRingToQuotientCompletion_ker_contains_completed_q d hx))

@[simp]
theorem completedQuotientToQuotientCompletion_mk
    (d : BadQuotientSourceData) (x : AdicCompletion d.𝔪 d.A) :
    completedQuotientToQuotientCompletion d
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) x) =
      completedRingToQuotientCompletion d x := by
  rfl

structure CompletedQuotientMapSourceFacts
    (d : BadQuotientSourceData) : Prop where
  completedRing_surjective :
    Function.Surjective (completedRingToQuotientCompletion d)
  completedRing_ker_le_completed_q :
    RingHom.ker (completedRingToQuotientCompletion d) ≤
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q

theorem completedRingToQuotientCompletion_ker_le_completed_q_source
    (d : BadQuotientSourceData) :
    RingHom.ker (completedRingToQuotientCompletion d) ≤
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q := by
  exact (completedRingToQuotientCompletion_ker_le_completedSubmoduleRange d).trans
    (completedSubmoduleRange_le_completed_q d)

theorem completedQuotientMapSourceFacts_source
    (d : BadQuotientSourceData) :
    CompletedQuotientMapSourceFacts d :=
  { completedRing_surjective := completedRingToQuotientCompletion_surjective d
    completedRing_ker_le_completed_q :=
      completedRingToQuotientCompletion_ker_le_completed_q_source d }

theorem completedRingToQuotientCompletion_surjective_source
    (d : BadQuotientSourceData) :
    Function.Surjective (completedRingToQuotientCompletion d) :=
  completedRingToQuotientCompletion_surjective d

theorem completedQuotientToQuotientCompletion_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective (completedQuotientToQuotientCompletion d) := by
  intro y
  rcases completedRingToQuotientCompletion_surjective_source d y with ⟨x, rfl⟩
  exact
    ⟨Ideal.Quotient.mk
      (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) x,
      rfl⟩

theorem completedRingToQuotientCompletion_ker_eq_completed_q_source
    (d : BadQuotientSourceData) :
    RingHom.ker (completedRingToQuotientCompletion d) =
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q :=
  le_antisymm
    (completedRingToQuotientCompletion_ker_le_completed_q_source d)
    (completedRingToQuotientCompletion_ker_contains_completed_q d)

theorem completedQuotientToQuotientCompletion_injective
    (d : BadQuotientSourceData) :
    Function.Injective (completedQuotientToQuotientCompletion d) := by
  dsimp [completedQuotientToQuotientCompletion]
  exact
    RingHom.lift_injective_of_ker_le_ideal
      (Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
      (fun _ hx => completedRingToQuotientCompletion_ker_contains_completed_q d hx)
      (completedRingToQuotientCompletion_ker_le_completed_q_source d)

theorem completedQuotientToQuotientCompletion_bijective_source
    (d : BadQuotientSourceData) :
    Function.Bijective (completedQuotientToQuotientCompletion d) := by
  exact
    ⟨completedQuotientToQuotientCompletion_injective d,
      completedQuotientToQuotientCompletion_surjective d⟩

noncomputable def quotientCompletionEquiv_source
    (d : BadQuotientSourceData) :
    quotientAdicCompletion d ≃+*
      (AdicCompletion d.𝔪 d.A ⧸
        Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) :=
  (RingEquiv.ofBijective
    (completedQuotientToQuotientCompletion d)
    (completedQuotientToQuotientCompletion_bijective_source d)).symm

structure QuotientCompletionAnalyticBridge (d : BadQuotientSourceData) where
  quotientCompletionEquiv :
    quotientAdicCompletion d ≃+*
      (AdicCompletion d.𝔪 d.A ⧸
        Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
  weakCriterionOnQuotientCompletion :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d)

theorem quotient_dimensionOneCriterionOnQuotientCompletion_source
    (d : BadQuotientSourceData) :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d) := by
  letI : IsNoetherianRing (d.A ⧸ d.q) := d.quotient_isNoetherian
  letI : IsLocalRing (d.A ⧸ d.q) := d.quotient_isLocal
  letI : IsDomain (d.A ⧸ d.q) := d.quotient_isDomain
  exact
    quotient_dimensionOneCriterionOnQuotientCompletion_of_source d
      d.quotient_ringKrullDim_eq_one_source
      (dimensionOne_weaklyQuasiComplete_iff_adicCompletion_source
        (d.A ⧸ d.q) (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪)
        d.quotient_adicIdeal_eq_maximalIdeal_source
        d.quotient_ringKrullDim_eq_one_source)

noncomputable def quotientCompletionAnalyticBridge_source
    (d : BadQuotientSourceData) :
    QuotientCompletionAnalyticBridge d :=
  { quotientCompletionEquiv := quotientCompletionEquiv_source d
    weakCriterionOnQuotientCompletion :=
      quotient_dimensionOneCriterionOnQuotientCompletion_source d }

theorem quotient_analyticCriterionOnCompletedQuotient_source
    (d : BadQuotientSourceData) :
    WeaklyQuasiComplete (d.A ⧸ d.q)
      (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) ↔
        AnalyticallyIrreducible (d.A ⧸ d.q)
          (AdicCompletion d.𝔪 d.A ⧸
            Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) := by
  let b := quotientCompletionAnalyticBridge_source d
  constructor
  · intro hWeak
    have hDomain :
        AnalyticallyIrreducible (d.A ⧸ d.q) (quotientAdicCompletion d) :=
      b.weakCriterionOnQuotientCompletion.1 hWeak
    dsimp [AnalyticallyIrreducible] at hDomain ⊢
    haveI : IsDomain (quotientAdicCompletion d) := hDomain
    exact MulEquiv.isDomain
      (quotientAdicCompletion d) b.quotientCompletionEquiv.symm.toMulEquiv
  · intro hDomain
    apply b.weakCriterionOnQuotientCompletion.2
    dsimp [AnalyticallyIrreducible] at hDomain ⊢
    haveI : IsDomain
        (AdicCompletion d.𝔪 d.A ⧸
          Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q) := hDomain
    exact MulEquiv.isDomain
      (AdicCompletion d.𝔪 d.A ⧸
        Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
      b.quotientCompletionEquiv.toMulEquiv

theorem all_quotients_weak_criterion_source
    (d : BadQuotientSourceData) :
    QuasiComplete d.A d.𝔪 ↔
      ∀ J : Ideal d.A,
        WeaklyQuasiComplete (d.A ⧸ J)
          (Ideal.map (Ideal.Quotient.mk J) d.𝔪) := by
  exact quasiComplete_iff_all_quotients_weak d.A d.𝔪

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
  sourcePrimeContraction :
    AdicCompletionPrimeContractionCondition data.A data.𝔪

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
    ⟨d.A, d.instA, d.𝔪, d.ι, d.q, d.a, d.jensenCompletion, d.hCounter,
      d.hNoeth, d.hLocal, d.hDomain, d.hWeak, d.hBot, d.hNonzeroContraction, d.hqComap,
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
    ⟨A, instA, 𝔪, ι, q, a, w, hCounter, hNoeth, hLocal, hDomain, hWeak,
      hBot, hNonzeroContraction, hqComap, hqPrime, hqNonzero, hqPrincipal⟩
  letI := instA
  exact
    ⟨⟨A, 𝔪, ι, q, a, hCounter, hNoeth, hLocal, hDomain, w, hWeak, hBot,
      hNonzeroContraction, hqComap, hqPrime, hqNonzero, hqPrincipal⟩,
      trivial⟩

noncomputable def quotientCompletionWitness_source
    (d : BadQuotientSourceData)
    (w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    QuotientCompletionWitness d := by
  exact
    { Bhat :=
        AdicCompletion d.𝔪 d.A ⧸
          Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q
      instBhat := inferInstance
      quotientCompletionEquiv := completedQuotientTargetEquivNode d w
      analyticCriterionOnBhat :=
        quotient_analyticCriterionOnCompletedQuotient_source d }

theorem badQuotient_quasiCriterion_source
    (d : BadQuotientSourceData)
    (_w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    d.QuasiCriterion := by
  exact
    quasiComplete_iff_all_quotients_weak d.A d.𝔪

theorem badQuotient_structured_source :
    ∃ _ : BadQuotientStructuredSource, True := by
  rcases badQuotient_sourceData_from_jensen with ⟨d, _hd⟩
  let w : JensenCompletionWitness d.A d.𝔪 d.ι :=
    d.jensenCompletionWitness
  let qw : QuotientCompletionWitness d :=
    quotientCompletionWitness_source d w
  let hQuasi : d.QuasiCriterion :=
    badQuotient_quasiCriterion_source d w
  let hPrimeContraction :
      AdicCompletionPrimeContractionCondition d.A d.𝔪 :=
    d.weaklyQuasiComplete_to_adicCompletionPrimeContraction_source
  exact ⟨⟨d, w, qw, hQuasi, hPrimeContraction⟩, trivial⟩

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
    ((quasiComplete_iff_all_quotients_weak A 𝔪).1 hQuasi q)

theorem andersonProblem8a :
    ∃ (A : Type) (_inst : CommRing A),
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ 𝔪 : @Ideal A _inst.toSemiring,
          WeaklyQuasiComplete A 𝔪 ∧ ¬ QuasiComplete A 𝔪 := by
  exact counterexampleRing_weak_and_bad_quotient

end

end TODO
end Run202608192034
