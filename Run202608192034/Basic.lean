import Mathlib

/-!
Historical Archon-track definitions and completion lemmas for the Anderson
reproduction. All declarations are closed; results not internalized in this
track are exposed as explicitly named external boundaries. The canonical
zero-custom-axiom development lives under `Anderson/`.
-/

universe u

namespace Run202608192034
namespace TODO

def QuasiComplete (R : Type u) [CommRing R] (𝔪 : Ideal R) : Prop :=
  ∀ (I : ℕ → Ideal R),
    (∀ n : ℕ, I (n + 1) ≤ I n) →
      ∀ k : ℕ, 0 < k → ∃ s : ℕ, I s ≤ (⨅ n, I n) ⊔ 𝔪 ^ k

def WeaklyQuasiComplete (R : Type u) [CommRing R] (𝔪 : Ideal R) : Prop :=
  ∀ (I : ℕ → Ideal R),
    (∀ n : ℕ, I (n + 1) ≤ I n) →
      (⨅ n, I n) = ⊥ →
        ∀ k : ℕ, 0 < k → ∃ s : ℕ, I s ≤ 𝔪 ^ k

def genericFormalFiber (A T : Type u) [CommRing A] [CommRing T] (ι : A →+* T) :
    Set (Ideal T) :=
  {P | P.IsPrime ∧ Ideal.comap ι P = ⊥}

def AnalyticallyIrreducible (A T : Type u) [CommRing A] [CommRing T] : Prop :=
  IsDomain T

noncomputable def quotientSupQuotientEquiv
    (R : Type u) [CommRing R] (I J : Ideal R) :
    R ⧸ (I ⊔ J) ≃+* (R ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J := by
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  let K : Ideal (R ⧸ I) := Ideal.map π J
  have hSupLe : I ⊔ J ≤ Ideal.comap π K := by
    rw [sup_le_iff]
    constructor
    · intro x hx
      change π x ∈ K
      have hzero : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simp [hzero]
    · intro x hx
      exact Ideal.mem_map_of_mem π hx
  have hComapLe : Ideal.comap π K ≤ I ⊔ J := by
    calc
      Ideal.comap π K = J ⊔ RingHom.ker π := by
        dsimp [K, π]
        exact Ideal.comap_map_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J
      _ = J ⊔ I := by rw [Ideal.mk_ker]
      _ = I ⊔ J := by rw [sup_comm]
      _ ≤ I ⊔ J := le_rfl
  let f : R ⧸ (I ⊔ J) →+* (R ⧸ I) ⧸ K :=
    Ideal.quotientMap K π hSupLe
  exact RingEquiv.ofBijective f
    ⟨Ideal.quotientMap_injective' hComapLe,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩

@[simp]
theorem quotientSupQuotientEquiv_mk
    (R : Type u) [CommRing R] (I J : Ideal R) (x : R) :
    quotientSupQuotientEquiv R I J (Ideal.Quotient.mk (I ⊔ J) x) =
      Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)
        (Ideal.Quotient.mk I x) := by
  rfl

theorem quasiComplete_iff_all_quotients_weak
    (R : Type u) [CommRing R] (𝔪 : Ideal R) :
    QuasiComplete R 𝔪 ↔
      ∀ J : Ideal R,
        WeaklyQuasiComplete (R ⧸ J) (Ideal.map (Ideal.Quotient.mk J) 𝔪) := by
  constructor
  · intro hQuasi J K hKmono hKinf k hk
    let π : R →+* R ⧸ J := Ideal.Quotient.mk J
    let I : ℕ → Ideal R := fun n => Ideal.comap π (K n)
    have hImono : ∀ n : ℕ, I (n + 1) ≤ I n := by
      intro n
      exact Ideal.comap_mono (hKmono n)
    have hIinf : (⨅ n, I n) = J := by
      dsimp [I, π]
      rw [← Ideal.comap_iInf, hKinf]
      simpa [RingHom.ker_eq_comap_bot] using
        (Ideal.mk_ker (I := J) : RingHom.ker (Ideal.Quotient.mk J) = J)
    obtain ⟨s, hs⟩ := hQuasi I hImono k hk
    refine ⟨s, ?_⟩
    have hs' : I s ≤ J ⊔ 𝔪 ^ k := by
      simpa [hIinf] using hs
    have hmap : Ideal.map π (I s) ≤ Ideal.map π (J ⊔ 𝔪 ^ k) :=
      Ideal.map_mono hs'
    have hleft : Ideal.map π (I s) = K s := by
      dsimp [I, π]
      exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective (K s)
    have hright :
        Ideal.map π (J ⊔ 𝔪 ^ k) =
          (Ideal.map π 𝔪) ^ k := by
      rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow]
    simpa [hleft, hright, π] using hmap
  · intro hAll I hImono k hk
    let J : Ideal R := ⨅ n, I n
    let π : R →+* R ⧸ J := Ideal.Quotient.mk J
    let K : ℕ → Ideal (R ⧸ J) := fun n => Ideal.map π (I n)
    have hJ_le : ∀ n : ℕ, J ≤ I n := by
      intro n
      exact iInf_le _ n
    have hKmono : ∀ n : ℕ, K (n + 1) ≤ K n := by
      intro n
      exact Ideal.map_mono (hImono n)
    have hKinf : (⨅ n, K n) = ⊥ := by
      apply Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
      have hKer : RingHom.ker π = J := by
        dsimp [π]
        exact Ideal.mk_ker
      have hComapBot : Ideal.comap π (⊥ : Ideal (R ⧸ J)) = J := by
        rw [← RingHom.ker_eq_comap_bot, hKer]
      have hEach :
          ∀ n : ℕ, Ideal.comap π (Ideal.map π (I n)) = I n ⊔ J := by
        intro n
        rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
          hComapBot]
      calc
        Ideal.comap π (⨅ n, K n) =
            J := by
              dsimp [K]
              rw [Ideal.comap_iInf]
              apply le_antisymm
              · refine le_iInf fun n => ?_
                calc
                  (⨅ n, Ideal.comap π (Ideal.map π (I n))) ≤
                      Ideal.comap π (Ideal.map π (I n)) := iInf_le _ n
                  _ = I n ⊔ J := hEach n
                  _ = I n := sup_eq_left.mpr (hJ_le n)
              · exact le_iInf fun n => by
                  rw [hEach n]
                  exact le_sup_right
        _ = Ideal.comap π (⊥ : Ideal (R ⧸ J)) := hComapBot.symm
    obtain ⟨s, hs⟩ := hAll J K hKmono hKinf k hk
    refine ⟨s, ?_⟩
    have hsComap : I s ≤ Ideal.comap π ((Ideal.map π 𝔪) ^ k) :=
      Ideal.map_le_iff_le_comap.mp hs
    have hComap :
        Ideal.comap π ((Ideal.map π 𝔪) ^ k) = J ⊔ 𝔪 ^ k := by
      rw [← Ideal.map_pow]
      calc
        Ideal.comap π (Ideal.map π (𝔪 ^ k)) =
            𝔪 ^ k ⊔ RingHom.ker π := by
              exact Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective (𝔪 ^ k)
        _ = J ⊔ 𝔪 ^ k := by
              rw [Ideal.mk_ker, sup_comm]
    simpa [hComap, J, π] using hsComap

theorem weaklyQuasiComplete_iff_completion_primes
    (A Ahat : Type u) [CommRing A] [CommRing Ahat] (𝔪 : Ideal A)
    (ι : A →+* Ahat)
    (hCriterion :
      WeaklyQuasiComplete A 𝔪 ↔
        ∀ P : Ideal Ahat, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥) :
    WeaklyQuasiComplete A 𝔪 ↔
      ∀ P : Ideal Ahat, P.IsPrime → P ≠ ⊥ → Ideal.comap ι P ≠ ⊥ := by
  exact hCriterion

def AdicCompletionPrimeContractionCondition
    (A : Type u) [CommRing A] (𝔪 : Ideal A) : Prop :=
  ∀ P : Ideal (AdicCompletion 𝔪 A), P.IsPrime → P ≠ ⊥ →
    Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P ≠ ⊥

theorem adicCompletionPrimeContractionCondition_iff_target
    (A T : Type u) [CommRing A] [CommRing T] (𝔪 : Ideal A)
    (ι : A →+* T) (e : AdicCompletion 𝔪 A ≃+* T)
    (hι : ι = e.toRingHom.comp (algebraMap A (AdicCompletion 𝔪 A))) :
    AdicCompletionPrimeContractionCondition A 𝔪 ↔
      ∀ Q : Ideal T, Q.IsPrime → Q ≠ ⊥ → Ideal.comap ι Q ≠ ⊥ := by
  constructor
  · intro hCompletion Q hQPrime hQNe
    let P : Ideal (AdicCompletion 𝔪 A) := Ideal.comap e Q
    have hPPrime : P.IsPrime := by
      letI : Q.IsPrime := hQPrime
      exact Ideal.comap_isPrime e Q
    have hPNe : P ≠ ⊥ := by
      intro hPBot
      apply hQNe
      calc
        Q = Ideal.map e P :=
          (Ideal.map_comap_of_surjective e e.surjective Q).symm
        _ = ⊥ := by rw [hPBot, Ideal.map_bot]
    simpa [P, hι, Ideal.comap_comap] using
      hCompletion P hPPrime hPNe
  · intro hTarget P hPPrime hPNe
    let Q : Ideal T := Ideal.map e P
    have hQPrime : Q.IsPrime := by
      letI : P.IsPrime := hPPrime
      exact inferInstance
    have hQNe : Q ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hPNe
    have hContraction := hTarget Q hQPrime hQNe
    rw [hι] at hContraction
    change
      Ideal.comap (e.toRingHom.comp
        (algebraMap A (AdicCompletion 𝔪 A))) (Ideal.map e P) ≠ ⊥
      at hContraction
    rw [← Ideal.comap_comap] at hContraction
    have hComapMap :
        Ideal.comap e.toRingHom (Ideal.map e P) = P := by
      simpa only [Ideal.map_coe] using
        (Ideal.comap_map_of_bijective e.toRingHom e.bijective :
          Ideal.comap e.toRingHom (Ideal.map e.toRingHom P) = P)
    rw [hComapMap] at hContraction
    exact hContraction

def WeaklyQuasiCompleteBadChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A) : Prop :=
  ∃ I : ℕ → Ideal A,
    (∀ n : ℕ, I (n + 1) ≤ I n) ∧
      (⨅ n, I n) = ⊥ ∧
        ∃ k : ℕ, 0 < k ∧ ∀ s : ℕ, ¬ I s ≤ 𝔪 ^ k

def AdicCompletionBadPrime
    (A : Type u) [CommRing A] (𝔪 : Ideal A) : Prop :=
  ∃ P : Ideal (AdicCompletion 𝔪 A),
    P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P = ⊥

noncomputable def adicCompletionPowerImage
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (n : ℕ) :
    Ideal (AdicCompletion 𝔪 A) :=
  Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ n)

noncomputable def badPrimeContractionChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) (n : ℕ) : Ideal A :=
  Ideal.comap (algebraMap A (AdicCompletion 𝔪 A))
    (P ⊔ adicCompletionPowerImage A 𝔪 n)

@[simp]
theorem mem_badPrimeContractionChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) (n : ℕ) (x : A) :
    x ∈ badPrimeContractionChain A 𝔪 P n ↔
      algebraMap A (AdicCompletion 𝔪 A) x ∈
        P ⊔ adicCompletionPowerImage A 𝔪 n := by
  rfl

theorem adicCompletionPowerImage_antitone
    (A : Type u) [CommRing A] (𝔪 : Ideal A) :
    Antitone (adicCompletionPowerImage A 𝔪) := by
  intro m n hmn
  exact Ideal.map_mono (Ideal.pow_le_pow_right hmn)

theorem badPrimeContractionChain_antitone
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    ∀ n : ℕ,
      badPrimeContractionChain A 𝔪 P (n + 1) ≤
        badPrimeContractionChain A 𝔪 P n := by
  intro n
  exact Ideal.comap_mono
    (sup_le_sup le_rfl ((adicCompletionPowerImage_antitone A 𝔪) n.le_succ))

theorem power_le_badPrimeContractionChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) (n : ℕ) :
    𝔪 ^ n ≤ badPrimeContractionChain A 𝔪 P n := by
  intro x hx
  rw [mem_badPrimeContractionChain]
  have hle :
      adicCompletionPowerImage A 𝔪 n ≤
        P ⊔ adicCompletionPowerImage A 𝔪 n := le_sup_right
  exact hle (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion 𝔪 A)) hx)

theorem comap_le_badPrimeContractionChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) (n : ℕ) :
    Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P ≤
      badPrimeContractionChain A 𝔪 P n := by
  exact Ideal.comap_mono le_sup_left

theorem comap_le_badPrimeContractionChain_iInf
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P ≤
      ⨅ n, badPrimeContractionChain A 𝔪 P n := by
  exact le_iInf fun n => comap_le_badPrimeContractionChain A 𝔪 P n

theorem adicCompletionPowerImage_one_ne_top
    (A : Type u) [CommRing A] [IsLocalRing A] (𝔪 : Ideal A)
    (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    adicCompletionPowerImage A 𝔪 1 ≠ ⊤ := by
  intro htop
  have hmap_eq_bot :
      Ideal.map (AdicCompletion.evalₐ 𝔪 1).toRingHom
        (adicCompletionPowerImage A 𝔪 1) = ⊥ := by
    rw [adicCompletionPowerImage, Ideal.map_map]
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    rw [RingHom.mem_ker]
    change (AdicCompletion.evalₐ 𝔪 1)
        (algebraMap A (AdicCompletion 𝔪 A) a) = 0
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have htopbot : (⊤ : Ideal (A ⧸ 𝔪 ^ 1)) = ⊥ := by
    calc
      (⊤ : Ideal (A ⧸ 𝔪 ^ 1)) =
          Ideal.map (AdicCompletion.evalₐ 𝔪 1).toRingHom ⊤ := by
            rw [Ideal.map_top]
      _ = Ideal.map (AdicCompletion.evalₐ 𝔪 1).toRingHom
          (adicCompletionPowerImage A 𝔪 1) := by rw [htop]
      _ = ⊥ := hmap_eq_bot
  have hqmem : (1 : A ⧸ 𝔪 ^ 1) ∈ (⊥ : Ideal (A ⧸ 𝔪 ^ 1)) := by
    rw [← htopbot]
    trivial
  have hqzero : (1 : A ⧸ 𝔪 ^ 1) = 0 := by
    simpa using hqmem
  have hOnePow : (1 : A) ∈ 𝔪 ^ 1 :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hqzero)
  have hOneM : (1 : A) ∈ 𝔪 := by
    simpa using hOnePow
  have hmtop : 𝔪 = ⊤ := (Ideal.eq_top_iff_one 𝔪).mpr hOneM
  have hmne : 𝔪 ≠ ⊤ := by
    rw [hMax]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  exact hmne hmtop

theorem adicCompletion_quotient_hausdorff_of_noetherian_local_completion
    (A : Type u) [CommRing A] [IsLocalRing A] (𝔪 : Ideal A)
    (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    [IsNoetherianRing (AdicCompletion 𝔪 A)]
    [IsLocalRing (AdicCompletion 𝔪 A)]
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P) := by
  exact IsHausdorff.of_isLocalRing
    (adicCompletionPowerImage A 𝔪 1)
    (AdicCompletion 𝔪 A ⧸ P)
    (adicCompletionPowerImage_one_ne_top A 𝔪 hMax)

theorem adicCompletion_quotient_hausdorff_of_noetherian_jacobson_completion
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    [IsNoetherianRing (AdicCompletion 𝔪 A)]
    (hJac :
      adicCompletionPowerImage A 𝔪 1 ≤
        (⊥ : Ideal (AdicCompletion 𝔪 A)).jacobson)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P) := by
  exact IsHausdorff.of_le_jacobson
    (adicCompletionPowerImage A 𝔪 1)
    (AdicCompletion 𝔪 A ⧸ P)
    hJac

theorem adicCompletionPowerImage_one_le_jacobson_of_isAdicComplete
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (hComplete :
      IsAdicComplete (adicCompletionPowerImage A 𝔪 1) (AdicCompletion 𝔪 A)) :
    adicCompletionPowerImage A 𝔪 1 ≤
      (⊥ : Ideal (AdicCompletion 𝔪 A)).jacobson := by
  exact @IsAdicComplete.le_jacobson_bot
    (AdicCompletion 𝔪 A) _ (adicCompletionPowerImage A 𝔪 1) hComplete

/--
External standard-completion boundary: over a Noetherian local ring, every
ideal of the maximal-adic completion is closed, equivalently every quotient of
the completion is Hausdorff for the induced adic topology.  This is the
Krull-intersection/Artin--Rees input used in Anderson's proof.  Mathlib v4.29
contains the quotient-Hausdorff theorem once Noetherianity of the completion is
available, but not yet the general theorem that an adic completion of a
Noetherian ring is Noetherian.
-/
axiom adicCompletion_quotient_hausdorff_external
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P)

theorem adicCompletion_quotient_hausdorff_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P) := by
  exact adicCompletion_quotient_hausdorff_external A 𝔪 _hMax P

theorem adicCompletion_neighborhood_iInf_le_prime_of_hausdorff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A))
    [IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P)] :
    (⨅ n, P ⊔ adicCompletionPowerImage A 𝔪 n) ≤ P := by
  intro x hx
  have hxzero : (Ideal.Quotient.mk P) x = 0 := by
    refine IsHausdorff.haus
      (inferInstance : IsHausdorff (adicCompletionPowerImage A 𝔪 1)
        (AdicCompletion 𝔪 A ⧸ P))
      ((Ideal.Quotient.mk P) x) ?_
    intro n
    rw [SModEq.zero]
    have hx_n : x ∈ P ⊔ adicCompletionPowerImage A 𝔪 n :=
      (Ideal.mem_iInf.mp hx) n
    have hpow :
        adicCompletionPowerImage A 𝔪 1 ^ n =
          adicCompletionPowerImage A 𝔪 n := by
      simp [adicCompletionPowerImage, Ideal.map_pow]
    rw [hpow]
    rcases Submodule.mem_sup.mp hx_n with ⟨p, hp, z, hz, hpzx⟩
    have hqz :
        (Ideal.Quotient.mk P) z ∈
          (adicCompletionPowerImage A 𝔪 n) •
            (⊤ : Submodule (AdicCompletion 𝔪 A)
              (AdicCompletion 𝔪 A ⧸ P)) := by
      simpa [Algebra.smul_def] using
        (Submodule.smul_mem_smul hz
          (Submodule.mem_top :
            (1 : AdicCompletion 𝔪 A ⧸ P) ∈
              (⊤ : Submodule (AdicCompletion 𝔪 A)
                (AdicCompletion 𝔪 A ⧸ P))))
    have hqx :
        (Ideal.Quotient.mk P) x = (Ideal.Quotient.mk P) z := by
      calc
        (Ideal.Quotient.mk P) x =
            (Ideal.Quotient.mk P) (p + z) := by rw [hpzx]
        _ = (Ideal.Quotient.mk P) p + (Ideal.Quotient.mk P) z := rfl
        _ = 0 + (Ideal.Quotient.mk P) z := by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        _ = (Ideal.Quotient.mk P) z := zero_add _
    rwa [hqx]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

theorem adicCompletion_neighborhood_iInf_le_prime_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    (⨅ n, P ⊔ adicCompletionPowerImage A 𝔪 n) ≤ P := by
  letI :
      IsHausdorff (adicCompletionPowerImage A 𝔪 1)
        (AdicCompletion 𝔪 A ⧸ P) :=
    adicCompletion_quotient_hausdorff_source A 𝔪 _hMax P
  exact adicCompletion_neighborhood_iInf_le_prime_of_hausdorff A 𝔪 P

theorem badPrimeContractionChain_iInf_le_comap
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    (⨅ n, badPrimeContractionChain A 𝔪 P n) ≤
      Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P := by
  intro x hx
  have hxhat :
      algebraMap A (AdicCompletion 𝔪 A) x ∈
        ⨅ n, P ⊔ adicCompletionPowerImage A 𝔪 n := by
    rw [Ideal.mem_iInf]
    intro n
    exact (mem_badPrimeContractionChain A 𝔪 P n x).mp
      ((Ideal.mem_iInf.mp hx) n)
  exact adicCompletion_neighborhood_iInf_le_prime_source A 𝔪 hMax P hxhat

theorem badPrimeContractionChain_iInf_eq_comap
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A)) :
    (⨅ n, badPrimeContractionChain A 𝔪 P n) =
      Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P := by
  exact le_antisymm
    (badPrimeContractionChain_iInf_le_comap A 𝔪 hMax P)
    (comap_le_badPrimeContractionChain_iInf A 𝔪 P)

theorem badPrimeContractionChain_iInf_eq_bot
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A))
    (hPzero : Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P = ⊥) :
    (⨅ n, badPrimeContractionChain A 𝔪 P n) = ⊥ := by
  rw [badPrimeContractionChain_iInf_eq_comap A 𝔪 hMax P, hPzero]

theorem adicCompletion_nonzero_not_mem_powerImage_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    {y : AdicCompletion 𝔪 A} (hy : y ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ y ∉ adicCompletionPowerImage A 𝔪 k := by
  classical
  by_contra h
  push_neg at h
  have hyzero : y = 0 := by
    refine
      (inferInstance :
        IsHausdorff 𝔪 (AdicCompletion 𝔪 A)).haus y ?_
    intro n
    rw [SModEq.zero]
    have hEq :
        (𝔪 ^ n • (⊤ : Submodule A (AdicCompletion 𝔪 A))) =
          ((𝔪 ^ n).map (algebraMap A (AdicCompletion 𝔪 A))).restrictScalars A :=
      Ideal.smul_top_eq_map
        (R := A) (S := AdicCompletion 𝔪 A) (𝔪 ^ n)
    have hmemId :
        y ∈ ((𝔪 ^ n).map (algebraMap A (AdicCompletion 𝔪 A))).restrictScalars A := by
      by_cases hn : n = 0
      · subst n
        rw [pow_zero]
        have hmap :
            Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (1 : Ideal A) =
              ⊤ := by
          rw [Ideal.one_eq_top, Ideal.map_top]
        rw [hmap]
        trivial
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        simpa [adicCompletionPowerImage] using h n hpos
    exact hEq.symm ▸ hmemId
  exact hy hyzero

def quotientPowerLinearMap
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ) :
    A →ₗ[A] A ⧸ 𝔪 ^ t :=
  (Ideal.Quotient.mkₐ A (𝔪 ^ t)).toLinearMap

theorem quotientPowerLinearMap_surjective
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ) :
    Function.Surjective (quotientPowerLinearMap A 𝔪 t) := by
  intro y
  rcases Ideal.Quotient.mk_surjective y with ⟨a, rfl⟩
  exact ⟨a, rfl⟩

theorem adicCompletion_power_quotient_exact
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    Function.Exact
      (AdicCompletion.map 𝔪 ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A))
      (AdicCompletion.map 𝔪 (quotientPowerLinearMap A 𝔪 t)) := by
  exact
    AdicCompletion.map_exact
      (I := 𝔪)
      (f := ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A))
      (g := quotientPowerLinearMap A 𝔪 t)
      (Submodule.injective_subtype (𝔪 ^ t))
      (by
        simpa [quotientPowerLinearMap, Ideal.Quotient.mkₐ_eq_mk] using
          (LinearMap.exact_subtype_mkQ (𝔪 ^ t)))
      (quotientPowerLinearMap_surjective A 𝔪 t)

theorem adicCompletion_powerTensorImage_le_powerImage
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ)
    (z : TensorProduct A (AdicCompletion 𝔪 A) (𝔪 ^ t : Ideal A)) :
    AdicCompletion.ofTensorProduct 𝔪 A
        (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id :
            AdicCompletion 𝔪 A →ₗ[AdicCompletion 𝔪 A]
              AdicCompletion 𝔪 A)
          ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A) z) ∈
      adicCompletionPowerImage A 𝔪 t := by
  induction z using TensorProduct.induction_on with
  | zero =>
      exact Ideal.zero_mem _
  | tmul r x =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul,
        LinearMap.id_coe, id_eq, AdicCompletion.ofTensorProduct_tmul]
      change r * algebraMap A (AdicCompletion 𝔪 A) (x : A) ∈
        adicCompletionPowerImage A 𝔪 t
      exact Ideal.mul_mem_left _
        r (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion 𝔪 A)) x.property)
  | add x y hx hy =>
      have hinner :
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion 𝔪 A →ₗ[AdicCompletion 𝔪 A]
                AdicCompletion 𝔪 A)
            ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) (x + y) =
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion 𝔪 A →ₗ[AdicCompletion 𝔪 A]
                AdicCompletion 𝔪 A)
            ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) x +
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id :
              AdicCompletion 𝔪 A →ₗ[AdicCompletion 𝔪 A]
                AdicCompletion 𝔪 A)
            ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) y := by
        exact map_add _ x y
      rw [hinner]
      rw [LinearMap.map_add]
      exact Ideal.add_mem _ hx hy

theorem adicCompletion_powerSubmoduleRange_le_powerImage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    LinearMap.range
        (AdicCompletion.map 𝔪 ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) ≤
      adicCompletionPowerImage A 𝔪 t := by
  intro y hy
  obtain ⟨z, rfl⟩ := (LinearMap.mem_range).mp hy
  letI : Module.Finite A (𝔪 ^ t : Ideal A) := inferInstance
  obtain ⟨w, hw⟩ :=
    AdicCompletion.ofTensorProduct_surjective_of_finite 𝔪 (𝔪 ^ t : Ideal A) z
  rw [← hw]
  have hnat :=
    congrFun
      (congrArg DFunLike.coe
        (AdicCompletion.ofTensorProduct_naturality 𝔪
          ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A))) w
  change
      ((AdicCompletion.map 𝔪 ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) ∘ₗ
        AdicCompletion.ofTensorProduct 𝔪 (𝔪 ^ t : Ideal A)) w ∈
      adicCompletionPowerImage A 𝔪 t
  rw [hnat]
  exact adicCompletion_powerTensorImage_le_powerImage A 𝔪 t w

theorem adicCompletion_map_quotientPower_eq_zero_of_evalₐ_eq_zero
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ)
    {x : AdicCompletion 𝔪 A}
    (hx : (AdicCompletion.evalₐ 𝔪 t).toRingHom x = 0) :
    AdicCompletion.map 𝔪 (quotientPowerLinearMap A 𝔪 t) x = 0 := by
  apply AdicCompletion.ext
  intro n
  rw [AdicCompletion.map_val_apply]
  have hxEval :
      AdicCompletion.eval 𝔪 A t x = 0 := by
    have h :=
      AdicCompletion.factor_evalₐ_eq_eval
        (I := 𝔪) (x := x) (n := t)
        (show 𝔪 ^ t ≤ 𝔪 ^ t • (⊤ : Ideal A) by
          exact le_of_eq (by ext y; simp))
    rw [← h]
    change
      Ideal.Quotient.factor
          (show 𝔪 ^ t ≤ 𝔪 ^ t • (⊤ : Ideal A) by
            exact le_of_eq (by ext y; simp))
          ((AdicCompletion.evalₐ 𝔪 t).toRingHom x) = 0
    rw [hx]
    rfl
  by_cases hnt : n ≤ t
  · have hxn : x.val n = 0 := by
      rw [← AdicCompletion.transitionMap_comp_eval_apply 𝔪 A hnt x]
      change
        AdicCompletion.transitionMap 𝔪 A hnt
          ((AdicCompletion.eval 𝔪 A t) x) = 0
      rw [hxEval]
      rfl
    rw [hxn]
    simp
  · have htn : t ≤ n := le_of_not_ge hnt
    have hxt : x.val t = 0 := by
      simpa [AdicCompletion.eval_apply] using hxEval
    have hfactor :
        AdicCompletion.transitionMap 𝔪 A htn (x.val n) = 0 := by
      rw [AdicCompletion.transitionMap_comp_eval_apply 𝔪 A htn x, hxt]
    revert hfactor
    induction x.val n using Quotient.inductionOn' with
    | h a =>
        intro hfactor
        change
          Submodule.Quotient.mk
              (p := (𝔪 ^ n • ⊤ : Submodule A (A ⧸ 𝔪 ^ t)))
              (quotientPowerLinearMap A 𝔪 t a) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        have ha_zero :
            Submodule.Quotient.mk (p := (𝔪 ^ t • ⊤ : Submodule A A)) a = 0 := by
          simpa using hfactor
        have ha_mem : a ∈ 𝔪 ^ t := by
          have ha_mem_sub :
              a ∈ (𝔪 ^ t • ⊤ : Submodule A A) :=
            (Submodule.Quotient.mk_eq_zero _).mp ha_zero
          simpa using ha_mem_sub
        change quotientPowerLinearMap A 𝔪 t a ∈
          𝔪 ^ n • (⊤ : Submodule A (A ⧸ 𝔪 ^ t))
        have hq : quotientPowerLinearMap A 𝔪 t a = 0 := by
          change Ideal.Quotient.mk (𝔪 ^ t) a = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr ha_mem
        rw [hq]
        exact Submodule.zero_mem _

theorem adicCompletion_evalₐ_kernel_le_powerImage_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ 𝔪 t).toRingHom ≤
      adicCompletionPowerImage A 𝔪 t := by
  intro x hx
  have hExact := adicCompletion_power_quotient_exact A 𝔪 t
  have hxmap :
      AdicCompletion.map 𝔪 (quotientPowerLinearMap A 𝔪 t) x = 0 :=
    adicCompletion_map_quotientPower_eq_zero_of_evalₐ_eq_zero A 𝔪 t
      (RingHom.mem_ker.mp hx)
  have hxrange :
      x ∈ LinearMap.range
        (AdicCompletion.map 𝔪 ((𝔪 ^ t).subtype : (𝔪 ^ t : Ideal A) →ₗ[A] A)) := by
    simpa [LinearMap.mem_range] using (hExact x).mp hxmap
  exact adicCompletion_powerSubmoduleRange_le_powerImage A 𝔪 t hxrange

theorem adicCompletionPowerImage_eq_evalₐ_kernel
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    adicCompletionPowerImage A 𝔪 t =
      RingHom.ker (AdicCompletion.evalₐ 𝔪 t).toRingHom := by
  apply le_antisymm
  · rw [adicCompletionPowerImage]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change (algebraMap A (AdicCompletion 𝔪 A) a) ∈
      RingHom.ker (AdicCompletion.evalₐ 𝔪 t).toRingHom
    rw [RingHom.mem_ker]
    change (AdicCompletion.evalₐ 𝔪 t)
        (algebraMap A (AdicCompletion 𝔪 A) a) = 0
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · exact adicCompletion_evalₐ_kernel_le_powerImage_source A 𝔪 t

theorem adicCompletionPowerImage_one_eq_evalₐ_kernel
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A) :
    adicCompletionPowerImage A 𝔪 1 =
      RingHom.ker (AdicCompletion.evalₐ 𝔪 1).toRingHom := by
  simpa using adicCompletionPowerImage_eq_evalₐ_kernel A 𝔪 1

theorem adicCompletionPowerImage_one_pow
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ) :
    adicCompletionPowerImage A 𝔪 1 ^ t =
      adicCompletionPowerImage A 𝔪 t := by
  simp [adicCompletionPowerImage, Ideal.map_pow]

theorem ideal_smul_top_eq_self
    (B : Type u) [CommRing B] (J : Ideal B) :
    J • (⊤ : Submodule B B) = (J : Submodule B B) := by
  apply le_antisymm
  · refine Submodule.smul_le.mpr ?_
    intro r hr x _hx
    change r * x ∈ J
    exact Ideal.mul_mem_right x J hr
  · intro x hx
    simpa using
      (Submodule.smul_mem_smul hx
        (Submodule.mem_top : (1 : B) ∈ (⊤ : Submodule B B)))

theorem adicCompletionPowerImage_one_pow_smul_top_restrictScalars
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (t : ℕ) :
    ((adicCompletionPowerImage A 𝔪 1 ^ t) •
        (⊤ : Submodule (AdicCompletion 𝔪 A) (AdicCompletion 𝔪 A))).restrictScalars A =
      (𝔪 ^ t • (⊤ : Submodule A (AdicCompletion 𝔪 A))) := by
  rw [adicCompletionPowerImage_one_pow]
  rw [adicCompletionPowerImage]
  ext x
  change
    x ∈ (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ t) •
      (⊤ : Submodule (AdicCompletion 𝔪 A) (AdicCompletion 𝔪 A))) ↔
    x ∈ (𝔪 ^ t • (⊤ : Submodule A (AdicCompletion 𝔪 A)))
  have hJ :
      Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ t) •
          (⊤ : Submodule (AdicCompletion 𝔪 A) (AdicCompletion 𝔪 A)) =
        (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ t) :
          Submodule (AdicCompletion 𝔪 A) (AdicCompletion 𝔪 A)) :=
    ideal_smul_top_eq_self (AdicCompletion 𝔪 A)
      (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ t))
  have hA :
      𝔪 ^ t • (⊤ : Submodule A (AdicCompletion 𝔪 A)) =
        (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ t)).restrictScalars A :=
    Ideal.smul_top_eq_map
      (R := A) (S := AdicCompletion 𝔪 A) (𝔪 ^ t)
  rw [hJ, hA]
  rfl

noncomputable def adicCompletionQuotientPowerImageEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    AdicCompletion 𝔪 A ⧸ adicCompletionPowerImage A 𝔪 t ≃+*
      A ⧸ 𝔪 ^ t :=
  (Ideal.quotEquivOfEq (adicCompletionPowerImage_eq_evalₐ_kernel A 𝔪 t)).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalₐ 𝔪 t).toRingHom)
      (AdicCompletion.surjective_evalₐ 𝔪 t))

noncomputable def adicCompletionQuotientPowerEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (t : ℕ) :
    AdicCompletion 𝔪 A ⧸ adicCompletionPowerImage A 𝔪 1 ^ t ≃+*
      A ⧸ 𝔪 ^ t :=
  (Ideal.quotEquivOfEq (adicCompletionPowerImage_one_pow A 𝔪 t)).trans
    (adicCompletionQuotientPowerImageEquiv A 𝔪 t)

theorem adicCompletionPowerImage_one_isMaximal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    (adicCompletionPowerImage A 𝔪 1).IsMaximal := by
  have hmMax : 𝔪.IsMaximal := by
    rw [hMax]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpowMax : (𝔪 ^ 1).IsMaximal := by
    simpa using hmMax
  letI : DivisionRing (A ⧸ 𝔪 ^ 1) := Ideal.Quotient.divisionRing (𝔪 ^ 1)
  rw [adicCompletionPowerImage_one_eq_evalₐ_kernel A 𝔪]
  exact RingHom.ker_isMaximal_of_surjective
    (AdicCompletion.evalₐ 𝔪 1).toRingHom
    (AdicCompletion.surjective_evalₐ 𝔪 1)

theorem adicCompletionPowerImage_one_isHausdorff
    (A : Type u) [CommRing A] (𝔪 : Ideal A) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A) := by
  have hMap :
      IsHausdorff (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) 𝔪)
        (AdicCompletion 𝔪 A) :=
    (IsHausdorff.map_algebraMap_iff
      (I := 𝔪) (S := AdicCompletion 𝔪 A)).mpr inferInstance
  simpa [adicCompletionPowerImage] using hMap

theorem adicCompletion_eval_eq_of_smodEq
    (A : Type u) [CommRing A] (𝔪 : Ideal A) (n : ℕ)
    {x y : AdicCompletion 𝔪 A}
    (hxy :
      x ≡ y
        [SMOD (𝔪 ^ n •
          (⊤ : Submodule A (AdicCompletion 𝔪 A)))]) :
    AdicCompletion.eval 𝔪 A n x = AdicCompletion.eval 𝔪 A n y := by
  rw [← sub_eq_zero]
  change AdicCompletion.eval 𝔪 A n (x - y) = 0
  change x - y ∈ LinearMap.ker (AdicCompletion.eval 𝔪 A n)
  have hsub :
      x - y ∈
        𝔪 ^ n • (⊤ : Submodule A (AdicCompletion 𝔪 A)) :=
    SModEq.sub_mem.mp hxy
  refine Submodule.smul_induction_on hsub ?_ ?_
  · intro r hr z _hz
    change AdicCompletion.eval 𝔪 A n (r • z) = 0
    rw [map_smul]
    induction (AdicCompletion.eval 𝔪 A n z) using Quotient.inductionOn' with
    | _ a =>
      simpa using (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_smul hr
          (Submodule.mem_top : a ∈ (⊤ : Submodule A A)))
  · intro z w hz hw
    exact Submodule.add_mem _ hz hw

theorem adicCompletion_isPrecomplete_original_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A) :
    IsPrecomplete 𝔪 (AdicCompletion 𝔪 A) := by
  refine ⟨?_⟩
  intro f hf
  let L : AdicCompletion 𝔪 A :=
    ⟨fun n => AdicCompletion.eval 𝔪 A n (f n), by
      intro m n hmn
      calc
        AdicCompletion.transitionMap 𝔪 A hmn
            (AdicCompletion.eval 𝔪 A n (f n))
            = AdicCompletion.eval 𝔪 A m (f n) := by
              exact AdicCompletion.transitionMap_comp_eval_apply 𝔪 A hmn (f n)
        _ = AdicCompletion.eval 𝔪 A m (f m) := by
              exact (adicCompletion_eval_eq_of_smodEq A 𝔪 m (hf hmn)).symm⟩
  refine ⟨L, ?_⟩
  intro n
  rw [SModEq.sub_mem]
  have hEval : AdicCompletion.eval 𝔪 A n (f n - L) = 0 := by
    change AdicCompletion.eval 𝔪 A n (f n) -
        AdicCompletion.eval 𝔪 A n L = 0
    have hLn : AdicCompletion.eval 𝔪 A n L =
        AdicCompletion.eval 𝔪 A n (f n) := rfl
    rw [hLn, sub_self]
    rfl
  have hEvalₐ : (AdicCompletion.evalₐ 𝔪 n).toRingHom (f n - L) = 0 := by
    change (AdicCompletion.evalₐ 𝔪 n) (f n - L) = 0
    have hfactor :=
      AdicCompletion.factor_eval_eq_evalₐ
        (I := 𝔪) (x := f n - L) (n := n)
        (show 𝔪 ^ n • (⊤ : Ideal A) ≤ 𝔪 ^ n by
          exact le_of_eq (by ext y; simp))
    rw [← hfactor, hEval]
    rfl
  have hmemImage :
      f n - L ∈ adicCompletionPowerImage A 𝔪 n :=
    adicCompletion_evalₐ_kernel_le_powerImage_source A 𝔪 n
      (by simpa [RingHom.mem_ker] using hEvalₐ)
  have hA :
      𝔪 ^ n • (⊤ : Submodule A (AdicCompletion 𝔪 A)) =
        (Ideal.map (algebraMap A (AdicCompletion 𝔪 A)) (𝔪 ^ n)).restrictScalars A :=
    Ideal.smul_top_eq_map
      (R := A) (S := AdicCompletion 𝔪 A) (𝔪 ^ n)
  rw [hA]
  simpa [adicCompletionPowerImage] using hmemImage

theorem adicCompletionPowerImage_one_isPrecomplete_of_original_precomplete
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    [IsPrecomplete 𝔪 (AdicCompletion 𝔪 A)] :
    IsPrecomplete (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A) := by
  refine ⟨?_⟩
  intro f hf
  have hfA :
      ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n
          [SMOD (𝔪 ^ m • (⊤ : Submodule A (AdicCompletion 𝔪 A)))] := by
    intro m n hmn
    rw [← adicCompletionPowerImage_one_pow_smul_top_restrictScalars A 𝔪 m]
    exact hf hmn
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec
      (inferInstance : IsPrecomplete 𝔪 (AdicCompletion 𝔪 A)) hfA
  refine ⟨L, ?_⟩
  intro n
  have hLn := hL n
  rw [← adicCompletionPowerImage_one_pow_smul_top_restrictScalars A 𝔪 n] at hLn
  exact hLn

theorem adicCompletionPowerImage_one_isAdicComplete_of_original_precomplete
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    [IsPrecomplete 𝔪 (AdicCompletion 𝔪 A)] :
    IsAdicComplete (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A) where
  toIsHausdorff := adicCompletionPowerImage_one_isHausdorff A 𝔪
  toIsPrecomplete :=
    adicCompletionPowerImage_one_isPrecomplete_of_original_precomplete A 𝔪

theorem adicCompletionPowerImage_one_isPrecomplete_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A) :
    IsPrecomplete (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A) := by
  letI : IsPrecomplete 𝔪 (AdicCompletion 𝔪 A) :=
    adicCompletion_isPrecomplete_original_source A 𝔪
  exact adicCompletionPowerImage_one_isPrecomplete_of_original_precomplete A 𝔪

theorem adicCompletionPowerImage_one_isAdicComplete_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A) :
    IsAdicComplete (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A) where
  toIsHausdorff := adicCompletionPowerImage_one_isHausdorff A 𝔪
  toIsPrecomplete := adicCompletionPowerImage_one_isPrecomplete_source A 𝔪

theorem adicCompletion_isLocalRing_of_original_precomplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    [IsPrecomplete 𝔪 (AdicCompletion 𝔪 A)] :
    IsLocalRing (AdicCompletion 𝔪 A) := by
  exact @isLocalRing_of_isAdicComplete_maximal
    (AdicCompletion 𝔪 A) _ (adicCompletionPowerImage A 𝔪 1)
    (adicCompletionPowerImage_one_isMaximal A 𝔪 hMax)
    (adicCompletionPowerImage_one_isAdicComplete_of_original_precomplete A 𝔪)

theorem adicCompletion_isLocalRing_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    IsLocalRing (AdicCompletion 𝔪 A) := by
  exact @isLocalRing_of_isAdicComplete_maximal
    (AdicCompletion 𝔪 A) _ (adicCompletionPowerImage A 𝔪 1)
    (adicCompletionPowerImage_one_isMaximal A 𝔪 hMax)
    (adicCompletionPowerImage_one_isAdicComplete_source A 𝔪)

theorem adicCompletion_quotient_hausdorff_of_noetherian_original_precomplete
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    [IsNoetherianRing (AdicCompletion 𝔪 A)]
    [IsPrecomplete 𝔪 (AdicCompletion 𝔪 A)]
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P) := by
  exact adicCompletion_quotient_hausdorff_of_noetherian_jacobson_completion
    A 𝔪
      (adicCompletionPowerImage_one_le_jacobson_of_isAdicComplete A 𝔪
      (adicCompletionPowerImage_one_isAdicComplete_of_original_precomplete A 𝔪))
    P

theorem adicCompletion_quotient_hausdorff_of_noetherian_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    [IsNoetherianRing (AdicCompletion 𝔪 A)]
    (P : Ideal (AdicCompletion 𝔪 A)) :
    IsHausdorff (adicCompletionPowerImage A 𝔪 1)
      (AdicCompletion 𝔪 A ⧸ P) := by
  exact adicCompletion_quotient_hausdorff_of_noetherian_jacobson_completion
    A 𝔪
    (adicCompletionPowerImage_one_le_jacobson_of_isAdicComplete A 𝔪
      (adicCompletionPowerImage_one_isAdicComplete_source A 𝔪))
    P

theorem adicCompletion_exists_approx_mod_powerImage_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] (𝔪 : Ideal A)
    (y : AdicCompletion 𝔪 A) :
    ∀ t : ℕ, ∃ a : A,
      y - algebraMap A (AdicCompletion 𝔪 A) a ∈
        adicCompletionPowerImage A 𝔪 t := by
  intro t
  rcases Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔪 t y) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply adicCompletion_evalₐ_kernel_le_powerImage_source A 𝔪 t
  rw [RingHom.mem_ker, map_sub]
  have hmapa :
      (AdicCompletion.evalₐ 𝔪 t).toRingHom
          (algebraMap A (AdicCompletion 𝔪 A) a) =
        Ideal.Quotient.mk (𝔪 ^ t) a := by
    simp [AdicCompletion.algebraMap_apply]
  rw [hmapa]
  exact sub_eq_zero.mpr ha.symm

theorem badPrimeContractionChain_avoids_fixed_power_of_element
    (A : Type u) [CommRing A] (𝔪 : Ideal A)
    (P : Ideal (AdicCompletion 𝔪 A)) (k : ℕ) (_hk : 0 < k)
    (y : AdicCompletion 𝔪 A)
    (hyP : y ∈ P)
    (hyNot : y ∉ adicCompletionPowerImage A 𝔪 k)
    (hApprox : ∀ t : ℕ, ∃ a : A,
      y - algebraMap A (AdicCompletion 𝔪 A) a ∈
        adicCompletionPowerImage A 𝔪 t) :
    ∀ s : ℕ, ¬ badPrimeContractionChain A 𝔪 P s ≤ 𝔪 ^ k := by
  intro s hle
  let t : ℕ := max s k
  rcases hApprox t with ⟨a, haApprox⟩
  have hts : s ≤ t := Nat.le_max_left s k
  have htk : k ≤ t := Nat.le_max_right s k
  have haApprox_s :
      y - algebraMap A (AdicCompletion 𝔪 A) a ∈
        adicCompletionPowerImage A 𝔪 s :=
    (adicCompletionPowerImage_antitone A 𝔪 hts) haApprox
  have hdelta_sup :
      y - algebraMap A (AdicCompletion 𝔪 A) a ∈
        P ⊔ adicCompletionPowerImage A 𝔪 s :=
    (show adicCompletionPowerImage A 𝔪 s ≤
      P ⊔ adicCompletionPowerImage A 𝔪 s from le_sup_right) haApprox_s
  have hy_sup : y ∈ P ⊔ adicCompletionPowerImage A 𝔪 s :=
    (show P ≤ P ⊔ adicCompletionPowerImage A 𝔪 s from le_sup_left) hyP
  have ha_image :
      algebraMap A (AdicCompletion 𝔪 A) a ∈
        P ⊔ adicCompletionPowerImage A 𝔪 s := by
    have hsub :=
      (P ⊔ adicCompletionPowerImage A 𝔪 s).sub_mem hy_sup hdelta_sup
    convert hsub using 1
    ring
  have ha_chain : a ∈ badPrimeContractionChain A 𝔪 P s :=
    (mem_badPrimeContractionChain A 𝔪 P s a).mpr ha_image
  have ha_pow : a ∈ 𝔪 ^ k := hle ha_chain
  have hfa_k :
      algebraMap A (AdicCompletion 𝔪 A) a ∈
        adicCompletionPowerImage A 𝔪 k :=
    Ideal.mem_map_of_mem (algebraMap A (AdicCompletion 𝔪 A)) ha_pow
  have haApprox_k :
      y - algebraMap A (AdicCompletion 𝔪 A) a ∈
        adicCompletionPowerImage A 𝔪 k :=
    (adicCompletionPowerImage_antitone A 𝔪 htk) haApprox
  have hy_k : y ∈ adicCompletionPowerImage A 𝔪 k := by
    have hsum :=
      (adicCompletionPowerImage A 𝔪 k).add_mem haApprox_k hfa_k
    convert hsum using 1
    ring
  exact hyNot hy_k

theorem badPrimeContractionChain_avoids_fixed_power_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (P : Ideal (AdicCompletion 𝔪 A))
    (_hPprime : P.IsPrime) (hPne : P ≠ ⊥)
    (_hPzero : Ideal.comap (algebraMap A (AdicCompletion 𝔪 A)) P = ⊥) :
    ∃ k : ℕ, 0 < k ∧
      ∀ s : ℕ, ¬ badPrimeContractionChain A 𝔪 P s ≤ 𝔪 ^ k := by
  rcases P.ne_bot_iff.mp hPne with ⟨y, hyP, hyNe⟩
  rcases adicCompletion_nonzero_not_mem_powerImage_source A 𝔪 _hMax hyNe with
    ⟨k, hk, hyNot⟩
  exact ⟨k, hk,
    badPrimeContractionChain_avoids_fixed_power_of_element A 𝔪 P k hk y hyP hyNot
      (adicCompletion_exists_approx_mod_powerImage_source A 𝔪 y)⟩

theorem not_weaklyQuasiComplete_iff_badChain
    (A : Type u) [CommRing A] (𝔪 : Ideal A) :
    ¬ WeaklyQuasiComplete A 𝔪 ↔ WeaklyQuasiCompleteBadChain A 𝔪 := by
  classical
  unfold WeaklyQuasiComplete WeaklyQuasiCompleteBadChain
  push_neg
  exact Iff.rfl

theorem not_adicCompletionPrimeContractionCondition_iff_badPrime
    (A : Type u) [CommRing A] (𝔪 : Ideal A) :
    ¬ AdicCompletionPrimeContractionCondition A 𝔪 ↔
      AdicCompletionBadPrime A 𝔪 := by
  classical
  unfold AdicCompletionPrimeContractionCondition AdicCompletionBadPrime
  push_neg
  exact Iff.rfl

theorem adicCompletion_badPrime_to_badChain_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    AdicCompletionBadPrime A 𝔪 → WeaklyQuasiCompleteBadChain A 𝔪 := by
  intro hBad
  rcases hBad with ⟨P, hPprime, hPne, hPzero⟩
  refine ⟨badPrimeContractionChain A 𝔪 P, ?_, ?_, ?_⟩
  · exact badPrimeContractionChain_antitone A 𝔪 P
  · exact badPrimeContractionChain_iInf_eq_bot A 𝔪 hMax P hPzero
  · exact badPrimeContractionChain_avoids_fixed_power_source A 𝔪 hMax P hPprime hPne hPzero

/--
Published-source boundary: D. D. Anderson, "Quasi-complete Semilocal Rings
and Modules", Corollary 2(1) (Springer, 2014).  Farley 2016, Proposition 1,
quotes this criterion in the same form.
-/
axiom anderson_corollary2_part1_external
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    WeaklyQuasiComplete A 𝔪 ↔
      AdicCompletionPrimeContractionCondition A 𝔪

/--
Published-source boundary: Anderson 2014, Corollary 2(3), the dimension-one
equivalence between weak quasi-completeness and analytic irreducibility.
-/
axiom anderson_corollary2_part3_external
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (hDim : ringKrullDim A = 1) :
    WeaklyQuasiComplete A 𝔪 ↔
      AnalyticallyIrreducible A (AdicCompletion 𝔪 A)

theorem weaklyQuasiComplete_badChain_to_adicCompletion_badPrime_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    WeaklyQuasiCompleteBadChain A 𝔪 → AdicCompletionBadPrime A 𝔪 := by
  intro hBadChain
  have hNotWeak : ¬ WeaklyQuasiComplete A 𝔪 :=
    (not_weaklyQuasiComplete_iff_badChain A 𝔪).2 hBadChain
  have hNotContraction :
      ¬ AdicCompletionPrimeContractionCondition A 𝔪 := by
    intro hContraction
    exact hNotWeak
      ((anderson_corollary2_part1_external A 𝔪 _hMax).2 hContraction)
  exact
    (not_adicCompletionPrimeContractionCondition_iff_badPrime A 𝔪).1
      hNotContraction

theorem weaklyQuasiComplete_to_adicCompletion_primeContraction_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (hWeak : WeaklyQuasiComplete A 𝔪) :
    AdicCompletionPrimeContractionCondition A 𝔪 := by
  classical
  by_contra hNot
  have hBadPrime :
      AdicCompletionBadPrime A 𝔪 :=
    (not_adicCompletionPrimeContractionCondition_iff_badPrime A 𝔪).1 hNot
  have hBadChain :
      WeaklyQuasiCompleteBadChain A 𝔪 :=
    adicCompletion_badPrime_to_badChain_source A 𝔪 hMax hBadPrime
  exact (not_weaklyQuasiComplete_iff_badChain A 𝔪).2 hBadChain hWeak

theorem adicCompletion_primeContraction_to_weaklyQuasiComplete_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (hPrimeContraction : AdicCompletionPrimeContractionCondition A 𝔪) :
    WeaklyQuasiComplete A 𝔪 := by
  classical
  by_contra hNotWeak
  have hBadChain :
      WeaklyQuasiCompleteBadChain A 𝔪 :=
    (not_weaklyQuasiComplete_iff_badChain A 𝔪).1 hNotWeak
  have hBadPrime :
      AdicCompletionBadPrime A 𝔪 :=
    weaklyQuasiComplete_badChain_to_adicCompletion_badPrime_source A 𝔪 hMax hBadChain
  exact
    (not_adicCompletionPrimeContractionCondition_iff_badPrime A 𝔪).2
      hBadPrime hPrimeContraction

theorem weaklyQuasiComplete_iff_adicCompletion_primeContraction_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A) :
    WeaklyQuasiComplete A 𝔪 ↔
      AdicCompletionPrimeContractionCondition A 𝔪 := by
  constructor
  · exact weaklyQuasiComplete_to_adicCompletion_primeContraction_source A 𝔪 hMax
  · exact adicCompletion_primeContraction_to_weaklyQuasiComplete_source A 𝔪 hMax

theorem dimensionOne_adicCompletion_primeContraction_iff_analyticIrreducible_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (_hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (_hDim : ringKrullDim A = 1) :
    AdicCompletionPrimeContractionCondition A 𝔪 ↔
      AnalyticallyIrreducible A (AdicCompletion 𝔪 A) := by
  exact
    (anderson_corollary2_part1_external A 𝔪 _hMax).symm.trans
      (anderson_corollary2_part3_external A 𝔪 _hMax _hDim)

theorem dimensionOne_weaklyQuasiComplete_iff
    (A Ahat : Type u) [CommRing A] [CommRing Ahat] (𝔪 : Ideal A)
    (hCriterion : WeaklyQuasiComplete A 𝔪 ↔ AnalyticallyIrreducible A Ahat) :
    WeaklyQuasiComplete A 𝔪 ↔ AnalyticallyIrreducible A Ahat := by
  exact hCriterion

theorem dimensionOne_weaklyQuasiComplete_iff_adicCompletion_source
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (𝔪 : Ideal A) (hMax : 𝔪 = IsLocalRing.maximalIdeal A)
    (_hDim : ringKrullDim A = 1) :
    WeaklyQuasiComplete A 𝔪 ↔
      AnalyticallyIrreducible A (AdicCompletion 𝔪 A) := by
  exact anderson_corollary2_part3_external A 𝔪 hMax _hDim

end TODO
end Run202608192034
