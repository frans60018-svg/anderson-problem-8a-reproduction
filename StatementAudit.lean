import StrictReproduction

/-!
This file independently restates both definitions and the final proposition
from the published `Challenge.lean`. Successful elaboration verifies that the
canonical theorem proves the exact local-ring statement, with the maximal ideal
built into both definitions.
-/

namespace StatementAudit

variable (R : Type*) [CommRing R] [IsLocalRing R]

def ChallengeIsQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A →
    ∀ (k : ℕ), ∃ s,
      A s ≤ (⨅ n, A n) ⊔ (IsLocalRing.maximalIdeal R) ^ k

def ChallengeIsWeaklyQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A → (⨅ n, A n) = ⊥ →
    ∀ (k : ℕ), ∃ s, A s ≤ (IsLocalRing.maximalIdeal R) ^ k

theorem challenge_quasiComplete_iff :
    ChallengeIsQuasiComplete R ↔ IsQuasiComplete R := by
  rfl

theorem challenge_weaklyQuasiComplete_iff :
    ChallengeIsWeaklyQuasiComplete R ↔ IsWeaklyQuasiComplete R := by
  rfl

theorem exactChallengeStatement :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R),
      ChallengeIsWeaklyQuasiComplete R ∧
        ¬ ChallengeIsQuasiComplete R := by
  rcases Run202608192034.andersonProblem8a with
    ⟨R, instCommRing, instLocal, instNoetherian, hWeak, hNotQuasi⟩
  exact
    ⟨R, instCommRing, instLocal, instNoetherian,
      (challenge_weaklyQuasiComplete_iff R).2 hWeak,
      fun hQuasi => hNotQuasi ((challenge_quasiComplete_iff R).1 hQuasi)⟩

end StatementAudit
