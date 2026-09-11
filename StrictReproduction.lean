import Anderson.Main

/-!
# Strict reproduction of Anderson Problem 8(a)

This module is intentionally independent of the historical Archon track. Its
import closure contains only the fully internalized `Anderson` proof modules.
-/

namespace Run202608192034

/--
There exists a Noetherian local ring which is weakly quasi-complete but not
quasi-complete. Both notions use the unique maximal ideal supplied by the
`IsLocalRing` instance.
-/
theorem andersonProblem8a :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R),
      IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R := by
  exact main_theorem

end Run202608192034
