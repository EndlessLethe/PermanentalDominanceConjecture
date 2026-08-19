import PermanentalDominance.N4.RepresentativeDominanceRegistry
import PermanentalDominance.N4.RepresentativeCompletenessRegistry

/-!
# Normalized permanental dominance in dimension four

The analytic registry proves dominance for all thirty-seven registered rows
of the eleven representative subgroup types.  The completeness registry
identifies every simple complex representation of every subgroup of `S₄`
with one of those rows after conjugation.  Combining the two registries gives
the normalized `n = 4` theorem with no remaining hypotheses beyond positive
semidefiniteness and simplicity.
-/

noncomputable section

open CategoryTheory
open scoped ComplexOrder

namespace PermanentalDominance.N4

/-- The character row of every simple representation of every subgroup of
`S₄` is dominated by the permanent on the full positive-semidefinite cone. -/
theorem simple_fdRep_tableDominates
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V] :
    (FinalAssembly.fdRepRow V).TableDominates :=
  FinalAssembly.simple_fdRep_tableDominates_of_registries
    RepresentativeDominanceRegistry.all_representative_rows
    RepresentativeCompletenessRegistry.all_simple_representations H V

/-- Normalized permanental dominance for `n = 4`, for an arbitrary subgroup
and an arbitrary irreducible finite-dimensional complex representation. -/
theorem normalized_permanental_dominance_n4
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V]
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) :
    (normalizedMatrixFunction H V.character
      (Module.finrank ℂ V : ℂ) A).re ≤ A.permanent.re := by
  exact FinalAssembly.simple_fdRep_dominatesAt_of_registries
    RepresentativeDominanceRegistry.all_representative_rows
    RepresentativeCompletenessRegistry.all_simple_representations
    H V hA

/-- Reality of both sides together with normalized permanental dominance. -/
theorem normalized_permanental_dominance_n4_real
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V]
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) :
    (normalizedMatrixFunction H V.character
        (Module.finrank ℂ V : ℂ) A).im = 0 ∧
      A.permanent.im = 0 ∧
      (normalizedMatrixFunction H V.character
        (Module.finrank ℂ V : ℂ) A).re ≤ A.permanent.re :=
  FinalAssembly.simple_fdRep_real_dominance_of_registries
    RepresentativeDominanceRegistry.all_representative_rows
    RepresentativeCompletenessRegistry.all_simple_representations
    H V hA

end PermanentalDominance.N4
