import PermanentalDominance.N4.CompletenessTransport
import PermanentalDominance.N4.AbelianCompleteness
import PermanentalDominance.N4.A4Realization
import PermanentalDominance.N4.S4Realization

/-!
# Character completeness registry on the representative subgroups

This file turns the concrete classification of simple representations into
the row equality required by `CompletenessTransport`.  The only general input
is that isomorphic finite-dimensional representations have the same character
and dimension.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4.RepresentativeCompletenessRegistry

open CompletenessTransport

private theorem rowZero_of_iso (k : SubgroupKind)
    (V : FDRep ℂ (representative k))
    (iV : V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative k))) :
    FinalAssembly.fdRepRow V =
      rowOfIndex k ⟨0, by cases k <;> decide⟩ := by
  apply fdRepRow_eq_of_iso iV
  · exact rowZero_character k
  · simpa using rowZero_degree k

theorem trivial_complete (V : FDRep ℂ (representative .trivial)) [Simple V] :
    ∃ i : Fin 1, FinalAssembly.fdRepRow V = rowOfIndex .trivial i := by
  rcases trivial_simple_complete V with ⟨iV⟩
  exact ⟨⟨0, by decide⟩, rowZero_of_iso .trivial V iV⟩

theorem c2Transposition_complete
    (V : FDRep ℂ (representative .c2Transposition)) [Simple V] :
    ∃ i : Fin 2, FinalAssembly.fdRepRow V = rowOfIndex .c2Transposition i := by
  rcases c2Transposition_simple_complete V with ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .c2Transposition V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _
      c2Transposition_rowOne_character ?_⟩
    simpa using c2Transposition_rowOne_degree

theorem c2DoubleTransposition_complete
    (V : FDRep ℂ (representative .c2DoubleTransposition)) [Simple V] :
    ∃ i : Fin 2, FinalAssembly.fdRepRow V =
      rowOfIndex .c2DoubleTransposition i := by
  rcases c2DoubleTransposition_simple_complete V with ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .c2DoubleTransposition V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _
      c2DoubleTransposition_rowOne_character ?_⟩
    simpa using c2DoubleTransposition_rowOne_degree

theorem c3_complete (V : FDRep ℂ (representative .c3)) [Simple V] :
    ∃ i : Fin 3, FinalAssembly.fdRepRow V = rowOfIndex .c3 i := by
  rcases c3_simple_complete V with ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .c3 V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _ c3_rowOne_character ?_⟩
    simpa using c3_rowOne_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨2, by decide⟩, fdRepRow_eq_of_iso iV _ c3_rowTwo_character ?_⟩
    simpa using c3_rowTwo_degree

theorem c4_complete (V : FDRep ℂ (representative .c4)) [Simple V] :
    ∃ i : Fin 4, FinalAssembly.fdRepRow V = rowOfIndex .c4 i := by
  rcases c4_simple_complete V with ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .c4 V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _ c4_rowOne_character ?_⟩
    simpa using c4_rowOne_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨2, by decide⟩, fdRepRow_eq_of_iso iV _ c4_rowTwo_character ?_⟩
    simpa using c4_rowTwo_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨3, by decide⟩, fdRepRow_eq_of_iso iV _ c4_rowThree_character ?_⟩
    simpa using c4_rowThree_degree

theorem v4Normal_complete (V : FDRep ℂ (representative .v4Normal)) [Simple V] :
    ∃ i : Fin 4, FinalAssembly.fdRepRow V = rowOfIndex .v4Normal i := by
  rcases v4Normal_simple_complete V with ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .v4Normal V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Normal_rowOne_character ?_⟩
    simpa using v4Normal_rowOne_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨2, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Normal_rowTwo_character ?_⟩
    simpa using v4Normal_rowTwo_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨3, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Normal_rowThree_character ?_⟩
    simpa using v4Normal_rowThree_degree

theorem v4Disjoint_complete (V : FDRep ℂ (representative .v4Disjoint)) [Simple V] :
    ∃ i : Fin 4, FinalAssembly.fdRepRow V = rowOfIndex .v4Disjoint i := by
  rcases v4Disjoint_simple_complete V with ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩ | ⟨iV⟩
  · rcases iV with ⟨iV⟩
    exact ⟨⟨0, by decide⟩, rowZero_of_iso .v4Disjoint V iV⟩
  · rcases iV with ⟨iV⟩
    refine ⟨⟨1, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Disjoint_rowOne_character ?_⟩
    simpa using v4Disjoint_rowOne_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨2, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Disjoint_rowTwo_character ?_⟩
    simpa using v4Disjoint_rowTwo_degree
  · rcases iV with ⟨iV⟩
    refine ⟨⟨3, by decide⟩, fdRepRow_eq_of_iso iV _
      v4Disjoint_rowThree_character ?_⟩
    simpa using v4Disjoint_rowThree_degree

private theorem s3RegisteredIrrep_character (i : Fin 3) :
    (rowOfIndex .s3 i).coeff = (s3RegisteredIrrep i).character := by
  fin_cases i
  · simpa [s3RegisteredIrrep] using rowZero_character .s3
  · simpa [s3RegisteredIrrep] using s3_sign_character
  · simpa [s3RegisteredIrrep] using s3_standard_character

private theorem s3RegisteredIrrep_degree (i : Fin 3) :
    (rowOfIndex .s3 i).degree = (Module.finrank ℂ (s3RegisteredIrrep i) : ℂ) := by
  fin_cases i
  · simpa [s3RegisteredIrrep] using rowZero_degree .s3
  · simpa [s3RegisteredIrrep] using s3_sign_degree
  · simpa [s3RegisteredIrrep] using s3_standard_degree

theorem s3_complete (V : FDRep ℂ (representative .s3)) [Simple V] :
    ∃ i : Fin 3, FinalAssembly.fdRepRow V = rowOfIndex .s3 i := by
  rcases s3_simple_complete V with ⟨i, ⟨iV⟩⟩
  exact ⟨i, fdRepRow_eq_of_iso iV _
    (s3RegisteredIrrep_character i) (s3RegisteredIrrep_degree i)⟩

private theorem d8RegisteredIrrep_character (i : Fin 5) :
    (rowOfIndex .d8 i).coeff = (d8RegisteredIrrep i).character := by
  fin_cases i
  · simpa [d8RegisteredIrrep] using rowZero_character .d8
  · simpa [d8RegisteredIrrep] using d8_linear1_character
  · simpa [d8RegisteredIrrep] using d8_linear2_character
  · simpa [d8RegisteredIrrep] using d8_linear3_character
  · simpa [d8RegisteredIrrep] using d8_standard_character

private theorem d8RegisteredIrrep_degree (i : Fin 5) :
    (rowOfIndex .d8 i).degree = (Module.finrank ℂ (d8RegisteredIrrep i) : ℂ) := by
  fin_cases i
  · simpa [d8RegisteredIrrep] using rowZero_degree .d8
  · simpa [d8RegisteredIrrep] using d8_linear1_degree
  · simpa [d8RegisteredIrrep] using d8_linear2_degree
  · simpa [d8RegisteredIrrep] using d8_linear3_degree
  · simpa [d8RegisteredIrrep] using d8_standard_degree

theorem d8_complete (V : FDRep ℂ (representative .d8)) [Simple V] :
    ∃ i : Fin 5, FinalAssembly.fdRepRow V = rowOfIndex .d8 i := by
  rcases d8_simple_complete V with ⟨i, ⟨iV⟩⟩
  exact ⟨i, fdRepRow_eq_of_iso iV _
    (d8RegisteredIrrep_character i) (d8RegisteredIrrep_degree i)⟩

theorem a4_complete (V : FDRep ℂ (representative .a4)) [Simple V] :
    ∃ i : Fin 4, FinalAssembly.fdRepRow V = rowOfIndex .a4 i := by
  rcases a4_simple_complete V with ⟨i, ⟨iV⟩⟩
  exact ⟨i, fdRepRow_eq_of_iso iV _
    (a4RegisteredIrrep_character i) (a4RegisteredIrrep_degree i)⟩

theorem s4_complete (V : FDRep ℂ (representative .s4)) [Simple V] :
    ∃ i : Fin 5, FinalAssembly.fdRepRow V = rowOfIndex .s4 i := by
  rcases s4_simple_complete V with ⟨i, ⟨iV⟩⟩
  exact ⟨i, fdRepRow_eq_of_iso iV _
    (s4RegisteredIrrep_character i) (s4RegisteredIrrep_degree i)⟩

/-- Every simple representation of each of the eleven fixed representative
subgroups occurs in its registered character-table row family. -/
theorem all_representative_simple_rows :
    CompletenessTransport.RepresentativeSimpleCompleteness := by
  intro k V hsimple
  letI : Simple V := hsimple
  cases k with
  | trivial => exact trivial_complete V
  | c2Transposition => exact c2Transposition_complete V
  | c2DoubleTransposition => exact c2DoubleTransposition_complete V
  | c3 => exact c3_complete V
  | c4 => exact c4_complete V
  | v4Normal => exact v4Normal_complete V
  | v4Disjoint => exact v4Disjoint_complete V
  | s3 => exact s3_complete V
  | d8 => exact d8_complete V
  | a4 => exact a4_complete V
  | s4 => exact s4_complete V

/-- Conjugation-aware completeness for arbitrary subgroups of `S₄`. -/
theorem all_simple_representations :
    FinalAssembly.SimpleRepresentativeCompleteness :=
  CompletenessTransport.simpleRepresentativeCompleteness_of_representatives
    all_representative_simple_rows

/-- Backward-compatible descriptive alias for the complete arbitrary-subgroup
registry. -/
theorem simple_representative_completeness :
    FinalAssembly.SimpleRepresentativeCompleteness :=
  all_simple_representations

end PermanentalDominance.N4.RepresentativeCompletenessRegistry
