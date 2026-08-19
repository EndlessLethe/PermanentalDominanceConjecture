import PermanentalDominance.N4.FinalAssembly
import PermanentalDominance.N4.LowOrderRegistry
import PermanentalDominance.N4.C4TableBridge
import PermanentalDominance.N4.D8TableBridge
import PermanentalDominance.N4.A4Registry
import PermanentalDominance.N4.S4TableBridge

/-!
# Analytic dominance registry for the eleven representative subgroups

The case modules prove the normalized inequalities on correlation matrices.
`CorrelationLift` supplies the zero-diagonal and positive-diagonal scaling
argument, so the theorem below certifies every one of the thirty-seven rows
on the entire positive-semidefinite cone.
-/

noncomputable section

open scoped ComplexOrder

namespace PermanentalDominance.N4.RepresentativeDominanceRegistry

open CorrelationReduction

private theorem c4_tableDominates (j : Fin 4) :
    (rowOfIndex .c4 j).TableDominates := by
  apply CorrelationLift.tableDominates_of_correlation
  intro a b c d e f hA
  exact sub_nonneg.mpr
    (C4TableBridge.registered_row_correlation_dominance j a b c d e f hA)

private theorem d8_tableDominates (j : Fin 5) :
    (rowOfIndex .d8 j).TableDominates := by
  apply CorrelationLift.tableDominates_of_correlation
  intro a b c d e f hA
  exact sub_nonneg.mpr
    (D8TableBridge.registered_row_correlation_dominance j a b c d e f hA)

private theorem s4_tableDominates (j : Fin 5) :
    (rowOfIndex .s4 j).TableDominates := by
  apply CorrelationLift.tableDominates_of_correlation
  intro a b c d e f hA
  exact sub_nonneg.mpr
    (S4TableBridge.registered_row_correlation_dominance j a b c d e f hA)

/-- Every registered row for every representative subgroup of `S₄` satisfies
normalized permanental dominance on the full positive-semidefinite cone. -/
theorem all_representative_rows : FinalAssembly.RepresentativeDominanceRegistry := by
  intro k j
  cases k with
  | trivial =>
      exact LowOrderRegistry.tableDominates .trivial (Or.inl rfl) j
  | c2Transposition =>
      exact LowOrderRegistry.tableDominates .c2Transposition
        (Or.inr (Or.inl rfl)) j
  | c2DoubleTransposition =>
      exact LowOrderRegistry.tableDominates .c2DoubleTransposition
        (Or.inr (Or.inr (Or.inl rfl))) j
  | c3 =>
      exact LowOrderRegistry.tableDominates .c3
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) j
  | c4 =>
      exact c4_tableDominates j
  | v4Normal =>
      exact LowOrderRegistry.tableDominates .v4Normal
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) j
  | v4Disjoint =>
      exact LowOrderRegistry.tableDominates .v4Disjoint
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) j
  | s3 =>
      exact LowOrderRegistry.tableDominates .s3
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) j
  | d8 =>
      exact d8_tableDominates j
  | a4 =>
      exact A4Registry.a4_representative_dominance_registry j
  | s4 =>
      exact s4_tableDominates j

/-- List-shaped version used by finite table completeness statements. -/
theorem subgroupTable_certified (k : SubgroupKind) :
    IrrepDatum.TableCertified (subgroupTable k) := by
  intro row hrow
  rcases mem_subgroupTable_iff.mp hrow with ⟨j, rfl⟩
  exact all_representative_rows k j

end PermanentalDominance.N4.RepresentativeDominanceRegistry
