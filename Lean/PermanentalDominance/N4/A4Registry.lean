import PermanentalDominance.N4.A4Gap
import PermanentalDominance.N4.S4TableBridge
import PermanentalDominance.N4.CorrelationLift

/-!
# The complete registered `A₄` table

The two non-real rows are supplied by the analytic `A4Gap` certificate.  The
trivial and three-dimensional rows are the even-permutation halves of,
respectively, the trivial/sign and standard/sign-twist pairs on `S₄`.
This module joins those four facts and lifts correlation-matrix dominance to
the full positive-semidefinite cone.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.A4Registry

open CorrelationReduction CycleCoordinates ScalarAggregates
open PermutationEnumeration

local instance : Fintype (representative .a4) := Fintype.ofFinite _

private theorem v4Normal_iff_identity_or_square_one_raw :
    ∀ sigma : S4, sigma ∈ representativeCarrier .a4 →
      (sigma ∈ representativeCarrier .v4Normal ↔
        sigma = 1 ∨ sigma * sigma = 1) := by
  native_decide

private theorem v4Normal_iff_identity_or_square_one
    (sigma : representative .a4) :
    sigma.1 ∈ representativeCarrier .v4Normal ↔
      sigma.1 = 1 ∨ sigma.1 * sigma.1 = 1 := by
  apply v4Normal_iff_identity_or_square_one_raw sigma.1
  exact sigma.2

private theorem inA4PositiveClass_iff_gapPositiveClass (sigma : S4) :
    inA4PositiveClass sigma ↔ sigma ∈ A4Gap.a4PositiveClass := by
  rfl

theorem registered_omega_normalizedCoeff
    (sigma : representative .a4) :
    (rowOfIndex .a4 (⟨1, by decide⟩ : Fin 4)).normalizedCoeff sigma =
      A4Gap.omegaCharacter sigma := by
  have hv4 := v4Normal_iff_identity_or_square_one sigma
  have hpos := inA4PositiveClass_iff_gapPositiveClass sigma.1
  simp [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff,
    A4Gap.omegaCharacter, hv4, hpos, omega, A4Certificate.omega]

theorem registered_omegaConjugate_normalizedCoeff
    (sigma : representative .a4) :
    (rowOfIndex .a4 (⟨2, by decide⟩ : Fin 4)).normalizedCoeff sigma =
      A4Gap.omegaConjugateCharacter sigma := by
  have hv4 := v4Normal_iff_identity_or_square_one sigma
  have hpos := inA4PositiveClass_iff_gapPositiveClass sigma.1
  by_cases hv : sigma.1 ∈ representativeCarrier .v4Normal
  · have hcycle : sigma.1 = 1 ∨ sigma.1 * sigma.1 = 1 := hv4.mp hv
    rcases hcycle with h0 | h1
    · have hs : sigma = 1 := Subtype.ext h0
      have hone : (1 : S4) ∈ representativeCarrier .v4Normal := by
        native_decide
      simp [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff,
        A4Gap.omegaConjugateCharacter, A4Gap.omegaCharacter, hs, hone]
    · simp [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff,
        A4Gap.omegaConjugateCharacter, A4Gap.omegaCharacter, h1, hv]
  · have hcycle : ¬ (sigma.1 = 1 ∨ sigma.1 * sigma.1 = 1) := by
      intro h
      exact hv (hv4.mpr h)
    have h0 : sigma.1 ≠ 1 := fun h => hcycle (Or.inl h)
    have h1 : sigma.1 * sigma.1 ≠ 1 := fun h => hcycle (Or.inr h)
    have hs : sigma ≠ 1 := by
      intro hs
      exact hcycle (Or.inl (congrArg Subtype.val hs))
    by_cases hp : sigma.1 ∈ A4Gap.a4PositiveClass
    · have hp' : inA4PositiveClass sigma.1 := hpos.mpr hp
      simpa [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff,
        A4Gap.omegaConjugateCharacter, A4Gap.omegaCharacter, hv,
        h0, h1, hs, hp, hp', omega, A4Certificate.omega] using
          A4Certificate.star_omega.symm
    · have hp' : ¬ inA4PositiveClass sigma.1 := by
        intro h
        exact hp (hpos.mp h)
      simpa [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff,
        A4Gap.omegaConjugateCharacter, A4Gap.omegaCharacter, hv,
        h0, h1, hs, hp, hp', omega, A4Certificate.omega] using
          A4Gap.star_omega_sq.symm

theorem registered_omega_tableMatrixFunction
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (rowOfIndex .a4 (⟨1, by decide⟩ : Fin 4)).tableMatrixFunction A =
      generalizedMatrixFunction (representative .a4)
        A4Gap.omegaCharacter A := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, generalizedMatrixFunction]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [registered_omega_normalizedCoeff]

theorem registered_omegaConjugate_tableMatrixFunction
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (rowOfIndex .a4 (⟨2, by decide⟩ : Fin 4)).tableMatrixFunction A =
      generalizedMatrixFunction (representative .a4)
        A4Gap.omegaConjugateCharacter A := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, generalizedMatrixFunction]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [registered_omegaConjugate_normalizedCoeff]

private def a4CycleClass (sigma : representative .a4) : Fin 3 :=
  if sigma.1 = 1 then 0 else if sigma.1 * sigma.1 = 1 then 1 else 2

private theorem rowThree_normalizedCoeff
    (sigma : representative .a4) :
    (rowOfIndex .a4 (⟨3, by decide⟩ : Fin 4)).normalizedCoeff sigma =
      if a4CycleClass sigma = 0 then 1
      else if a4CycleClass sigma = 1 then -(1 : ℂ) / 3 else 0 := by
  simp only [rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff]
  by_cases h0 : sigma.1 = 1
  · simp [a4CycleClass, h0]
  · by_cases h1 : sigma.1 * sigma.1 = 1
    · simp [a4CycleClass, h0, h1]
    · simp [a4CycleClass, h0, h1]

private theorem a4CycleClass_q0123 : a4CycleClass A4Gap.q0123 = 0 := by native_decide
private theorem a4CycleClass_q0231 : a4CycleClass A4Gap.q0231 = 2 := by native_decide
private theorem a4CycleClass_q0312 : a4CycleClass A4Gap.q0312 = 2 := by native_decide
private theorem a4CycleClass_q1032 : a4CycleClass A4Gap.q1032 = 1 := by native_decide
private theorem a4CycleClass_q1203 : a4CycleClass A4Gap.q1203 = 2 := by native_decide
private theorem a4CycleClass_q1320 : a4CycleClass A4Gap.q1320 = 2 := by native_decide
private theorem a4CycleClass_q2013 : a4CycleClass A4Gap.q2013 = 2 := by native_decide
private theorem a4CycleClass_q2130 : a4CycleClass A4Gap.q2130 = 2 := by native_decide
private theorem a4CycleClass_q2301 : a4CycleClass A4Gap.q2301 = 1 := by native_decide
private theorem a4CycleClass_q3021 : a4CycleClass A4Gap.q3021 = 2 := by native_decide
private theorem a4CycleClass_q3102 : a4CycleClass A4Gap.q3102 = 2 := by native_decide
private theorem a4CycleClass_q3210 : a4CycleClass A4Gap.q3210 = 1 := by native_decide

attribute [local simp] a4CycleClass_q0123 a4CycleClass_q0231
  a4CycleClass_q0312 a4CycleClass_q1032 a4CycleClass_q1203
  a4CycleClass_q1320 a4CycleClass_q2013 a4CycleClass_q2130
  a4CycleClass_q2301 a4CycleClass_q3021 a4CycleClass_q3102
  a4CycleClass_q3210

set_option maxHeartbeats 3000000 in
theorem registered_trivial_correlation_expansion (a b c d e f : ℂ) :
    ((rowOfIndex .a4 (⟨0, by decide⟩ : Fin 4)).tableMatrixFunction
      (correlation a b c d e f)).re =
      1 + D a b c d e f + C a b c d e f := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum,
    ← A4Gap.allA4Rows_eq_univ, ← A4Gap.explicitA4Rows_eq_allA4Rows]
  simp [A4Gap.explicitA4Rows, A4Gap.explicitA4RowsList,
    rowOfIndex, a4Row, mkRow, IrrepDatum.normalizedCoeff]
  simp only [A4Gap.q0123, A4Gap.q0231, A4Gap.q0312, A4Gap.q1032,
    A4Gap.q1203, A4Gap.q1320, A4Gap.q2013, A4Gap.q2130,
    A4Gap.q2301, A4Gap.q3021, A4Gap.q3102, A4Gap.q3210,
    monomial_p0123, monomial_p0231, monomial_p0312, monomial_p1032,
    monomial_p1203, monomial_p1320, monomial_p2013, monomial_p2130,
    monomial_p2301, monomial_p3021, monomial_p3102, monomial_p3210]
  simp only [D, C, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  norm_num
  ring

set_option maxHeartbeats 3000000 in
theorem registered_threeDimensional_correlation_expansion
    (a b c d e f : ℂ) :
    ((rowOfIndex .a4 (⟨3, by decide⟩ : Fin 4)).tableMatrixFunction
      (correlation a b c d e f)).re =
      1 - D a b c d e f / 3 := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum,
    ← A4Gap.allA4Rows_eq_univ, ← A4Gap.explicitA4Rows_eq_allA4Rows]
  simp only [A4Gap.explicitA4Rows, A4Gap.explicitA4RowsList,
    Finset.sum_insert, Finset.sum_singleton, rowThree_normalizedCoeff]
  norm_num
  simp only [A4Gap.q0123, A4Gap.q0231, A4Gap.q0312, A4Gap.q1032,
    A4Gap.q1203, A4Gap.q1320, A4Gap.q2013, A4Gap.q2130,
    A4Gap.q2301, A4Gap.q3021, A4Gap.q3102, A4Gap.q3210,
    monomial_p0123, monomial_p0231, monomial_p0312, monomial_p1032,
    monomial_p1203, monomial_p1320, monomial_p2013, monomial_p2130,
    monomial_p2301, monomial_p3021, monomial_p3102, monomial_p3210]
  norm_num
  simp only [D, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  simp only [show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]
  norm_num
  ring

/-- The trivial `A₄` row is the half-sum of the trivial and sign rows of
`S₄`, after evaluation on the same correlation matrix. -/
theorem registered_trivial_eq_s4_average (a b c d e f : ℂ) :
    ((rowOfIndex .a4 (⟨0, by decide⟩ : Fin 4)).tableMatrixFunction
        (correlation a b c d e f)).re =
      (((rowOfIndex .s4 (⟨0, by decide⟩ : Fin 5)).tableMatrixFunction
          (correlation a b c d e f)).re +
       ((rowOfIndex .s4 (⟨1, by decide⟩ : Fin 5)).tableMatrixFunction
          (correlation a b c d e f)).re) / 2 := by
  rw [registered_trivial_correlation_expansion,
    S4TableBridge.registered_row_expansion_0,
    S4TableBridge.registered_row_expansion_1]
  simp only [permanentForm, determinantForm]
  ring

/-- The normalized three-dimensional `A₄` row is the half-sum of the
standard and sign-twisted standard rows of `S₄`. -/
theorem registered_threeDimensional_eq_s4_average (a b c d e f : ℂ) :
    ((rowOfIndex .a4 (⟨3, by decide⟩ : Fin 4)).tableMatrixFunction
        (correlation a b c d e f)).re =
      (((rowOfIndex .s4 (⟨2, by decide⟩ : Fin 5)).tableMatrixFunction
          (correlation a b c d e f)).re +
       ((rowOfIndex .s4 (⟨3, by decide⟩ : Fin 5)).tableMatrixFunction
          (correlation a b c d e f)).re) / 2 := by
  rw [registered_threeDimensional_correlation_expansion,
    S4TableBridge.registered_row_expansion_2,
    S4TableBridge.registered_row_expansion_3]
  simp only [s4Standard31, s4Standard211]
  ring

theorem registered_row_correlation_dominance (j : Fin 4)
    (a b c d e f : ℂ) (hA : IsPSD (correlation a b c d e f)) :
    ((rowOfIndex .a4 j).tableMatrixFunction (correlation a b c d e f)).re ≤
      (correlation a b c d e f).permanent.re := by
  fin_cases j
  · rw [registered_trivial_eq_s4_average]
    have h0 := S4TableBridge.registered_row_correlation_dominance
      (⟨0, by decide⟩ : Fin 5) a b c d e f hA
    have h1 := S4TableBridge.registered_row_correlation_dominance
      (⟨1, by decide⟩ : Fin 5) a b c d e f hA
    linarith
  · rw [registered_omega_tableMatrixFunction]
    exact sub_nonneg.mp (A4Gap.a4Omega_generalized_gap_nonneg hA)
  · rw [registered_omegaConjugate_tableMatrixFunction]
    exact sub_nonneg.mp (A4Gap.a4OmegaConjugate_generalized_gap_nonneg hA)
  · rw [registered_threeDimensional_eq_s4_average]
    have h2 := S4TableBridge.registered_row_correlation_dominance
      (⟨2, by decide⟩ : Fin 5) a b c d e f hA
    have h3 := S4TableBridge.registered_row_correlation_dominance
      (⟨3, by decide⟩ : Fin 5) a b c d e f hA
    linarith

/-- All four registered `A₄` rows are dominated on the full PSD cone. -/
theorem registered_row_tableDominates (j : Fin 4) :
    (rowOfIndex .a4 j).TableDominates := by
  apply CorrelationLift.tableDominates_of_correlation
  intro a b c d e f hA
  exact sub_nonneg.mpr (registered_row_correlation_dominance j a b c d e f hA)

/-- Registry-shaped interface for the `A₄` component of final assembly. -/
theorem a4_representative_dominance_registry
    (i : Fin (rowCount .a4)) :
    (rowOfIndex .a4 i).TableDominates :=
  registered_row_tableDominates i

end PermanentalDominance.N4.A4Registry
