import PermanentalDominance.N4.CharacterTables
import PermanentalDominance.N4.PermutationEnumeration
import PermanentalDominance.N4.S4Cases

/-!
# The registered `S₄` table and the scalar certificates

This file is the finite bridge which was deliberately absent from the analytic
modules.  It unfolds each of the five registered character rows on an explicit
enumeration of `S₄`, and then invokes the corresponding scalar certificate.
-/

noncomputable section

open scoped BigOperators

namespace PermanentalDominance.N4.S4TableBridge

open CorrelationReduction CycleCoordinates ScalarAggregates
open PermutationEnumeration

local instance : Fintype (representative .s4) := Fintype.ofFinite _

theorem mem_s4_representative (sigma : S4) : sigma ∈ representative .s4 := by
  change sigma ∈ (Finset.univ : Finset S4)
  simp

def toS4Embedding : S4 ↪ representative .s4 where
  toFun sigma := ⟨sigma, mem_s4_representative sigma⟩
  inj' _ _ h := Subtype.ext_iff.mp h

def allS4Rows : Finset (representative .s4) :=
  allPerms.map toS4Embedding

theorem allS4Rows_eq_univ : allS4Rows = Finset.univ := by
  rw [allS4Rows, allPerms_eq_univ]
  ext sigma
  simp [toS4Embedding]

/-- The real part of the registered row, in the order used by
`CharacterTables.rowOfIndex`. -/
def registeredRowReal (j : Fin 5) (t d c f : ℝ) : ℝ :=
  if j = 0 then permanentForm t d c f
  else if j = 1 then determinantForm t d c f
  else if j = 2 then s4Standard31 t d c f
  else if j = 3 then s4Standard211 t d c f
  else s4Standard22 t d c f

private def explicitRowSum (row : IrrepDatum (representative .s4))
    (a b c d e f : ℂ) : ℂ :=
  ∑ sigma in allS4Rows,
    row.normalizedCoeff sigma * permutationMonomial (correlation a b c d e f) sigma.1

private theorem tableMatrixFunction_eq_explicitRowSum
    (row : IrrepDatum (representative .s4)) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      explicitRowSum row a b c d e f := by
  rw [row.tableMatrixFunction_eq_sum, ← allS4Rows_eq_univ]
  rfl

private def coeffAt (row : IrrepDatum (representative .s4)) (sigma : S4) : ℂ :=
  row.normalizedCoeff (toS4Embedding sigma)

private def cycleCode (sigma : S4) : Fin 5 :=
  s4Class sigma

private def cycleCoeff (j k : Fin 5) : ℂ :=
  if j = 0 then 1
  else if j = 1 then if k = 1 ∨ k = 4 then -1 else 1
  else if j = 2 then if k = 0 then 1 else if k = 1 then (1 : ℂ) / 3
    else if k = 2 ∨ k = 4 then (-1 : ℂ) / 3 else 0
  else if j = 3 then if k = 0 then 1 else if k = 1 ∨ k = 2 then (-1 : ℂ) / 3
    else if k = 4 then (1 : ℂ) / 3 else 0
  else if k = 0 then 1 else if k = 2 then 1 else if k = 3 then (-1 : ℂ) / 2 else 0

private theorem coeffAt_row_eq_cycleCoeff (j : Fin 5) (sigma : S4) :
    coeffAt (rowOfIndex .s4 j) sigma = cycleCoeff j (cycleCode sigma) := by
  generalize hclass : s4Class sigma = k
  fin_cases k <;>
    fin_cases j <;>
      simp [coeffAt, toS4Embedding, IrrepDatum.normalizedCoeff, rowOfIndex,
        s4Row, mkRow, cycleCode, cycleCoeff, hclass]

private theorem cycleCode_p0123 : cycleCode p0123 = 0 := by native_decide
private theorem cycleCode_p1023 : cycleCode p1023 = 1 := by native_decide
private theorem cycleCode_p2103 : cycleCode p2103 = 1 := by native_decide
private theorem cycleCode_p3120 : cycleCode p3120 = 1 := by native_decide
private theorem cycleCode_p0213 : cycleCode p0213 = 1 := by native_decide
private theorem cycleCode_p0321 : cycleCode p0321 = 1 := by native_decide
private theorem cycleCode_p0132 : cycleCode p0132 = 1 := by native_decide
private theorem cycleCode_p1032 : cycleCode p1032 = 2 := by native_decide
private theorem cycleCode_p2301 : cycleCode p2301 = 2 := by native_decide
private theorem cycleCode_p3210 : cycleCode p3210 = 2 := by native_decide
private theorem cycleCode_p1203 : cycleCode p1203 = 3 := by native_decide
private theorem cycleCode_p2013 : cycleCode p2013 = 3 := by native_decide
private theorem cycleCode_p1320 : cycleCode p1320 = 3 := by native_decide
private theorem cycleCode_p3021 : cycleCode p3021 = 3 := by native_decide
private theorem cycleCode_p2130 : cycleCode p2130 = 3 := by native_decide
private theorem cycleCode_p3102 : cycleCode p3102 = 3 := by native_decide
private theorem cycleCode_p0231 : cycleCode p0231 = 3 := by native_decide
private theorem cycleCode_p0312 : cycleCode p0312 = 3 := by native_decide
private theorem cycleCode_p1230 : cycleCode p1230 = 4 := by native_decide
private theorem cycleCode_p1302 : cycleCode p1302 = 4 := by native_decide
private theorem cycleCode_p2310 : cycleCode p2310 = 4 := by native_decide
private theorem cycleCode_p2031 : cycleCode p2031 = 4 := by native_decide
private theorem cycleCode_p3201 : cycleCode p3201 = 4 := by native_decide
private theorem cycleCode_p3012 : cycleCode p3012 = 4 := by native_decide

attribute [local simp] coeffAt_row_eq_cycleCoeff
  cycleCode_p0123 cycleCode_p1023 cycleCode_p2103 cycleCode_p3120
  cycleCode_p0213 cycleCode_p0321 cycleCode_p0132
  cycleCode_p1032 cycleCode_p2301 cycleCode_p3210
  cycleCode_p1203 cycleCode_p2013 cycleCode_p1320 cycleCode_p3021
  cycleCode_p2130 cycleCode_p3102 cycleCode_p0231 cycleCode_p0312
  cycleCode_p1230 cycleCode_p1302 cycleCode_p2310 cycleCode_p2031
  cycleCode_p3201 cycleCode_p3012

private def expandedRowSum (row : IrrepDatum (representative .s4))
    (a b c d e f : ℂ) : ℂ :=
  coeffAt row p0123 +
  coeffAt row p1023 * (a * star a) +
  coeffAt row p2103 * (b * star b) +
  coeffAt row p3120 * (c * star c) +
  coeffAt row p0213 * (d * star d) +
  coeffAt row p0321 * (e * star e) +
  coeffAt row p0132 * (f * star f) +
  coeffAt row p1032 * (a * star a * f * star f) +
  coeffAt row p2301 * (b * e * star b * star e) +
  coeffAt row p3210 * (c * d * star d * star c) +
  coeffAt row p1203 * (a * d * star b) +
  coeffAt row p2013 * (b * star a * star d) +
  coeffAt row p1320 * (a * e * star c) +
  coeffAt row p3021 * (c * star a * star e) +
  coeffAt row p2130 * (b * f * star c) +
  coeffAt row p3102 * (c * star b * star f) +
  coeffAt row p0231 * (d * f * star e) +
  coeffAt row p0312 * (e * star d * star f) +
  coeffAt row p1230 * (a * d * f * star c) +
  coeffAt row p1302 * (a * e * star b * star f) +
  coeffAt row p2310 * (b * e * star d * star c) +
  coeffAt row p2031 * (b * star a * f * star e) +
  coeffAt row p3201 * (c * d * star b * star e) +
  coeffAt row p3012 * (c * star a * star d * star f)

private def transpositionSum (a b c d e f : ℂ) : ℂ :=
  a * star a + b * star b + c * star c +
    d * star d + e * star e + f * star f

private def doubleTranspositionSum (a b c d e f : ℂ) : ℂ :=
  a * star a * f * star f + b * e * star b * star e +
    c * d * star d * star c

private def threeCycleSum (a b c d e f : ℂ) : ℂ :=
  a * d * star b + b * star a * star d +
  a * e * star c + c * star a * star e +
  b * f * star c + c * star b * star f +
  d * f * star e + e * star d * star f

private def fourCycleSum (a b c d e f : ℂ) : ℂ :=
  a * d * f * star c + a * e * star b * star f +
  b * e * star d * star c + b * star a * f * star e +
  c * d * star b * star e + c * star a * star d * star f

private def classExpandedRowSum (j : Fin 5) (a b c d e f : ℂ) : ℂ :=
  cycleCoeff j 0 +
    cycleCoeff j 1 * transpositionSum a b c d e f +
    cycleCoeff j 2 * doubleTranspositionSum a b c d e f +
    cycleCoeff j 3 * threeCycleSum a b c d e f +
    cycleCoeff j 4 * fourCycleSum a b c d e f

private theorem expandedRowSum_eq_classExpandedRowSum (j : Fin 5)
    (a b c d e f : ℂ) :
    expandedRowSum (rowOfIndex .s4 j) a b c d e f =
      classExpandedRowSum j a b c d e f := by
  simp only [expandedRowSum, classExpandedRowSum, transpositionSum,
    doubleTranspositionSum, threeCycleSum, fourCycleSum,
    coeffAt_row_eq_cycleCoeff,
    cycleCode_p0123, cycleCode_p1023, cycleCode_p2103, cycleCode_p3120,
    cycleCode_p0213, cycleCode_p0321, cycleCode_p0132,
    cycleCode_p1032, cycleCode_p2301, cycleCode_p3210,
    cycleCode_p1203, cycleCode_p2013, cycleCode_p1320, cycleCode_p3021,
    cycleCode_p2130, cycleCode_p3102, cycleCode_p0231, cycleCode_p0312,
    cycleCode_p1230, cycleCode_p1302, cycleCode_p2310, cycleCode_p2031,
    cycleCode_p3201, cycleCode_p3012]
  ring

private theorem explicitRowSum_eq_expandedRowSum
    (row : IrrepDatum (representative .s4)) (a b c d e f : ℂ) :
    explicitRowSum row a b c d e f = expandedRowSum row a b c d e f := by
  simp [explicitRowSum, expandedRowSum, coeffAt, allS4Rows, allPerms,
    allPermsList, toS4Embedding,
    monomial_p0123, monomial_p0132, monomial_p0213, monomial_p0231,
    monomial_p0312, monomial_p0321, monomial_p1023, monomial_p1032,
    monomial_p1203, monomial_p1230, monomial_p1302, monomial_p1320,
    monomial_p2013, monomial_p2031, monomial_p2103, monomial_p2130,
    monomial_p2301, monomial_p2310, monomial_p3012, monomial_p3021,
    monomial_p3102, monomial_p3120, monomial_p3201, monomial_p3210]
  ring


set_option maxHeartbeats 2000000 in
theorem registered_row_expansion_0 (a b c d e f : ℂ) :
    ((rowOfIndex .s4 (⟨0, by decide⟩ : Fin 5)).tableMatrixFunction
      (correlation a b c d e f)).re =
      permanentForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_explicitRowSum, explicitRowSum_eq_expandedRowSum,
    expandedRowSum_eq_classExpandedRowSum]
  simp [classExpandedRowSum, cycleCoeff, Fin.mk.injEq]
  simp only [transpositionSum, doubleTranspositionSum, threeCycleSum,
    fourCycleSum, permanentForm, T, D, C, F, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
theorem registered_row_expansion_1 (a b c d e f : ℂ) :
    ((rowOfIndex .s4 (⟨1, by decide⟩ : Fin 5)).tableMatrixFunction
      (correlation a b c d e f)).re =
      determinantForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_explicitRowSum, explicitRowSum_eq_expandedRowSum,
    expandedRowSum_eq_classExpandedRowSum]
  simp [classExpandedRowSum, cycleCoeff, Fin.mk.injEq]
  simp only [transpositionSum, doubleTranspositionSum, threeCycleSum,
    fourCycleSum, determinantForm, T, D, C, F, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
theorem registered_row_expansion_2 (a b c d e f : ℂ) :
    ((rowOfIndex .s4 (⟨2, by decide⟩ : Fin 5)).tableMatrixFunction
      (correlation a b c d e f)).re =
      s4Standard31 (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_explicitRowSum, explicitRowSum_eq_expandedRowSum,
    expandedRowSum_eq_classExpandedRowSum]
  simp [classExpandedRowSum, cycleCoeff, Fin.mk.injEq]
  simp only [transpositionSum, doubleTranspositionSum, threeCycleSum,
    fourCycleSum, s4Standard31, T, D, C, F, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
theorem registered_row_expansion_3 (a b c d e f : ℂ) :
    ((rowOfIndex .s4 (⟨3, by decide⟩ : Fin 5)).tableMatrixFunction
      (correlation a b c d e f)).re =
      s4Standard211 (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_explicitRowSum, explicitRowSum_eq_expandedRowSum,
    expandedRowSum_eq_classExpandedRowSum]
  simp [classExpandedRowSum, cycleCoeff, Fin.mk.injEq]
  simp only [transpositionSum, doubleTranspositionSum, threeCycleSum,
    fourCycleSum, s4Standard211, T, D, C, F, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
theorem registered_row_expansion_4 (a b c d e f : ℂ) :
    ((rowOfIndex .s4 (⟨4, by decide⟩ : Fin 5)).tableMatrixFunction
      (correlation a b c d e f)).re =
      s4Standard22 (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_explicitRowSum, explicitRowSum_eq_expandedRowSum,
    expandedRowSum_eq_classExpandedRowSum]
  simp [classExpandedRowSum, cycleCoeff, Fin.mk.injEq]
  simp only [transpositionSum, doubleTranspositionSum, threeCycleSum,
    fourCycleSum, s4Standard22, T, D, C, F, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  norm_num
  ring

theorem registered_row_expansion (j : Fin 5) (a b c d e f : ℂ) :
    ((rowOfIndex .s4 j).tableMatrixFunction (correlation a b c d e f)).re =
      registeredRowReal j (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  fin_cases j
  · simpa [registeredRowReal] using registered_row_expansion_0 a b c d e f
  · simpa [registeredRowReal] using registered_row_expansion_1 a b c d e f
  · simpa [registeredRowReal] using registered_row_expansion_2 a b c d e f
  · simpa [registeredRowReal] using registered_row_expansion_3 a b c d e f
  · simpa [registeredRowReal] using registered_row_expansion_4 a b c d e f

/-- All five registered `S₄` rows are dominated on normalized correlation
matrices. -/
theorem registered_row_correlation_dominance (j : Fin 5) (a b c d e f : ℂ)
    (hA : IsPSD (correlation a b c d e f)) :
    ((rowOfIndex .s4 j).tableMatrixFunction (correlation a b c d e f)).re ≤
      (correlation a b c d e f).permanent.re := by
  rw [registered_row_expansion, PermutationEnumeration.permanent_expansion]
  fin_cases j
  · exact le_rfl
  · exact S4Cases.correlation_sign hA
  · exact S4Cases.correlation_standard31 hA
  · exact S4Cases.correlation_standard211 hA
  · exact S4Cases.correlation_standard22 hA

/-- Coordinate-free form of the preceding theorem on the normalized
positive-semidefinite cone. -/
theorem registered_row_diagonal_one_dominance (j : Fin 5)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsPSD A)
    (hdiag : ∀ i : Fin 4, A i i = 1) :
    ((rowOfIndex .s4 j).tableMatrixFunction A).re ≤ A.permanent.re := by
  rw [CorrelationReduction.eq_correlation_of_diagonal_one hA hdiag]
  exact registered_row_correlation_dominance j _ _ _ _ _ _
    (CorrelationReduction.diagonal_one_correlation_psd hA hdiag)

end PermanentalDominance.N4.S4TableBridge
