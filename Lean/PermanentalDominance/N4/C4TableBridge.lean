import PermanentalDominance.N4.CharacterTables
import PermanentalDominance.N4.C4Cases
import PermanentalDominance.N4.PermutationEnumeration
import PermanentalDominance.N4.FischerContractions
import PermanentalDominance.N4.S4Cases

/-!
# Expansion of the four registered `C₄` rows

The carrier is enumerated by `attach`, so the finite proof never attempts
to execute the noncomputable `Fintype.ofFinite` instance on the abstract
subgroup.  Four shallow monomial lemmas give the exact scalar rows.
-/

noncomputable section

open scoped BigOperators

namespace PermanentalDominance.N4.C4TableBridge

open Complex CorrelationReduction CycleCoordinates ScalarAggregates
open PermutationEnumeration FischerContractions

abbrev HC4 : Subgroup S4 := representative .c4

local instance : Fintype HC4 := Fintype.ofFinite _

def allC4Rows : Finset HC4 := (representativeCarrier .c4).attach

theorem allC4Rows_eq_univ : allC4Rows = Finset.univ := by
  ext sigma
  simp only [Finset.mem_univ, iff_true]
  exact Finset.mem_attach _ _

def q0123 : HC4 :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .c4; native_decide⟩
def q1230 : HC4 :=
  ⟨p1230, by change p1230 ∈ representativeCarrier .c4; native_decide⟩
def q2301 : HC4 :=
  ⟨p2301, by change p2301 ∈ representativeCarrier .c4; native_decide⟩
def q3012 : HC4 :=
  ⟨p3012, by change p3012 ∈ representativeCarrier .c4; native_decide⟩

def explicitC4RowsList : Multiset HC4 := [q0123, q1230, q2301, q3012]

theorem explicitC4RowsList_nodup : explicitC4RowsList.Nodup := by native_decide

def explicitC4Rows : Finset HC4 :=
  ⟨explicitC4RowsList, explicitC4RowsList_nodup⟩

theorem explicitC4Rows_eq_allC4Rows : explicitC4Rows = allC4Rows := by
  native_decide

private theorem p0123_eq_one : p0123 = 1 := by native_decide
private theorem p1230_eq_cycle0123 : p1230 = ConcretePerm.cycle0123 := by
  native_decide
private theorem p2301_eq_cycle0123_sq : p2301 = ConcretePerm.cycle0123 ^ 2 := by
  native_decide
private theorem p3012_eq_cycle0123_cube : p3012 = ConcretePerm.cycle0123 ^ 3 := by
  native_decide

def cycleMonomial (a b c d e f : ℂ) : ℂ := a * d * f * star c

def halfTurnMonomial (b e : ℂ) : ℝ := normSq b * normSq e

private theorem tableMatrixFunction_eq_explicit
    (row : IrrepDatum HC4) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      ∑ sigma in explicitC4Rows,
        row.normalizedCoeff sigma *
          permutationMonomial (correlation a b c d e f) sigma.1 := by
  rw [row.tableMatrixFunction_eq_sum, ← allC4Rows_eq_univ,
    ← explicitC4Rows_eq_allC4Rows]

private def expandedRowSum (row : IrrepDatum HC4) (a b c d e f : ℂ) : ℂ :=
  row.normalizedCoeff q0123 +
    row.normalizedCoeff q1230 * (a * d * f * star c) +
    row.normalizedCoeff q2301 * (b * e * star b * star e) +
    row.normalizedCoeff q3012 * (c * star a * star d * star f)

private theorem tableMatrixFunction_eq_expanded
    (row : IrrepDatum HC4) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      expandedRowSum row a b c d e f := by
  rw [tableMatrixFunction_eq_explicit]
  simp [explicitC4Rows, explicitC4RowsList, expandedRowSum,
    q0123, q1230, q2301, q3012,
    monomial_p0123, monomial_p1230, monomial_p2301, monomial_p3012] <;> ring

private theorem g_ne_one : ConcretePerm.cycle0123 ≠ 1 := by native_decide
private theorem g2_ne_one : ConcretePerm.cycle0123 ^ 2 ≠ 1 := by native_decide
private theorem g3_ne_one : ConcretePerm.cycle0123 ^ 3 ≠ 1 := by native_decide
private theorem g_ne_g2 : ConcretePerm.cycle0123 ≠ ConcretePerm.cycle0123 ^ 2 := by
  native_decide
private theorem g2_ne_g : ConcretePerm.cycle0123 ^ 2 ≠ ConcretePerm.cycle0123 := by
  native_decide
private theorem g3_ne_g : ConcretePerm.cycle0123 ^ 3 ≠ ConcretePerm.cycle0123 := by
  native_decide
private theorem g3_ne_g2 : ConcretePerm.cycle0123 ^ 3 ≠ ConcretePerm.cycle0123 ^ 2 := by
  native_decide

attribute [local simp] p0123_eq_one p1230_eq_cycle0123 p2301_eq_cycle0123_sq
  p3012_eq_cycle0123_cube g_ne_one g2_ne_one g3_ne_one g_ne_g2 g2_ne_g
  g3_ne_g g3_ne_g2

set_option maxHeartbeats 2000000 in
theorem registered_row_expansion (j : Fin 4) (a b c d e f : ℂ) :
    ((rowOfIndex .c4 j).tableMatrixFunction (correlation a b c d e f)).re =
      C4Cases.rowReal j (halfTurnMonomial b e)
        (cycleMonomial a b c d e f).re (cycleMonomial a b c d e f).im := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_expanded]
  fin_cases j <;>
    simp [expandedRowSum, q0123, q1230, q2301, q3012,
      rowOfIndex, c4Row, trivialRow, mkRow, IrrepDatum.normalizedCoeff,
      C4Cases.rowReal, cycleMonomial, halfTurnMonomial,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      hstar_re, hstar_im, Fin.mk.injEq] <;>
    norm_num <;> ring

/-- The primitive cyclic rows are controlled by the two opposite-edge
products occurring in their generator monomial. -/
theorem two_abs_cycle_im_le_opposite_products (a c d f : ℂ) :
    2 * |(a * d * f * star c).im| ≤
      normSq a * normSq f + normSq c * normSq d := by
  let x : ℂ := a * f
  let y : ℂ := d * star c
  have him := Complex.abs_im_le_norm (x * y)
  have ham : 2 * ‖x * y‖ ≤ normSq x + normSq y := by
    rw [norm_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hxy : x * y = a * d * f * star c := by simp [x, y]; ring
  have him2 := mul_le_mul_of_nonneg_left him (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * |(a * d * f * star c).im| = 2 * |(x * y).im| := by rw [hxy]
    _ ≤ 2 * ‖x * y‖ := him2
    _ ≤ normSq x + normSq y := ham
    _ = normSq a * normSq f + normSq c * normSq d := by
      simp [x, y, Complex.normSq_mul, Complex.normSq_conj]
      ring

theorem two_abs_cycle_re_le_opposite_products (a c d f : ℂ) :
    2 * |(a * d * f * star c).re| ≤
      normSq a * normSq f + normSq c * normSq d := by
  let x : ℂ := a * f
  let y : ℂ := d * star c
  have hre := Complex.abs_re_le_norm (x * y)
  have ham : 2 * ‖x * y‖ ≤ normSq x + normSq y := by
    rw [norm_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hxy : x * y = a * d * f * star c := by simp [x, y]; ring
  have hre2 := mul_le_mul_of_nonneg_left hre (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * |(a * d * f * star c).re| = 2 * |(x * y).re| := by rw [hxy]
    _ ≤ 2 * ‖x * y‖ := hre2
    _ ≤ normSq x + normSq y := ham
    _ = normSq a * normSq f + normSq c * normSq d := by
      simp [x, y, Complex.normSq_mul, Complex.normSq_conj]
      ring

/-- All four registered cyclic rows on normalized correlation matrices. -/
theorem registered_row_correlation_dominance (j : Fin 4) (a b c d e f : ℂ)
    (hA : IsPSD (correlation a b c d e f)) :
    ((rowOfIndex .c4 j).tableMatrixFunction (correlation a b c d e f)).re ≤
      (correlation a b c d e f).permanent.re := by
  rw [registered_row_expansion, PermutationEnumeration.permanent_expansion]
  let r := normSq b * normSq e
  let z := a * d * f * star c
  let A := normSq a * normSq f + normSq c * normSq d
  let p := normSq b
  let q := normSq e
  let P := permanentForm (T a b c d e f) (D a b c d e f)
    (C a b c d e f) (F a b c d e f)
  have hp0 : 0 ≤ p := normSq_nonneg _
  have hq0 : 0 ≤ q := normSq_nonneg _
  have hA0 : 0 ≤ A := add_nonneg
    (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))
    (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))
  have hr0 : 0 ≤ r := mul_nonneg hp0 hq0
  have hplus := block_permanent_contraction hA
  have hdet := block_determinant_contraction hA
  have hopp := permanent_ge_one_plus_opposite_products hA
  have hopp' : 1 + A ≤ P := by simpa [add_assoc] using hopp
  have hplusEq : blockPermanentRhs a b c d e f =
      1 + r + 2 * z.re + p + q + A := by
    simp [blockPermanentRhs, D, r, z, p, q, A, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def]
    ring
  have hdetEq : blockDeterminantRhs a b c d e f =
      1 + r - 2 * z.re + A - p - q := by
    simp [blockDeterminantRhs, r, z, p, q, A, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def]
    ring
  change blockPermanentRhs a b c d e f ≤ P at hplus
  change blockDeterminantRhs a b c d e f ≤ P at hdet
  have hre := two_abs_cycle_re_le_opposite_products a c d f
  have him := two_abs_cycle_im_le_opposite_products a c d f
  change 2 * |z.re| ≤ A at hre
  change 2 * |z.im| ≤ A at him
  fin_cases j
  · simp [C4Cases.rowReal, halfTurnMonomial, cycleMonomial]
    have hscalar : 1 + r + 2 * z.re ≤ P := by
      rw [hplusEq] at hplus
      nlinarith
    simpa [z, r, P, Complex.mul_re, Complex.mul_im, Complex.star_def] using hscalar
  · simp [C4Cases.rowReal, halfTurnMonomial, cycleMonomial]
    have hscalar : 1 - r - 2 * z.im ≤ P := by
      nlinarith [hopp', le_abs_self z.im, neg_le_abs z.im]
    simpa [z, r, P, Complex.mul_re, Complex.mul_im, Complex.star_def] using hscalar
  · simp [C4Cases.rowReal, halfTurnMonomial, cycleMonomial]
    have hscalar : 1 + r - 2 * z.re ≤ P := by
      by_cases hApq : A ≤ p + q
      · rw [hplusEq] at hplus
        have hzlower : -2 * A ≤ 4 * z.re := by
          nlinarith [neg_le_abs z.re]
        nlinarith
      · rw [hdetEq] at hdet
        have hpqA : p + q ≤ A := le_of_not_ge hApq
        nlinarith
    simpa [z, r, P, Complex.mul_re, Complex.mul_im, Complex.star_def] using hscalar
  · simp [C4Cases.rowReal, halfTurnMonomial, cycleMonomial]
    have hscalar : 1 - r + 2 * z.im ≤ P := by
      nlinarith [hopp', le_abs_self z.im, neg_le_abs z.im]
    simpa [z, r, P, Complex.mul_re, Complex.mul_im, Complex.star_def] using hscalar

theorem registered_row_diagonal_one_dominance (j : Fin 4)
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hM : IsPSD M)
    (hdiag : ∀ i : Fin 4, M i i = 1) :
    ((rowOfIndex .c4 j).tableMatrixFunction M).re ≤ M.permanent.re := by
  rw [CorrelationReduction.eq_correlation_of_diagonal_one hM hdiag]
  exact registered_row_correlation_dominance j _ _ _ _ _ _
    (CorrelationReduction.diagonal_one_correlation_psd hM hdiag)

end PermanentalDominance.N4.C4TableBridge
