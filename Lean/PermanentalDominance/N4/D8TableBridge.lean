import PermanentalDominance.N4.CharacterTables
import PermanentalDominance.N4.PermutationEnumeration
import PermanentalDominance.N4.FischerContractions
import PermanentalDominance.N4.S4Cases

/-!
# The registered dihedral table

The chosen `D₈` preserves the pairing `{0,2}|{1,3}`.  Its five normalized
character rows are respectively the symmetric block permanent, two easy
subtractions from it or from the diagonal monomial, the alternating block
determinant, and the degree-two half-turn row.  This file supplies the finite
table expansion and attaches the two Fischer contractions.
-/

noncomputable section

open scoped BigOperators

namespace PermanentalDominance.N4.D8TableBridge

open Complex CorrelationReduction CycleCoordinates ScalarAggregates
open PermutationEnumeration FischerContractions

abbrev HD8 : Subgroup S4 := representative .d8

local instance : Fintype HD8 := Fintype.ofFinite _

def allD8Rows : Finset HD8 := (representativeCarrier .d8).attach

theorem allD8Rows_eq_univ : allD8Rows = Finset.univ := by
  ext sigma
  simp only [Finset.mem_univ, iff_true]
  exact Finset.mem_attach _ _

def q0123 : HD8 :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .d8; native_decide⟩
def q1230 : HD8 :=
  ⟨p1230, by change p1230 ∈ representativeCarrier .d8; native_decide⟩
def q2301 : HD8 :=
  ⟨p2301, by change p2301 ∈ representativeCarrier .d8; native_decide⟩
def q3012 : HD8 :=
  ⟨p3012, by change p3012 ∈ representativeCarrier .d8; native_decide⟩
def q2103 : HD8 :=
  ⟨p2103, by change p2103 ∈ representativeCarrier .d8; native_decide⟩
def q1032 : HD8 :=
  ⟨p1032, by change p1032 ∈ representativeCarrier .d8; native_decide⟩
def q0321 : HD8 :=
  ⟨p0321, by change p0321 ∈ representativeCarrier .d8; native_decide⟩
def q3210 : HD8 :=
  ⟨p3210, by change p3210 ∈ representativeCarrier .d8; native_decide⟩

def explicitD8RowsList : Multiset HD8 :=
  [q0123, q1230, q2301, q3012, q2103, q1032, q0321, q3210]

theorem explicitD8RowsList_nodup : explicitD8RowsList.Nodup := by native_decide

def explicitD8Rows : Finset HD8 :=
  ⟨explicitD8RowsList, explicitD8RowsList_nodup⟩

theorem explicitD8Rows_eq_allD8Rows : explicitD8Rows = allD8Rows := by
  native_decide

private theorem tableMatrixFunction_eq_explicit
    (row : IrrepDatum HD8) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      ∑ sigma in explicitD8Rows,
        row.normalizedCoeff sigma *
          permutationMonomial (correlation a b c d e f) sigma.1 := by
  rw [row.tableMatrixFunction_eq_sum, ← allD8Rows_eq_univ,
    ← explicitD8Rows_eq_allD8Rows]

private def expandedRowSum (row : IrrepDatum HD8)
    (a b c d e f : ℂ) : ℂ :=
  row.normalizedCoeff q0123 +
  row.normalizedCoeff q1230 * (a * d * f * star c) +
  row.normalizedCoeff q2301 * (b * e * star b * star e) +
  row.normalizedCoeff q3012 * (c * star a * star d * star f) +
  row.normalizedCoeff q2103 * (b * star b) +
  row.normalizedCoeff q1032 * (a * star a * f * star f) +
  row.normalizedCoeff q0321 * (e * star e) +
  row.normalizedCoeff q3210 * (c * d * star d * star c)

private theorem tableMatrixFunction_eq_expanded
    (row : IrrepDatum HD8) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      expandedRowSum row a b c d e f := by
  rw [tableMatrixFunction_eq_explicit]
  simp [explicitD8Rows, explicitD8RowsList, expandedRowSum,
    q0123, q1230, q2301, q3012, q2103, q1032, q0321, q3210,
    monomial_p0123, monomial_p1230, monomial_p2301,
    monomial_p3012, monomial_p2103, monomial_p1032, monomial_p0321,
    monomial_p3210] <;> ring

private theorem p0123_eq_one : p0123 = 1 := by native_decide
private theorem p1230_eq_g : p1230 = ConcretePerm.cycle0123 := by native_decide
private theorem p2301_eq_g2 : p2301 = ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem p3012_eq_g3 : p3012 = ConcretePerm.cycle0123 ^ 3 := by native_decide
private theorem p2103_eq_s : p2103 = ConcretePerm.t02 := by native_decide
private theorem p1032_eq_sg :
    p1032 = ConcretePerm.t02 * ConcretePerm.cycle0123 := by native_decide
private theorem p0321_eq_sg2 :
    p0321 = ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem p3210_eq_sg3 :
    p3210 = ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 3 := by native_decide

private theorem d8LinearValue_p0123 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p0123 eg es = 1 := by
  rw [d8LinearValue, if_pos (by native_decide)]
private theorem d8LinearValue_p1230 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p1230 eg es =
      if eg then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_pos (by native_decide)]
private theorem d8LinearValue_p2301 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p2301 eg es = 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]
private theorem d8LinearValue_p3012 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p3012 eg es =
      if eg then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]
private theorem d8LinearValue_p2103 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p2103 eg es =
      if es then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide), if_pos (by native_decide)]
private theorem d8LinearValue_p1032 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p1032 eg es =
      if Bool.xor eg es then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]
private theorem d8LinearValue_p0321 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p0321 eg es =
      if es then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]
private theorem d8LinearValue_p3210 (eg es : Bool) :
    d8LinearValue ConcretePerm.cycle0123 ConcretePerm.t02 p3210 eg es =
      if Bool.xor eg es then -1 else 1 := by
  rw [d8LinearValue, if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide)]

private theorem g_ne_one : ConcretePerm.cycle0123 ≠ 1 := by native_decide
private theorem g2_ne_one : ConcretePerm.cycle0123 ^ 2 ≠ 1 := by native_decide
private theorem g3_ne_one : ConcretePerm.cycle0123 ^ 3 ≠ 1 := by native_decide
private theorem s_ne_one : ConcretePerm.t02 ≠ 1 := by native_decide
private theorem sg_ne_one : ConcretePerm.t02 * ConcretePerm.cycle0123 ≠ 1 := by native_decide
private theorem sg2_ne_one : ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 2 ≠ 1 := by native_decide
private theorem sg3_ne_one : ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 3 ≠ 1 := by native_decide
private theorem g_ne_g2 : ConcretePerm.cycle0123 ≠ ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem g3_ne_g2 : ConcretePerm.cycle0123 ^ 3 ≠ ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem s_ne_g2 : ConcretePerm.t02 ≠ ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem sg_ne_g2 : ConcretePerm.t02 * ConcretePerm.cycle0123 ≠
    ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem sg2_ne_g2 : ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 2 ≠
    ConcretePerm.cycle0123 ^ 2 := by native_decide
private theorem sg3_ne_g2 : ConcretePerm.t02 * ConcretePerm.cycle0123 ^ 3 ≠
    ConcretePerm.cycle0123 ^ 2 := by native_decide

private theorem d8DegreeValue_p0123 :
    (if p0123 = 1 then (2 : ℂ)
      else if p0123 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 2 := by
  rw [if_pos (by native_decide)]
private theorem d8DegreeValue_p1230 :
    (if p1230 = 1 then (2 : ℂ)
      else if p1230 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]
private theorem d8DegreeValue_p2301 :
    (if p2301 = 1 then (2 : ℂ)
      else if p2301 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = -2 := by
  rw [if_neg (by native_decide), if_pos (by native_decide)]
private theorem d8DegreeValue_p3012 :
    (if p3012 = 1 then (2 : ℂ)
      else if p3012 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]
private theorem d8DegreeValue_p2103 :
    (if p2103 = 1 then (2 : ℂ)
      else if p2103 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]
private theorem d8DegreeValue_p1032 :
    (if p1032 = 1 then (2 : ℂ)
      else if p1032 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]
private theorem d8DegreeValue_p0321 :
    (if p0321 = 1 then (2 : ℂ)
      else if p0321 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]
private theorem d8DegreeValue_p3210 :
    (if p3210 = 1 then (2 : ℂ)
      else if p3210 = ConcretePerm.cycle0123 ^ 2 then -2 else 0) = 0 := by
  rw [if_neg (by native_decide), if_neg (by native_decide)]

attribute [local simp] d8LinearValue_p0123 d8LinearValue_p1230
  d8LinearValue_p2301 d8LinearValue_p3012 d8LinearValue_p2103
  d8LinearValue_p1032 d8LinearValue_p0321 d8LinearValue_p3210
  d8DegreeValue_p0123 d8DegreeValue_p1230 d8DegreeValue_p2301
  d8DegreeValue_p3012 d8DegreeValue_p2103 d8DegreeValue_p1032
  d8DegreeValue_p0321 d8DegreeValue_p3210
  g_ne_one g2_ne_one g3_ne_one s_ne_one sg_ne_one sg2_ne_one sg3_ne_one
  g_ne_g2 g3_ne_g2 s_ne_g2 sg_ne_g2 sg2_ne_g2 sg3_ne_g2

private def registeredRowReal (j : Fin 5) (a b c d e f : ℂ) : ℝ :=
  if j = 0 then blockPermanentRhs a b c d e f
  else if j = 1 then
    (1 + normSq b) * (1 + normSq e) - normSq (a * f + c * star d)
  else if j = 2 then
    (1 - normSq b) * (1 - normSq e) - normSq (a * f - c * star d)
  else if j = 3 then blockDeterminantRhs a b c d e f
  else 1 - normSq b * normSq e

set_option maxHeartbeats 2000000 in
private theorem registered_row_expansion_fixed (j : Fin 5) (a b c d e f : ℂ) :
    ((rowOfIndex .d8 j).tableMatrixFunction
      (correlation a b c d e f)).re = registeredRowReal j a b c d e f := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [tableMatrixFunction_eq_expanded]
  fin_cases j <;>
    simp [expandedRowSum, q0123, q1230, q2301, q3012,
      q2103, q1032, q0321, q3210, IrrepDatum.normalizedCoeff,
      rowOfIndex, d8Row, trivialRow, mkRow, registeredRowReal,
      blockPermanentRhs, blockDeterminantRhs, D, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, hstar_re, hstar_im, Fin.mk.injEq] <;>
    norm_num <;> ring

theorem registered_row_expansion (j : Fin 5) (a b c d e f : ℂ) :
    ((rowOfIndex .d8 j).tableMatrixFunction
      (correlation a b c d e f)).re = registeredRowReal j a b c d e f :=
  registered_row_expansion_fixed j a b c d e f

/-- All five registered `D₈` rows on correlation matrices. -/
theorem registered_row_correlation_dominance (j : Fin 5) (a b c d e f : ℂ)
    (hA : IsPSD (correlation a b c d e f)) :
    ((rowOfIndex .d8 j).tableMatrixFunction (correlation a b c d e f)).re ≤
      (correlation a b c d e f).permanent.re := by
  rw [registered_row_expansion, PermutationEnumeration.permanent_expansion]
  have hplus := block_permanent_contraction hA
  have hdet := block_determinant_contraction hA
  have hdiag := S4Cases.correlation_permanent_ge_one hA
  have hp0 := normSq_nonneg b
  have hq0 := normSq_nonneg e
  have hp1 := normSq_b_le_one hA
  have hq1 := normSq_e_le_one hA
  fin_cases j
  · simpa [registeredRowReal] using hplus
  · have hminus : (1 + normSq b) * (1 + normSq e) -
        normSq (a * f + c * star d) ≤ blockPermanentRhs a b c d e f := by
      have heq : blockPermanentRhs a b c d e f =
          (1 + normSq b) * (1 + normSq e) +
            normSq (a * f + c * star d) := by
        simp [blockPermanentRhs, D, Complex.normSq_apply, Complex.mul_re,
          Complex.mul_im, Complex.star_def]
        ring
      rw [heq]
      nlinarith [normSq_nonneg (a * f + c * star d)]
    exact (by simpa [registeredRowReal] using hminus.trans hplus)
  · have hrow : (1 - normSq b) * (1 - normSq e) -
        normSq (a * f - c * star d) ≤ 1 := by
      nlinarith [normSq_nonneg (a * f - c * star d),
        mul_nonneg hp0 (sub_nonneg.mpr hq1),
        mul_nonneg hq0 (sub_nonneg.mpr hp1)]
    exact (by simpa [registeredRowReal] using hrow.trans hdiag)
  · simpa [registeredRowReal] using hdet
  · have hrow : 1 - normSq b * normSq e ≤ 1 := by
      exact sub_le_self _ (mul_nonneg hp0 hq0)
    exact (by simpa [registeredRowReal] using hrow.trans hdiag)

theorem registered_row_diagonal_one_dominance (j : Fin 5)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsPSD A)
    (hdiag : ∀ i : Fin 4, A i i = 1) :
    ((rowOfIndex .d8 j).tableMatrixFunction A).re ≤ A.permanent.re := by
  rw [CorrelationReduction.eq_correlation_of_diagonal_one hA hdiag]
  exact registered_row_correlation_dominance j _ _ _ _ _ _
    (CorrelationReduction.diagonal_one_correlation_psd hA hdiag)

end PermanentalDominance.N4.D8TableBridge
