import PermanentalDominance.N4.CharacterTables
import PermanentalDominance.N4.PermutationEnumeration
import PermanentalDominance.N4.PrincipalPermanentContraction
import PermanentalDominance.N4.S4Cases
import PermanentalDominance.N4.CorrelationLift

/-!
# Registered low-order subgroup rows

This file handles the seven representatives below `C₄`: the trivial group,
the two order-two groups, `C₃`, the two Klein four groups, and `S₃`.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.LowOrderRegistry

open CorrelationReduction CycleCoordinates ScalarAggregates
open PermutationEnumeration PrincipalPermanentContraction

local instance {k : SubgroupKind} : Fintype (representative k) := Fintype.ofFinite _

private def allRows (k : SubgroupKind) : Finset (representative k) :=
  (representativeCarrier k).attach

private theorem allRows_eq_univ (k : SubgroupKind) : allRows k = Finset.univ := by
  ext sigma
  simp only [Finset.mem_univ, iff_true]
  exact Finset.mem_attach _ _

/-! ## Concrete carrier enumerations -/

private def qTriv : representative .trivial :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .trivial; native_decide⟩
private def trivList : Multiset (representative .trivial) := [qTriv]
private theorem trivList_nodup : trivList.Nodup := by native_decide
private def trivRows : Finset (representative .trivial) := ⟨trivList, trivList_nodup⟩
private theorem trivRows_eq : trivRows = allRows .trivial := by native_decide

private def qt0 : representative .c2Transposition :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .c2Transposition; native_decide⟩
private def qt1 : representative .c2Transposition :=
  ⟨p1023, by change p1023 ∈ representativeCarrier .c2Transposition; native_decide⟩
private def ctList : Multiset (representative .c2Transposition) := [qt0, qt1]
private theorem ctList_nodup : ctList.Nodup := by native_decide
private def ctRows : Finset (representative .c2Transposition) := ⟨ctList, ctList_nodup⟩
private theorem ctRows_eq : ctRows = allRows .c2Transposition := by native_decide

private def qd0 : representative .c2DoubleTransposition :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .c2DoubleTransposition; native_decide⟩
private def qd1 : representative .c2DoubleTransposition :=
  ⟨p1032, by change p1032 ∈ representativeCarrier .c2DoubleTransposition; native_decide⟩
private def cdList : Multiset (representative .c2DoubleTransposition) := [qd0, qd1]
private theorem cdList_nodup : cdList.Nodup := by native_decide
private def cdRows : Finset (representative .c2DoubleTransposition) := ⟨cdList, cdList_nodup⟩
private theorem cdRows_eq : cdRows = allRows .c2DoubleTransposition := by native_decide

private def qc0 : representative .c3 :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .c3; native_decide⟩
private def qc1 : representative .c3 :=
  ⟨p1203, by change p1203 ∈ representativeCarrier .c3; native_decide⟩
private def qc2 : representative .c3 :=
  ⟨p2013, by change p2013 ∈ representativeCarrier .c3; native_decide⟩
private def c3List : Multiset (representative .c3) := [qc0, qc1, qc2]
private theorem c3List_nodup : c3List.Nodup := by native_decide
private def c3Rows : Finset (representative .c3) := ⟨c3List, c3List_nodup⟩
private theorem c3Rows_eq : c3Rows = allRows .c3 := by native_decide

private def qn0 : representative .v4Normal :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .v4Normal; native_decide⟩
private def qn1 : representative .v4Normal :=
  ⟨p1032, by change p1032 ∈ representativeCarrier .v4Normal; native_decide⟩
private def qn2 : representative .v4Normal :=
  ⟨p2301, by change p2301 ∈ representativeCarrier .v4Normal; native_decide⟩
private def qn3 : representative .v4Normal :=
  ⟨p3210, by change p3210 ∈ representativeCarrier .v4Normal; native_decide⟩
private def vnList : Multiset (representative .v4Normal) := [qn0, qn1, qn2, qn3]
private theorem vnList_nodup : vnList.Nodup := by native_decide
private def vnRows : Finset (representative .v4Normal) := ⟨vnList, vnList_nodup⟩
private theorem vnRows_eq : vnRows = allRows .v4Normal := by native_decide

private def qv0 : representative .v4Disjoint :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .v4Disjoint; native_decide⟩
private def qv1 : representative .v4Disjoint :=
  ⟨p1023, by change p1023 ∈ representativeCarrier .v4Disjoint; native_decide⟩
private def qv2 : representative .v4Disjoint :=
  ⟨p0132, by change p0132 ∈ representativeCarrier .v4Disjoint; native_decide⟩
private def qv3 : representative .v4Disjoint :=
  ⟨p1032, by change p1032 ∈ representativeCarrier .v4Disjoint; native_decide⟩
private def vdList : Multiset (representative .v4Disjoint) := [qv0, qv1, qv2, qv3]
private theorem vdList_nodup : vdList.Nodup := by native_decide
private def vdRows : Finset (representative .v4Disjoint) := ⟨vdList, vdList_nodup⟩
private theorem vdRows_eq : vdRows = allRows .v4Disjoint := by native_decide

private def qs0 : representative .s3 :=
  ⟨p0123, by change p0123 ∈ representativeCarrier .s3; native_decide⟩
private def qs1 : representative .s3 :=
  ⟨p1023, by change p1023 ∈ representativeCarrier .s3; native_decide⟩
private def qs2 : representative .s3 :=
  ⟨p2103, by change p2103 ∈ representativeCarrier .s3; native_decide⟩
private def qs3 : representative .s3 :=
  ⟨p0213, by change p0213 ∈ representativeCarrier .s3; native_decide⟩
private def qs4 : representative .s3 :=
  ⟨p1203, by change p1203 ∈ representativeCarrier .s3; native_decide⟩
private def qs5 : representative .s3 :=
  ⟨p2013, by change p2013 ∈ representativeCarrier .s3; native_decide⟩
private def s3List : Multiset (representative .s3) := [qs0, qs1, qs2, qs3, qs4, qs5]
private theorem s3List_nodup : s3List.Nodup := by native_decide
private def s3Rows : Finset (representative .s3) := ⟨s3List, s3List_nodup⟩
private theorem s3Rows_eq : s3Rows = allRows .s3 := by native_decide

private theorem p0123_eq_one : p0123 = 1 := by native_decide
private theorem p1023_eq_t01 : p1023 = ConcretePerm.t01 := by native_decide
private theorem p0132_eq_t23 : p0132 = ConcretePerm.t23 := by native_decide
private theorem p1032_eq_double : p1032 = ConcretePerm.double01_23 := by native_decide
private theorem p1203_eq_cycle : p1203 = ConcretePerm.cycle012 := by native_decide
private theorem p2013_eq_cycle_sq : p2013 = ConcretePerm.cycle012 ^ 2 := by native_decide
private theorem p2301_eq_double2 : p2301 = ConcretePerm.double02_13 := by native_decide
private theorem p3210_eq_double3 :
    p3210 = ConcretePerm.double01_23 * ConcretePerm.double02_13 := by native_decide
private theorem p2103_eq_t02 : p2103 = ConcretePerm.t02 := by native_decide
private theorem p0213_eq_t12 : p0213 = ConcretePerm.t12 := by native_decide

private theorem t01_ne_one : ConcretePerm.t01 ≠ 1 := by native_decide
private theorem t23_ne_one : ConcretePerm.t23 ≠ 1 := by native_decide
private theorem t23_ne_t01 : ConcretePerm.t23 ≠ ConcretePerm.t01 := by native_decide
private theorem double_ne_one : ConcretePerm.double01_23 ≠ 1 := by native_decide
private theorem double_ne_t01 : ConcretePerm.double01_23 ≠ ConcretePerm.t01 := by
  native_decide
private theorem double_ne_t23 : ConcretePerm.double01_23 ≠ ConcretePerm.t23 := by
  native_decide
private theorem cycle_ne_one : ConcretePerm.cycle012 ≠ 1 := by native_decide
private theorem cycle_sq_ne_one : ConcretePerm.cycle012 ^ 2 ≠ 1 := by native_decide
private theorem cycle_sq_ne_cycle :
    ConcretePerm.cycle012 ^ 2 ≠ ConcretePerm.cycle012 := by native_decide
private theorem double2_ne_one : ConcretePerm.double02_13 ≠ 1 := by native_decide
private theorem double2_ne_double :
    ConcretePerm.double02_13 ≠ ConcretePerm.double01_23 := by native_decide
private theorem double3_ne_one :
    ConcretePerm.double01_23 * ConcretePerm.double02_13 ≠ 1 := by native_decide
private theorem double3_ne_double :
    ConcretePerm.double01_23 * ConcretePerm.double02_13 ≠
      ConcretePerm.double01_23 := by native_decide
private theorem double3_ne_double2 :
    ConcretePerm.double01_23 * ConcretePerm.double02_13 ≠
      ConcretePerm.double02_13 := by native_decide

private theorem s3Class_one : s3Class 1 = 0 := by native_decide
private theorem s3Class_t01 : s3Class ConcretePerm.t01 = 1 := by native_decide
private theorem s3Class_t02 : s3Class ConcretePerm.t02 = 1 := by native_decide
private theorem s3Class_t12 : s3Class ConcretePerm.t12 = 1 := by native_decide
private theorem s3Class_cycle : s3Class ConcretePerm.cycle012 = 2 := by native_decide
private theorem s3Class_cycle_sq : s3Class (ConcretePerm.cycle012 ^ 2) = 2 := by
  native_decide

private theorem omega_sq_explicit :
    omega ^ 2 = ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  calc
    omega ^ 2 = -omega - 1 := by linear_combination omega_quadratic
    _ = ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
      simp [omega]
      ring

private theorem omega_re : omega.re = -1 / 2 := by simp [omega]
private theorem omega_im : omega.im = -Real.sqrt 3 / 2 := by
  simp [omega]
  ring
private theorem omega_sq_re : (omega ^ 2).re = -1 / 2 := by
  rw [omega_sq_explicit]
  simp
private theorem omega_sq_im : (omega ^ 2).im = Real.sqrt 3 / 2 := by
  rw [omega_sq_explicit]
  simp

attribute [local simp] t01_ne_one t23_ne_one t23_ne_t01 double_ne_one
  double_ne_t01 double_ne_t23 cycle_ne_one cycle_sq_ne_one cycle_sq_ne_cycle
  double2_ne_one double2_ne_double double3_ne_one double3_ne_double
  double3_ne_double2 s3Class_one s3Class_t01 s3Class_t02 s3Class_t12
  s3Class_cycle s3Class_cycle_sq

/-! ## Scalar expansions -/

private theorem trivial_table_expanded (a b c d e f : ℂ) :
    (rowOfIndex .trivial (⟨0, by decide⟩ : Fin 1)).tableMatrixFunction
        (correlation a b c d e f) = 1 := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .trivial,
    ← trivRows_eq]
  simp [trivRows, trivList, qTriv, monomial_p0123, rowOfIndex, trivialRow,
    mkRow, IrrepDatum.normalizedCoeff]

theorem trivial_expansion (a b c d e f : ℂ) :
    ((rowOfIndex .trivial (⟨0, by decide⟩ : Fin 1)).tableMatrixFunction
      (correlation a b c d e f)).re = 1 := by
  rw [trivial_table_expanded]
  norm_num

private theorem c2Trans_table_expanded (row : IrrepDatum (representative .c2Transposition))
    (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qt0 + row.normalizedCoeff qt1 * (a * star a) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .c2Transposition,
    ← ctRows_eq]
  simp [ctRows, ctList, qt0, qt1, monomial_p0123, monomial_p1023]

theorem c2Trans_expansion (j : Fin 2) (a b c d e f : ℂ) :
    ((rowOfIndex .c2Transposition j).tableMatrixFunction
      (correlation a b c d e f)).re = if j = 0 then 1 + normSq a else 1 - normSq a := by
  rw [c2Trans_table_expanded]
  fin_cases j <;>
    simp [qt0, qt1, rowOfIndex, trivialRow, c2NontrivialRow,
      mkRow, IrrepDatum.normalizedCoeff, p0123_eq_one, p1023_eq_t01,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

private theorem c2Double_table_expanded
    (row : IrrepDatum (representative .c2DoubleTransposition))
    (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qd0 +
        row.normalizedCoeff qd1 * (a * star a * f * star f) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum,
    ← allRows_eq_univ .c2DoubleTransposition, ← cdRows_eq]
  simp [cdRows, cdList, qd0, qd1, monomial_p0123, monomial_p1032]

theorem c2Double_expansion (j : Fin 2) (a b c d e f : ℂ) :
    ((rowOfIndex .c2DoubleTransposition j).tableMatrixFunction
      (correlation a b c d e f)).re =
      if j = 0 then 1 + normSq a * normSq f else 1 - normSq a * normSq f := by
  rw [c2Double_table_expanded]
  fin_cases j <;>
    simp [qd0, qd1, rowOfIndex, trivialRow, c2NontrivialRow,
      mkRow, IrrepDatum.normalizedCoeff, p0123_eq_one, p1032_eq_double,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

def c3RowReal (j : Fin 3) (z : ℂ) : ℝ :=
  if j = 0 then 1 + 2 * z.re
  else if j = 1 then 1 - z.re + Real.sqrt 3 * z.im
  else 1 - z.re - Real.sqrt 3 * z.im

private theorem c3_table_expanded (row : IrrepDatum (representative .c3))
    (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qc0 +
        row.normalizedCoeff qc1 * (a * d * star b) +
        row.normalizedCoeff qc2 * (b * star a * star d) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .c3, ← c3Rows_eq]
  simp [c3Rows, c3List, qc0, qc1, qc2, monomial_p0123,
    monomial_p1203, monomial_p2013] <;> ring

theorem c3_expansion (j : Fin 3) (a b c d e f : ℂ) :
    ((rowOfIndex .c3 j).tableMatrixFunction (correlation a b c d e f)).re =
      c3RowReal j (a * d * star b) := by
  rw [c3_table_expanded]
  fin_cases j <;>
    simp [qc0, qc1, qc2, rowOfIndex, trivialRow, c3Row,
      mkRow, IrrepDatum.normalizedCoeff, p0123_eq_one, p1203_eq_cycle,
      p2013_eq_cycle_sq, c3RowReal, omega_re, omega_im, omega_sq_re,
      omega_sq_im, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    ring

def v4NormalRowReal (j : Fin 4) (a b c d e f : ℂ) : ℝ :=
  let r := normSq a * normSq f
  let s := normSq b * normSq e
  let t := normSq c * normSq d
  if j = 0 then 1 + r + s + t
  else if j = 1 then 1 - r + s - t
  else if j = 2 then 1 + r - s - t
  else 1 - r - s + t

private theorem v4Normal_table_expanded (row : IrrepDatum (representative .v4Normal))
    (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qn0 +
        row.normalizedCoeff qn1 * (a * star a * f * star f) +
        row.normalizedCoeff qn2 * (b * e * star b * star e) +
        row.normalizedCoeff qn3 * (c * d * star d * star c) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .v4Normal,
    ← vnRows_eq]
  simp [vnRows, vnList, qn0, qn1, qn2, qn3, monomial_p0123,
    monomial_p1032, monomial_p2301, monomial_p3210] <;> ring

theorem v4Normal_expansion (j : Fin 4) (a b c d e f : ℂ) :
    ((rowOfIndex .v4Normal j).tableMatrixFunction (correlation a b c d e f)).re =
      v4NormalRowReal j a b c d e f := by
  rw [v4Normal_table_expanded]
  fin_cases j <;>
    simp [qn0, qn1, qn2, qn3, rowOfIndex, trivialRow,
      v4Row, mkRow, IrrepDatum.normalizedCoeff, p0123_eq_one,
      p1032_eq_double, p2301_eq_double2, p3210_eq_double3, v4NormalRowReal,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

def v4DisjointRowReal (j : Fin 4) (a f : ℂ) : ℝ :=
  let r := normSq a
  let s := normSq f
  let t := normSq a * normSq f
  if j = 0 then 1 + r + s + t
  else if j = 1 then 1 - r + s - t
  else if j = 2 then 1 + r - s - t
  else 1 - r - s + t

private theorem v4Disjoint_table_expanded
    (row : IrrepDatum (representative .v4Disjoint)) (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qv0 + row.normalizedCoeff qv1 * (a * star a) +
        row.normalizedCoeff qv2 * (f * star f) +
        row.normalizedCoeff qv3 * (a * star a * f * star f) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .v4Disjoint,
    ← vdRows_eq]
  simp [vdRows, vdList, qv0, qv1, qv2, qv3, monomial_p0123,
    monomial_p1023, monomial_p0132, monomial_p1032] <;> ring

theorem v4Disjoint_expansion (j : Fin 4) (a b c d e f : ℂ) :
    ((rowOfIndex .v4Disjoint j).tableMatrixFunction (correlation a b c d e f)).re =
      v4DisjointRowReal j a f := by
  rw [v4Disjoint_table_expanded]
  fin_cases j <;>
    simp [qv0, qv1, qv2, qv3, rowOfIndex, trivialRow,
      v4Row, mkRow, IrrepDatum.normalizedCoeff, p0123_eq_one,
      p1023_eq_t01, p0132_eq_t23, p1032_eq_double, v4DisjointRowReal,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

def s3RowReal (j : Fin 3) (a b d : ℂ) : ℝ :=
  if j = 0 then principalPermanent012 a b d
  else if j = 1 then 1 - normSq a - normSq b - normSq d +
    2 * (a * d * star b).re
  else 1 - (a * d * star b).re

private theorem s3_table_expanded (row : IrrepDatum (representative .s3))
    (a b c d e f : ℂ) :
    row.tableMatrixFunction (correlation a b c d e f) =
      row.normalizedCoeff qs0 + row.normalizedCoeff qs1 * (a * star a) +
        row.normalizedCoeff qs2 * (b * star b) +
        row.normalizedCoeff qs3 * (d * star d) +
        row.normalizedCoeff qs4 * (a * d * star b) +
        row.normalizedCoeff qs5 * (b * star a * star d) := by
  rw [IrrepDatum.tableMatrixFunction_eq_sum, ← allRows_eq_univ .s3, ← s3Rows_eq]
  simp [s3Rows, s3List, qs0, qs1, qs2, qs3, qs4, qs5,
    monomial_p0123, monomial_p1023, monomial_p2103, monomial_p0213,
    monomial_p1203, monomial_p2013] <;> ring

theorem s3_expansion (j : Fin 3) (a b c d e f : ℂ) :
    ((rowOfIndex .s3 j).tableMatrixFunction (correlation a b c d e f)).re =
      s3RowReal j a b d := by
  rw [s3_table_expanded]
  fin_cases j <;>
    simp [qs0, qs1, qs2, qs3, qs4, qs5, rowOfIndex,
      s3Row, trivialRow, mkRow, IrrepDatum.normalizedCoeff,
      p0123_eq_one, p1023_eq_t01, p2103_eq_t02, p0213_eq_t12,
      p1203_eq_cycle, p2013_eq_cycle_sq, s3RowReal, principalPermanent012,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

/-! ## Analytic inequalities -/

private theorem principal012_psd {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation a b d) := by
  have h := hA.submatrix (![0, 1, 2] : Fin 3 → Fin 4)
  convert h using 1 <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [correlation, A4Certificate.correlation]

private theorem principal012_swap_psd {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation (star a) d b) := by
  have h := hA.submatrix (![1, 0, 2] : Fin 3 → Fin 4)
  convert h using 1 <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [correlation, A4Certificate.correlation]

private theorem triangle_gap_minus {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ normSq a + normSq b + normSq d +
      3 * (a * d * star b).re - Real.sqrt 3 * (a * d * star b).im := by
  simpa [A4Certificate.c0_expansion] using
    A4Certificate.c0_nonneg (principal012_psd hA)

private theorem triangle_gap_plus {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ normSq a + normSq b + normSq d +
      3 * (a * d * star b).re + Real.sqrt 3 * (a * d * star b).im := by
  have h := A4Certificate.c0_nonneg (principal012_swap_psd hA)
  rw [A4Certificate.c0_expansion] at h
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] at h ⊢
  nlinarith

private theorem permanent_ge_one_plus_D {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    1 + D a b c d e f ≤
      permanentForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hT := T_nonneg a b c d e f
  have hD := D_le_T_sq_div_four a b c d e f
  have hF := F_lower a b c d e f
  have h2D := two_D_le_T_of_edges_le_one
    (normSq_a_le_one hA) (normSq_b_le_one hA) (normSq_c_le_one hA)
    (normSq_d_le_one hA) (normSq_e_le_one hA) (normSq_f_le_one hA)
  have hS := SpectralThreeCycle.correlation_spectral_bound hA
  simp only [permanentForm]
  by_cases hsmall : T a b c d e f ≤ 2
  · nlinarith
  · have hC : 0 ≤ C a b c d e f := by nlinarith
    nlinarith

theorem correlation_dominance
    (k : SubgroupKind)
    (hk : k = .trivial ∨ k = .c2Transposition ∨ k = .c2DoubleTransposition ∨
      k = .c3 ∨ k = .v4Normal ∨ k = .v4Disjoint ∨ k = .s3)
    (j : Fin (rowCount k)) (a b c d e f : ℂ)
    (hA : IsPSD (correlation a b c d e f)) :
    ((rowOfIndex k j).tableMatrixFunction (correlation a b c d e f)).re ≤
      (correlation a b c d e f).permanent.re := by
  rw [PermutationEnumeration.permanent_expansion]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · fin_cases j
    rw [trivial_expansion]
    exact S4Cases.correlation_permanent_ge_one hA
  · rw [c2Trans_expansion]
    have hedge := principal012_ge_edge01 hA
    have hprincipal := principal012_contraction hA
    fin_cases j <;> simp <;> nlinarith [normSq_nonneg a]
  · rw [c2Double_expansion]
    have hopp := FischerContractions.permanent_ge_one_plus_opposite_products hA
    fin_cases j <;> simp <;>
      nlinarith [mul_nonneg (normSq_nonneg a) (normSq_nonneg f), normSq_nonneg c,
        normSq_nonneg d]
  · rw [c3_expansion]
    have hprincipal := principal012_contraction hA
    have hm := triangle_gap_minus hA
    have hp := triangle_gap_plus hA
    let x := (a * d * star b).re
    let y := (a * d * star b).im
    let A := normSq a + normSq b + normSq d
    let P := permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f)
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (add_nonneg (normSq_nonneg a) (normSq_nonneg b))
        (normSq_nonneg d)
    have hprincipal' : 1 + A + 2 * x ≤ P := by
      dsimp only [A, P]
      rw [show 1 + (normSq a + normSq b + normSq d) + 2 * x =
          principalPermanent012 a b d by
        dsimp only [x]
        simp only [principalPermanent012]
        ring]
      exact hprincipal
    have hm' : 0 ≤ A + 3 * x - Real.sqrt 3 * y := by
      simpa only [A, x, y] using hm
    have hp' : 0 ≤ A + 3 * x + Real.sqrt 3 * y := by
      simpa only [A, x, y] using hp
    fin_cases j
    · change 1 + 2 * x ≤ P
      nlinarith
    · change 1 - x + Real.sqrt 3 * y ≤ P
      nlinarith
    · change 1 - x - Real.sqrt 3 * y ≤ P
      nlinarith
  · rw [v4Normal_expansion]
    have hbase := permanent_ge_one_plus_D hA
    have hr := mul_nonneg (normSq_nonneg a) (normSq_nonneg f)
    have hs := mul_nonneg (normSq_nonneg b) (normSq_nonneg e)
    have ht := mul_nonneg (normSq_nonneg c) (normSq_nonneg d)
    let r := normSq a * normSq f
    let s := normSq b * normSq e
    let t := normSq c * normSq d
    let P := permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f)
    have hbase' : 1 + r + s + t ≤ P := by
      dsimp [r, s, t, P]
      rw [show 1 + normSq a * normSq f + normSq b * normSq e +
          normSq c * normSq d = 1 + D a b c d e f by
        simp only [D]
        ring]
      exact hbase
    change 0 ≤ r at hr
    change 0 ≤ s at hs
    change 0 ≤ t at ht
    fin_cases j
    · change 1 + r + s + t ≤ P
      exact hbase'
    · change 1 - r + s - t ≤ P
      nlinarith
    · change 1 + r - s - t ≤ P
      nlinarith
    · change 1 - r - s + t ≤ P
      nlinarith
  · rw [v4Disjoint_expansion]
    have hbase := FischerContractions.permanent_ge_matching_af hA
    have ha := normSq_nonneg a
    have hf := normSq_nonneg f
    have haf := mul_nonneg ha hf
    let r := normSq a
    let s := normSq f
    let P := permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f)
    have hbase' : 1 + r + s + r * s ≤ P := by
      dsimp [r, s, P]
      rw [show 1 + normSq a + normSq f + normSq a * normSq f =
          (1 + normSq a) * (1 + normSq f) by ring]
      exact hbase
    fin_cases j
    · change 1 + r + s + r * s ≤ P
      exact hbase'
    · change 1 - r + s - r * s ≤ P
      nlinarith
    · change 1 + r - s - r * s ≤ P
      nlinarith
    · change 1 - r - s + r * s ≤ P
      nlinarith
  · rw [s3_expansion]
    have hprincipal := principal012_contraction hA
    have hm := triangle_gap_minus hA
    have hp := triangle_gap_plus hA
    let x := (a * d * star b).re
    let A := normSq a + normSq b + normSq d
    let P := permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f)
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (add_nonneg (normSq_nonneg a) (normSq_nonneg b))
        (normSq_nonneg d)
    have hprincipal' : 1 + A + 2 * x ≤ P := by
      dsimp only [A, P]
      rw [show 1 + (normSq a + normSq b + normSq d) + 2 * x =
          principalPermanent012 a b d by
        dsimp only [x]
        simp only [principalPermanent012]
        ring]
      exact hprincipal
    have htriangle : 0 ≤ A + 3 * x := by
      dsimp [A, x] at hm hp ⊢
      linarith
    have hxraw :
        (a.re * d.re - a.im * d.im) * b.re +
            (a.re * d.im + a.im * d.re) * b.im = x := by
      dsimp only [x]
      simp [Complex.star_def, Complex.mul_re, Complex.mul_im]
    have hAeq : normSq a + normSq b + normSq d = A := rfl
    fin_cases j
    · change principalPermanent012 a b d ≤ P
      exact hprincipal
    · simp only [s3RowReal]
      norm_num [Fin.mk.injEq]
      rw [hxraw]
      nlinarith [hAeq]
    · simp only [s3RowReal]
      norm_num [Fin.mk.injEq]
      rw [hxraw]
      nlinarith

/-- Full-cone dominance for every row in one of the seven low-order tables. -/
theorem tableDominates
    (k : SubgroupKind)
    (hk : k = .trivial ∨ k = .c2Transposition ∨ k = .c2DoubleTransposition ∨
      k = .c3 ∨ k = .v4Normal ∨ k = .v4Disjoint ∨ k = .s3)
    (j : Fin (rowCount k)) : (rowOfIndex k j).TableDominates := by
  apply CorrelationLift.tableDominates_of_correlation
  intro a b c d e f hA
  rw [IrrepDatum.tableGap, sub_nonneg]
  exact correlation_dominance k hk j a b c d e f hA

end PermanentalDominance.N4.LowOrderRegistry
