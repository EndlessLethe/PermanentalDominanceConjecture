import PermanentalDominance.N4.DiagonalScaling
import PermanentalDominance.N4.CorrelationReduction
import Mathlib.Data.Complex.BigOperators

/-!
# Lifting correlation inequalities to the full positive-semidefinite cone

Every nonzero diagonal entry of a positive-semidefinite matrix is a positive
real number.  Congruence by its inverse square root therefore produces a
correlation matrix.  Both the permanent and every normalized table matrix
function acquire the same homogeneous factor under the inverse congruence.

If a diagonal entry vanishes, its entire row and column vanish, so both
matrix functions are zero.  Thus no limiting argument and no invertibility
assumption on the original matrix are needed.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.CorrelationLift

open CorrelationReduction DiagonalScaling

/-- The real part of a diagonal entry of a PSD matrix is nonnegative. -/
theorem diagonal_re_nonneg {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A)
    (i : Fin 4) : 0 ≤ (A i i).re := by
  have h := hA.re_dotProduct_nonneg (Pi.single i 1)
  simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
    single_dotProduct, one_mul, Matrix.transpose_apply] using h

/-- A nonzero diagonal entry of a PSD matrix has strictly positive real part. -/
theorem diagonal_re_pos_of_ne_zero {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (i : Fin 4) (hii : A i i ≠ 0) :
    0 < (A i i).re := by
  have hre := diagonal_re_nonneg hA i
  have hreal := hA.isHermitian.coe_re_apply_self i
  have hrne : (A i i).re ≠ 0 := by
    intro hr
    apply hii
    calc
      A i i = ((A i i).re : ℂ) := hreal.symm
      _ = 0 := by rw [hr]; norm_num
  exact lt_of_le_of_ne hre (Ne.symm hrne)

/-- Positive diagonal square roots. -/
def diagonalSqrt (A : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4) : ℝ :=
  Real.sqrt (A i i).re

/-- Reciprocal diagonal square roots used to normalize a PSD matrix. -/
def inverseDiagonalSqrt (A : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4) : ℝ :=
  1 / diagonalSqrt A i

/-- Diagonal congruence normalization. -/
def normalizeMatrix (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  scaleMatrix (inverseDiagonalSqrt A) A

theorem normalizeMatrix_psd {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) : IsPSD (normalizeMatrix A) :=
  scaleMatrix_psd hA _

theorem diagonalSqrt_pos {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (hne : ∀ i : Fin 4, A i i ≠ 0) (i : Fin 4) :
    0 < diagonalSqrt A i := by
  exact Real.sqrt_pos.2 (diagonal_re_pos_of_ne_zero hA i (hne i))

theorem diagonalSqrt_mul_inverse {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (hne : ∀ i : Fin 4, A i i ≠ 0) (i : Fin 4) :
    diagonalSqrt A i * inverseDiagonalSqrt A i = 1 := by
  have hsne : diagonalSqrt A i ≠ 0 := ne_of_gt (diagonalSqrt_pos hA hne i)
  simp [inverseDiagonalSqrt, hsne]

/-- With nonzero diagonal, the normalized matrix has diagonal one. -/
theorem normalizeMatrix_diagonal_one {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (hne : ∀ i : Fin 4, A i i ≠ 0) (i : Fin 4) :
    normalizeMatrix A i i = 1 := by
  have hre := diagonal_re_nonneg hA i
  have hreal := hA.isHermitian.coe_re_apply_self i
  have hspos := diagonalSqrt_pos hA hne i
  have hsne : diagonalSqrt A i ≠ 0 := ne_of_gt hspos
  have hsquare : (diagonalSqrt A i) ^ 2 = (A i i).re := by
    exact Real.sq_sqrt hre
  have hscalar : inverseDiagonalSqrt A i * (A i i).re *
      inverseDiagonalSqrt A i = 1 := by
    dsimp [inverseDiagonalSqrt]
    field_simp
    nlinarith [hsquare]
  rw [normalizeMatrix, scaleMatrix_apply, ← hreal]
  calc
    (inverseDiagonalSqrt A i : ℂ) * ((A i i).re : ℂ) *
        (inverseDiagonalSqrt A i : ℂ) =
      ((inverseDiagonalSqrt A i * (A i i).re *
        inverseDiagonalSqrt A i : ℝ) : ℂ) := by norm_num
    _ = 1 := by rw [hscalar]; norm_num

/-- Scaling the normalized matrix back by the diagonal square roots recovers
the original matrix. -/
theorem scale_normalizeMatrix {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (hne : ∀ i : Fin 4, A i i ≠ 0) :
    scaleMatrix (diagonalSqrt A) (normalizeMatrix A) = A := by
  ext i j
  have hiR := diagonalSqrt_mul_inverse hA hne i
  have hjR := diagonalSqrt_mul_inverse hA hne j
  have hi : (diagonalSqrt A i : ℂ) * (inverseDiagonalSqrt A i : ℂ) = 1 := by
    exact_mod_cast hiR
  have hj : (inverseDiagonalSqrt A j : ℂ) * (diagonalSqrt A j : ℂ) = 1 := by
    exact_mod_cast (by simpa [mul_comm] using hjR)
  simp only [scaleMatrix_apply, normalizeMatrix]
  calc
    (diagonalSqrt A i : ℂ) *
          ((inverseDiagonalSqrt A i : ℂ) * A i j *
            (inverseDiagonalSqrt A j : ℂ)) *
        (diagonalSqrt A j : ℂ) =
        ((diagonalSqrt A i : ℂ) * (inverseDiagonalSqrt A i : ℂ)) *
          A i j *
          ((inverseDiagonalSqrt A j : ℂ) * (diagonalSqrt A j : ℂ)) := by
            ring
    _ = A i j := by rw [hi, hj]; ring

/-- The real gap has homogeneous degree eight under real diagonal
congruence.  The normalization by `row.degree` is already built into
`tableMatrixFunction`, so it acquires exactly the same factor as the
permanent. -/
theorem tableGap_scale {H : Subgroup S4} (row : IrrepDatum H)
    (s : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    row.tableGap (scaleMatrix s A) =
      (∏ i, s i) ^ 2 * row.tableGap A := by
  let p : ℝ := ∏ i, s i
  have hprod : (∏ i, (s i : ℂ)) = (p : ℂ) := by
    dsimp [p]
    norm_cast
  have hre : ((∏ i, (s i : ℂ)) ^ 2).re = p ^ 2 := by
    rw [hprod]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : ((∏ i, (s i : ℂ)) ^ 2).im = 0 := by
    rw [hprod]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [IrrepDatum.tableGap, permanent_scale,
    tableMatrixFunction_scale]
  simp only [Complex.mul_re]
  rw [hre, him]
  simp [IrrepDatum.tableGap]
  dsimp [p]
  ring

/-- A dominance proof for all correlation matrices lifts to the full PSD
cone, including matrices with zero diagonal. -/
theorem tableDominates_of_correlation {H : Subgroup S4} (row : IrrepDatum H)
    (hcorr : ∀ a b c d e f : ℂ,
      IsPSD (correlation a b c d e f) →
        0 ≤ row.tableGap (correlation a b c d e f)) :
    row.TableDominates := by
  intro A hA
  by_cases hz : ∃ i : Fin 4, A i i = 0
  · rcases hz with ⟨i, hii⟩
    rw [IrrepDatum.tableGap,
      permanent_eq_zero_of_diagonal_eq_zero hA i hii,
      tableMatrixFunction_eq_zero_of_diagonal_eq_zero row hA i hii]
    norm_num
  · have hne : ∀ i : Fin 4, A i i ≠ 0 := by
      intro i hii
      exact hz ⟨i, hii⟩
    let C := normalizeMatrix A
    have hC : IsPSD C := by
      simpa [C] using normalizeMatrix_psd hA
    have hdiag : ∀ i : Fin 4, C i i = 1 := by
      intro i
      simpa [C] using normalizeMatrix_diagonal_one hA hne i
    have hgapC : 0 ≤ row.tableGap C := by
      rw [eq_correlation_of_diagonal_one hC hdiag]
      exact hcorr _ _ _ _ _ _
        (diagonal_one_correlation_psd hC hdiag)
    have hrecover : scaleMatrix (diagonalSqrt A) C = A := by
      simpa [C] using scale_normalizeMatrix hA hne
    rw [← hrecover, tableGap_scale]
    exact mul_nonneg (sq_nonneg _) hgapC

end PermanentalDominance.N4.CorrelationLift
