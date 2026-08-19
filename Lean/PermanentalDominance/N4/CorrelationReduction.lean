import PermanentalDominance.PSD

/-!
# Four by four correlation coordinates

All explicit analytic case checks use the same six upper-triangular
coordinates.  Keeping this matrix and its elementary consequences in one
place prevents the case files from silently choosing incompatible edge
orders.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.CorrelationReduction

/-- A Hermitian `4 × 4` matrix with diagonal one, in edge order
`01, 02, 03, 12, 13, 23`. -/
def correlation (a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  1, a, b, c;
  star a, 1, d, e;
  star b, star d, 1, f;
  star c, star e, star f, 1]

theorem correlation_isHermitian (a b c d e f : ℂ) :
    (correlation a b c d e f).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [correlation]

/-- Every positive-semidefinite matrix with unit diagonal is definitionally
captured by the six correlation coordinates. -/
theorem eq_correlation_of_diagonal_one
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A)
    (hdiag : ∀ i : Fin 4, A i i = 1) :
    A = correlation (A 0 1) (A 0 2) (A 0 3) (A 1 2) (A 1 3) (A 2 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlation, hdiag, hA.isHermitian.apply]

theorem diagonal_one_correlation_psd
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A)
    (hdiag : ∀ i : Fin 4, A i i = 1) :
    IsPSD (correlation (A 0 1) (A 0 2) (A 0 3) (A 1 2) (A 1 3) (A 2 3)) := by
  rw [← eq_correlation_of_diagonal_one hA hdiag]
  exact hA

private theorem edge_normSq_le_one_aux
    {a b c d e f : ℂ} (hA : IsPSD (correlation a b c d e f))
    (x : Fin 4 → ℂ) (z : ℂ)
    (hform : (dotProduct (star x) (correlation a b c d e f *ᵥ x)).re =
      1 - normSq z) : normSq z ≤ 1 := by
  have hq := hA.re_dotProduct_nonneg x
  have hz : 0 ≤ 1 - normSq z := by
    rw [← hform]
    exact hq
  linarith

theorem normSq_a_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq a ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![-a, 1, 0, 0] a
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem normSq_b_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq b ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![-b, 0, 1, 0] b
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem normSq_c_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq c ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![-c, 0, 0, 1] c
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem normSq_d_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq d ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![0, -d, 1, 0] d
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem normSq_e_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq e ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![0, -e, 0, 1] e
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem normSq_f_le_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) : normSq f ≤ 1 := by
  apply edge_normSq_le_one_aux hA ![0, 0, -f, 1] f
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring

end PermanentalDominance.N4.CorrelationReduction
