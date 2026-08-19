import PermanentalDominance.N4.A4GeometricQuadratic
import PermanentalDominance.GramExtension

/-!
# Completing the non-collinear geometric quadratic

This module turns the positive coordinate Hessian into the exact lower bound
needed by the Gram argument.  The minimizing point is written with
`adjugate T`; its value is the previously certified numerator `N / det T`.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4GeometricMinimum

open A4GeometricGeneral A4GeometricHessian A4GeometricNoncollinear
open A4GeometricNormalization A4GeometricQuadratic
open PermanentalDominance.GramExtension

theorem coordinateHessian_det_full (a b r s : ℝ) :
    (coordinateHessian a b r s).det =
      (gramDefect a b r s : ℂ) * (T a b r s).det := by
  rw [coordinateHessian, Matrix.det_mul, G_det]

/-- In the non-collinear region `det T` is real. -/
theorem T_det_eq_re
    {a b r s : ℝ} (ha : 0 < a) (hδ : 0 < gramDefect a b r s) :
    (T a b r s).det = ((T a b r s).det.re : ℂ) := by
  have hQdet : 0 < (coordinateHessian a b r s).det :=
    (coordinateHessian_posDef ha hδ).det_pos
  have hQim : (coordinateHessian a b r s).det.im = 0 :=
    (RCLike.pos_iff.mp hQdet).2
  rw [coordinateHessian_det_full] at hQim
  have hTim : (T a b r s).det.im = 0 := by
    simp [Complex.mul_im] at hQim
    exact hQim.resolve_left hδ.ne'
  apply Complex.ext
  · rfl
  · simpa [hTim]

/-- The point at which the non-collinear coordinate quadratic is minimized. -/
def minimumPoint (a b r s : ℝ) : Fin 2 → ℂ :=
  -((((T a b r s).det.re : ℂ)⁻¹) •
    ((T a b r s).adjugate *ᵥ l a b r s))

theorem T_mulVec_minimumPoint
    {a b r s : ℝ} (ha : 0 < a) (hδ : 0 < gramDefect a b r s) :
    T a b r s *ᵥ minimumPoint a b r s = -l a b r s := by
  have hD : 0 < (T a b r s).det.re :=
    hessianDeterminant_pos ha hδ.le
  have hdet := T_det_eq_re ha hδ
  simp only [minimumPoint, Matrix.mulVec_neg, Matrix.mulVec_smul_assoc,
    Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec]
  rw [hdet]
  ext i
  simp [Pi.smul_apply]
  field_simp [hD.ne']

theorem coordinateHessian_mulVec_minimumPoint
    {a b r s : ℝ} (ha : 0 < a) (hδ : 0 < gramDefect a b r s) :
    coordinateHessian a b r s *ᵥ minimumPoint a b r s =
      -(G a b r s *ᵥ l a b r s) := by
  rw [coordinateHessian, ← Matrix.mulVec_mulVec,
    T_mulVec_minimumPoint ha hδ, Matrix.mulVec_neg]

/-- The completed-square constant is exactly the certified minimum
numerator divided by `det T`. -/
theorem minimumPoint_value
    {a b r s : ℝ} (ha : 0 < a) (hδ : 0 < gramDefect a b r s) :
    P0 a b r s +
        (dotProduct (star (G a b r s *ᵥ l a b r s))
          (minimumPoint a b r s)).re =
      N a b r s / (T a b r s).det.re := by
  let D := (T a b r s).det.re
  let S := dotProduct (star (l a b r s))
    ((G a b r s * (T a b r s).adjugate) *ᵥ l a b r s)
  have hD : 0 < D := hessianDeterminant_pos ha hδ.le
  have hmove :
      dotProduct (star (G a b r s *ᵥ l a b r s))
          ((T a b r s).adjugate *ᵥ l a b r s) = S := by
    dsimp [S]
    rw [← Matrix.mulVec_mulVec]
    exact hermitian_mulVec_dot (G_isHermitian a b r s)
      (l a b r s) ((T a b r s).adjugate *ᵥ l a b r s)
  have hlinear :
      (dotProduct (star (G a b r s *ᵥ l a b r s))
        (minimumPoint a b r s)).re = -S.re / D := by
    rw [minimumPoint]
    simp only [dotProduct_neg, dotProduct_smul, hmove]
    change (-(((D : ℂ)⁻¹) • S)).re = -S.re / D
    simp only [smul_eq_mul]
    norm_num [Complex.inv_re, Complex.inv_im, Complex.mul_re, hD.ne']
    field_simp [hD.ne']
  have hN : N a b r s = P0 a b r s * D - S.re := by
    dsimp [N, D, S]
    rw [T_det_eq_re ha hδ]
    simp
  rw [hlinear, hN]
  field_simp [hD.ne']
  ring

/-- Strict lower bound for the coordinate quadratic in the genuinely
non-collinear region. -/
theorem coordinateQuadratic_pos
    {a b r s : ℝ} (ha : 0 < a) (hδ : 0 < gramDefect a b r s)
    (z : Fin 2 → ℂ) :
    0 < P0 a b r s +
        2 * (dotProduct (star (G a b r s *ᵥ l a b r s)) z).re +
        (dotProduct (star z) (coordinateHessian a b r s *ᵥ z)).re := by
  have hQ := coordinateHessian_posDef ha hδ
  refine hermitian_quadratic_pos_of_minimum hQ.posSemidef
    (coordinateHessian_mulVec_minimumPoint ha hδ) ?_ z
  rw [minimumPoint_value ha hδ]
  exact div_pos (minimumNumerator_pos ha hδ)
    (hessianDeterminant_pos ha hδ.le)

/-- Split the normalized polynomial into the positive coordinate quadratic
and the nonnegative third-vector Gram slack. -/
theorem coordinateQuadratic_decomposition
    (a b c r s : ℝ) (z : Fin 2 → ℂ) :
    P0 a b r s +
        2 * (dotProduct (star (l a b r s))
          (G a b r s *ᵥ z)).re +
        geometricLambda a b r s * c +
        (dotProduct (star (G a b r s *ᵥ z))
          (M a b r s *ᵥ (G a b r s *ᵥ z))).re =
      (P0 a b r s +
        2 * (dotProduct (star (G a b r s *ᵥ l a b r s)) z).re +
        (dotProduct (star z) (coordinateHessian a b r s *ᵥ z)).re) +
      geometricLambda a b r s *
        (c - (dotProduct (star z) (G a b r s *ᵥ z)).re) := by
  have hG := G_isHermitian a b r s
  have hlin := hermitian_mulVec_dot hG (l a b r s) z
  have hmiddle := hermitian_mulVec_dot hG z
    (M a b r s *ᵥ (G a b r s *ᵥ z))
  have hQ : coordinateHessian a b r s *ᵥ z =
      (geometricLambda a b r s : ℂ) • (G a b r s *ᵥ z) +
        G a b r s *ᵥ (M a b r s *ᵥ (G a b r s *ᵥ z)) := by
    rw [coordinateHessian, ← Matrix.mulVec_mulVec, T,
      Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_smul_assoc]
  rw [hlin, hQ]
  simp only [dotProduct_add, dotProduct_smul, Complex.add_re,
    Complex.real_smul, smul_eq_mul]
  rw [← hmiddle]
  norm_num [Complex.mul_re]
  ring

/-- Nonnegativity of `geometricP` for a non-collinear Gram triple once the
third inner-product vector is expressed in the independent-pair coordinates. -/
theorem geometricP_nonneg_of_coordinates
    {a b c r s : ℝ} {p q : ℂ} (z : Fin 2 → ℂ)
    (ha : 0 < a) (hδ : 0 < gramDefect a b r s)
    (hz : thirdInner p q = G a b r s *ᵥ z)
    (hc : (dotProduct (star z) (G a b r s *ᵥ z)).re ≤ c) :
    0 ≤ geometricP a b c (g r s) p q := by
  have hb : 0 ≤ b := by
    dsimp [gramDefect] at hδ
    nlinarith [sq_nonneg r, sq_nonneg s]
  have hgram : r ^ 2 + s ^ 2 ≤ a * b := by
    dsimp [gramDefect] at hδ
    linarith
  have hlam : 0 < geometricLambda a b r s :=
    geometricLambda_pos ha.le hb hgram
  rw [geometricP_quadratic, hz,
    coordinateQuadratic_decomposition]
  exact add_nonneg
    (coordinateQuadratic_pos ha hδ z).le
    (mul_nonneg hlam.le (sub_nonneg.mpr hc))

end PermanentalDominance.N4.A4GeometricMinimum
