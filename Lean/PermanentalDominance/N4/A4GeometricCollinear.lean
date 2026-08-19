import PermanentalDominance.N4.A4GeometricHessian

/-!
# Collinear boundary constants for the geometric `A₄` proof

The exact Hessian expansions use two constant terms, `D0` and `N0`, obtained
when the Gram defect `δ = ab - |g|²` vanishes.  This module connects those
constants to the independently verified rank-one branch.
-/

noncomputable section

open Complex Matrix

namespace PermanentalDominance.N4.A4GeometricCollinear

open A4GeometricGeneral A4GeometricHessian
open A4GeometricNormalization A4GeometricRankOne

/-- The second squared norm on the collinear boundary. -/
def collinearB (a r s : ℝ) : ℝ := (r ^ 2 + s ^ 2) / a

/-- The positive eigenvalue of the Hessian along the common Gram line. -/
def collinearH (a r s : ℝ) : ℝ :=
  2 * geometricLambda a (collinearB a r s) r s - 6 +
    4 * (r ^ 2 + s ^ 2)

theorem collinearB_nonneg {a r s : ℝ} (ha : 0 < a) :
    0 ≤ collinearB a r s :=
  div_nonneg (add_nonneg (sq_nonneg r) (sq_nonneg s)) ha.le

theorem collinear_gram_eq {a r s : ℝ} (ha : a ≠ 0) :
    a * collinearB a r s = r ^ 2 + s ^ 2 := by
  dsimp [collinearB]
  field_simp [ha]

/-- The line coefficient is strictly positive.  This is the invariant form
of the manuscript's
`6 |1 + conj α β|² + 2 |ω α + ω² β|² > 0`. -/
theorem collinearH_pos {a r s : ℝ} (ha : 0 < a) :
    0 < collinearH a r s := by
  have hb : 0 ≤ collinearB a r s := collinearB_nonneg ha
  have hgram : r ^ 2 + s ^ 2 ≤ a * collinearB a r s := by
    rw [collinear_gram_eq ha.ne']
  have hab := two_mul_rho_le_add ha.le hb hgram
  have hlin := linearForm_lower r s
  have hrho := rho_sq r s
  have hrho0 := rho_nonneg r s
  have h7sq : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7nonneg : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have h7lt : Real.sqrt 7 < 3 := by nlinarith
  have hsquare := sq_nonneg (3 * rho r s - 2)
  dsimp [collinearH, geometricLambda]
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Exact determinant constant on the rank-one Gram boundary. -/
theorem D0_eq (a r s : ℝ) (ha : a ≠ 0) :
    D0 a r s =
      a ^ 3 * geometricLambda a (collinearB a r s) r s *
        collinearH a r s := by
  simp [D0, T, M, G, g, collinearB, collinearH, geometricLambda,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    A4Certificate.omega, pow_two, Complex.I_mul_I,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def]
  field_simp [ha]
  ring_nf

/-- Strict positivity of the determinant constant required by the
non-collinear `δ` expansion. -/
theorem D0_pos {a r s : ℝ} (ha : 0 < a) :
    0 < D0 a r s := by
  rw [D0_eq a r s ha.ne']
  have hb : 0 ≤ collinearB a r s := collinearB_nonneg ha
  have hgram : r ^ 2 + s ^ 2 ≤ a * collinearB a r s := by
    rw [collinear_gram_eq ha.ne']
  have hlam := geometricLambda_pos ha.le hb hgram
  exact mul_pos (mul_pos (pow_pos ha _) hlam) (collinearH_pos ha)

/-- Scalar representatives of a rank-one Gram pair with invariants
`‖x‖² = a` and `star x * y = g`. -/
def collinearX (a : ℝ) : ℂ := (Real.sqrt a : ℂ)

def collinearY (a r s : ℝ) : ℂ :=
  g r s / (Real.sqrt a : ℂ)

/-- The line component of the linear coefficient in the third-vector
quadratic. -/
def collinearEll (a r s : ℝ) : ℂ :=
  collinearX a * l a (collinearB a r s) r s 0 +
    collinearY a r s * l a (collinearB a r s) r s 1

/-- Real and imaginary Gram coordinates in the Hessian convention
`g = r - i s`. -/
def rankOneR (x y : ℂ) : ℝ := (star x * y).re

def rankOneS (x y : ℂ) : ℝ := -(star x * y).im

/-- The scalar line component of the Hessian linear term. -/
def rankOneEll (x y : ℂ) : ℂ :=
  x * l (normSq x) (normSq y) (rankOneR x y) (rankOneS x y) 0 +
    y * l (normSq x) (normSq y) (rankOneR x y) (rankOneS x y) 1

/-- The coefficient of `normSq z` in the rank-one quadratic. -/
def rankOneH (x y : ℂ) : ℝ :=
  2 * geometricLambda (normSq x) (normSq y)
      (rankOneR x y) (rankOneS x y) -
    6 + 4 * normSq (star x * y)

set_option maxHeartbeats 3000000 in
/-- The normalized geometric polynomial on a scalar Gram line is exactly the
quadratic governed by the Hessian data. -/
theorem geometricP_rankOne_quadratic (x y z : ℂ) :
    geometricP
        (normSq x)
        (normSq y)
        (normSq z)
        (star x * y)
        (star x * z)
        (star y * z) =
      P0 (normSq x) (normSq y) (rankOneR x y) (rankOneS x y) +
        2 * (star (rankOneEll x y) * z).re +
        rankOneH x y * normSq z := by
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [rankOneR, rankOneS, rankOneEll, rankOneH,
    P0, l, g, geometricLambda, geometricP,
    symmetricTensorSumNormSq, symmetricTensorFourierNormSq, pairTensorDiag,
    tensorInner1213, tensorInner1223, tensorInner1323,
    geometricGamma, geometricTau,
    A4Certificate.omega, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def, pow_two, Complex.I_mul_I]
  ring_nf
  rw [hsqrt3]
  ring

theorem collinearX_normSq {a : ℝ} (ha : 0 ≤ a) :
    normSq (collinearX a) = a := by
  rw [show collinearX a = (Real.sqrt a : ℂ) by rfl,
    Complex.normSq_ofReal, Real.mul_self_sqrt ha]

theorem collinearY_normSq {a r s : ℝ} (ha : 0 < a) :
    normSq (collinearY a r s) = collinearB a r s := by
  rw [show collinearY a r s = g r s / (Real.sqrt a : ℂ) by rfl,
    Complex.normSq_div, Complex.normSq_ofReal]
  have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  rw [hsqa]
  simp [g, collinearB, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem collinearXY {a r s : ℝ} (ha : 0 < a) :
    star (collinearX a) * collinearY a r s = g r s := by
  have hsqrta : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr ha
  simp [collinearX, collinearY, Complex.star_def]
  field_simp [hsqrta]

/-- Exact rank-one specialization of the geometric polynomial as a scalar
quadratic in its third Gram vector. -/
theorem geometricP_collinear_quadratic
    (a r s : ℝ) (z : ℂ) (ha : 0 < a) :
    geometricP
        (normSq (collinearX a))
        (normSq (collinearY a r s))
        (normSq z)
        (star (collinearX a) * collinearY a r s)
        (star (collinearX a) * z)
        (star (collinearY a r s) * z) =
      P0 a (collinearB a r s) r s +
        2 * (star (collinearEll a r s) * z).re +
        collinearH a r s * normSq z := by
  have hx := collinearX_normSq ha.le
  have hy := collinearY_normSq (a := a) (r := r) (s := s) ha
  have hxy := collinearXY (a := a) (r := r) (s := s) ha
  have hr : rankOneR (collinearX a) (collinearY a r s) = r := by
    unfold rankOneR
    rw [hxy]
    simp [g]
  have hs : rankOneS (collinearX a) (collinearY a r s) = s := by
    unfold rankOneS
    rw [hxy]
    simp [g]
  have hab := collinear_gram_eq (a := a) (r := r) (s := s) ha.ne'
  simpa [rankOneEll, rankOneH, collinearEll, collinearH,
    hx, hy, hr, hs, hxy, hab] using
      geometricP_rankOne_quadratic
        (collinearX a) (collinearY a r s) z

/-- A nonnegative complex quadratic with positive leading coefficient has
nonpositive scalar discriminant. -/
theorem complex_quadratic_discriminant_of_nonneg
    {K C : ℝ} {L : ℂ} (hK : 0 < K)
    (hquad : ∀ z : ℂ,
      0 ≤ C + 2 * (star L * z).re + K * normSq z) :
    normSq L ≤ C * K := by
  have hz := hquad (-(L / (K : ℂ)))
  have hid :
      C + 2 * (star L * (-(L / (K : ℂ)))).re +
          K * normSq (-(L / (K : ℂ))) =
        (C * K - normSq L) / K := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def]
    field_simp [hK.ne']
    ring
  rw [hid] at hz
  rcases div_nonneg_iff.mp hz with hpos | hneg
  · exact sub_nonneg.mp hpos.1
  · exact False.elim ((not_le_of_gt hK) hneg.2)

/-- The collinear constant quadratic has nonpositive discriminant, directly
from the rank-one sum-of-squares theorem. -/
theorem collinear_discriminant_nonneg {a r s : ℝ} (ha : 0 < a) :
    normSq (collinearEll a r s) ≤
      P0 a (collinearB a r s) r s * collinearH a r s := by
  apply complex_quadratic_discriminant_of_nonneg (collinearH_pos ha)
  intro z
  rw [← geometricP_collinear_quadratic a r s z ha]
  exact geometricP_collinear_nonneg
    (collinearX a) (collinearY a r s) z

def collinearEllScaled (a r s : ℝ) : ℂ :=
  (a : ℂ) * l a (collinearB a r s) r s 0 +
    g r s * l a (collinearB a r s) r s 1

theorem collinearEllScaled_normSq (a r s : ℝ) (ha : 0 < a) :
    normSq (collinearEllScaled a r s) =
      a * normSq (collinearEll a r s) := by
  have hsqrta : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr ha
  have hsqa : Real.sqrt a * Real.sqrt a = a :=
    Real.mul_self_sqrt ha.le
  have hscaled :
      (Real.sqrt a : ℂ) * collinearEll a r s =
        collinearEllScaled a r s := by
    simp only [collinearEll, collinearEllScaled, collinearX, collinearY]
    field_simp [hsqrta]
    calc
      (Real.sqrt a : ℂ) * l a (collinearB a r s) r s 0 * Real.sqrt a =
          ((Real.sqrt a : ℂ) * Real.sqrt a) *
            l a (collinearB a r s) r s 0 := by ring
      _ = (a : ℂ) * l a (collinearB a r s) r s 0 := by
        rw [show (Real.sqrt a : ℂ) * Real.sqrt a = (a : ℂ) by
          exact_mod_cast hsqa]
  rw [← hscaled, Complex.normSq_mul, Complex.normSq_ofReal, hsqa]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
/-- Polynomial form of the collinear numerator identity, with the square-root
denominator cleared from the line component. -/
theorem N0_scaled_eq (a r s : ℝ) (ha : 0 < a) :
    N0 a r s =
      a ^ 2 * geometricLambda a (collinearB a r s) r s *
        (a * P0 a (collinearB a r s) r s * collinearH a r s -
          normSq (collinearEllScaled a r s)) := by
  simpa [N0, collinearB, collinearH, collinearEllScaled] using
    collinearNumerator_scaled_identity a r s ha.ne'

/-- The scaled collinear numerator is the discriminant residual of the
rank-one quadratic. -/
theorem N0_eq (a r s : ℝ) (ha : 0 < a) :
    N0 a r s =
      a ^ 3 * geometricLambda a (collinearB a r s) r s *
        (P0 a (collinearB a r s) r s * collinearH a r s -
          normSq (collinearEll a r s)) := by
  rw [N0_scaled_eq a r s ha, collinearEllScaled_normSq a r s ha]
  ring

/-- Nonnegativity of the constant term in the minimum-numerator expansion. -/
theorem N0_nonneg {a r s : ℝ} (ha : 0 < a) :
    0 ≤ N0 a r s := by
  rw [N0_eq a r s ha]
  have hb : 0 ≤ collinearB a r s := collinearB_nonneg ha
  have hgram : r ^ 2 + s ^ 2 ≤ a * collinearB a r s := by
    rw [collinear_gram_eq ha.ne']
  exact mul_nonneg
    (mul_nonneg (pow_nonneg ha.le _)
      (geometricLambda_pos ha.le hb hgram).le)
    (sub_nonneg.mpr (collinear_discriminant_nonneg ha))

end PermanentalDominance.N4.A4GeometricCollinear
