import PermanentalDominance.N4.A4GeometricRankOne

/-!
# Scalar spine of the general geometric `A₄` argument

After the collinear case, the old proof fixes two residual Gram vectors and
writes the third-variable expression as a Hermitian quadratic.  The first
structural fact is strict positivity of its scalar part `lambda`.  This file
records that estimate directly from the `2 × 2` Gram constraint; no spectral
coefficient certificate is used.
-/

noncomputable section

namespace PermanentalDominance.N4.A4GeometricGeneral

/-- Scalar part of the Hessian in the old quadratic decomposition. -/
def geometricLambda (a b r s : ℝ) : ℝ :=
  6 + a + b + (r ^ 2 + s ^ 2) + 5 * r - Real.sqrt 3 * s

/-- The modulus variable used in the invariant form of the estimate. -/
def rho (r s : ℝ) : ℝ := Real.sqrt (r ^ 2 + s ^ 2)

theorem rho_nonneg (r s : ℝ) : 0 ≤ rho r s := Real.sqrt_nonneg _

theorem rho_sq (r s : ℝ) : rho r s ^ 2 = r ^ 2 + s ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg r) (sq_nonneg s))

/-- Cauchy's inequality for the linear form `(5, -sqrt 3)`. -/
theorem linearForm_lower (r s : ℝ) :
    -(2 * Real.sqrt 7 * rho r s) ≤ 5 * r - Real.sqrt 3 * s := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hrho := rho_sq r s
  have hsos := sq_nonneg (Real.sqrt 3 * r + 5 * s)
  have hsq : (5 * r - Real.sqrt 3 * s) ^ 2 ≤
      (2 * Real.sqrt 7 * rho r s) ^ 2 := by
    nlinarith
  have hright : 0 ≤ 2 * Real.sqrt 7 * rho r s :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (rho_nonneg _ _)
  exact (abs_le_of_sq_le_sq' hsq hright).1

/-- A `2 × 2` positive-semidefinite Gram constraint implies
`a + b ≥ 2 |g|`. -/
theorem two_mul_rho_le_add
    {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgram : r ^ 2 + s ^ 2 ≤ a * b) :
    2 * rho r s ≤ a + b := by
  have hr0 := rho_nonneg r s
  have hrsq := rho_sq r s
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsquare := sq_nonneg (a - b)
  have hsum0 : 0 ≤ a + b := add_nonneg ha hb
  nlinarith [sq_nonneg (a + b + 2 * rho r s)]

/-- Exact lower bound used in the old manuscript. -/
theorem geometricLambda_lower
    {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgram : r ^ 2 + s ^ 2 ≤ a * b) :
    (rho r s - (Real.sqrt 7 - 1)) ^ 2 +
        2 * (Real.sqrt 7 - 1) ≤ geometricLambda a b r s := by
  have h7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hab := two_mul_rho_le_add ha hb hgram
  have hlin := linearForm_lower r s
  have hrsq := rho_sq r s
  dsimp [geometricLambda]
  nlinarith

/-- Strict positivity of the general-case Hessian scalar. -/
theorem geometricLambda_pos
    {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgram : r ^ 2 + s ^ 2 ≤ a * b) :
    0 < geometricLambda a b r s := by
  have h7lt : 1 < Real.sqrt 7 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)
  have hlower := geometricLambda_lower ha hb hgram
  have hsquare := sq_nonneg (rho r s - (Real.sqrt 7 - 1))
  nlinarith

/-! ## Exact two-variable completions used by the determinant/minimum proof -/

/-- Strict positivity criterion for an isotropic real quadratic in two
variables.  The displayed residual is precisely the Schur complement of the
quadratic coefficient. -/
theorem real_quadratic_two_pos
    {Q Lr Ls C r s : ℝ} (hQ : 0 < Q)
    (hres : 0 < 4 * Q * C - Lr ^ 2 - Ls ^ 2) :
    0 < Q * (r ^ 2 + s ^ 2) + Lr * r + Ls * s + C := by
  have hsq1 := sq_nonneg (2 * Q * r + Lr)
  have hsq2 := sq_nonneg (2 * Q * s + Ls)
  have hid :
      4 * Q * (Q * (r ^ 2 + s ^ 2) + Lr * r + Ls * s + C) =
        (2 * Q * r + Lr) ^ 2 + (2 * Q * s + Ls) ^ 2 +
          (4 * Q * C - Lr ^ 2 - Ls ^ 2) := by ring
  nlinarith [mul_pos (by positivity : 0 < 4 * Q) hres]

/-- The coefficient called `D₁` after substituting
`b = (r²+s²+delta)/a` in the old Hessian determinant. -/
def determinantDeltaCoeff (a r s : ℝ) : ℝ :=
  a * ((4 + 11 * a) * (r ^ 2 + s ^ 2) +
    a * (20 + a) * r - Real.sqrt 3 * a * (4 + 3 * a) * s +
    a * (18 + 10 * a + 3 * a ^ 2))

/-- Exact completed-square residual for `D₁`. -/
theorem determinantDeltaCoeff_residual (a : ℝ) :
    4 * (4 + 11 * a) * (a * (18 + 10 * a + 3 * a ^ 2)) -
        (a * (20 + a)) ^ 2 -
        (-Real.sqrt 3 * a * (4 + 3 * a)) ^ 2 =
      4 * a * (72 + 126 * a + 94 * a ^ 2 + 26 * a ^ 3) := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem determinantDeltaCoeff_pos
    {a r s : ℝ} (ha : 0 < a) : 0 < determinantDeltaCoeff a r s := by
  let Q : ℝ := 4 + 11 * a
  let Lr : ℝ := a * (20 + a)
  let Ls : ℝ := -Real.sqrt 3 * a * (4 + 3 * a)
  let C : ℝ := a * (18 + 10 * a + 3 * a ^ 2)
  have hQ : 0 < Q := by dsimp [Q]; nlinarith
  have hpoly : 0 < 72 + 126 * a + 94 * a ^ 2 + 26 * a ^ 3 := by
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha.le _
    nlinarith
  have hres : 0 < 4 * Q * C - Lr ^ 2 - Ls ^ 2 := by
    dsimp [Q, Lr, Ls, C]
    rw [determinantDeltaCoeff_residual]
    positivity
  have hquad := real_quadratic_two_pos (r := r) (s := s) hQ hres
  dsimp [Q, Lr, Ls, C] at hquad
  have hquad' : 0 <
      (4 + 11 * a) * (r ^ 2 + s ^ 2) +
        a * (20 + a) * r - Real.sqrt 3 * a * (4 + 3 * a) * s +
        a * (18 + 10 * a + 3 * a ^ 2) := by
    convert hquad using 1 <;> ring
  dsimp [determinantDeltaCoeff]
  exact mul_pos ha hquad'

/-- The coefficient `N₂` in the old minimum numerator. -/
def minimumDeltaSqCoeff (a r s : ℝ) : ℝ :=
  36 * (r ^ 2 + s ^ 2) +
    a * (120 + 84 * r - 36 * Real.sqrt 3 * s +
      36 * (r ^ 2 + s ^ 2)) +
    a ^ 2 * (60 + 24 * r - 24 * Real.sqrt 3 * s +
      16 * (r ^ 2 + s ^ 2)) +
    a ^ 3 * (16 + 2 * (r ^ 2 + s ^ 2)) + 2 * a ^ 4

theorem minimumDeltaSqCoeff_collected (a r s : ℝ) :
    minimumDeltaSqCoeff a r s =
      (36 + 36 * a + 16 * a ^ 2 + 2 * a ^ 3) * (r ^ 2 + s ^ 2) +
      (84 * a + 24 * a ^ 2) * r -
      Real.sqrt 3 * (36 * a + 24 * a ^ 2) * s +
      (120 * a + 60 * a ^ 2 + 16 * a ^ 3 + 2 * a ^ 4) := by
  dsimp [minimumDeltaSqCoeff]
  ring

theorem minimumDeltaSqCoeff_residual (a : ℝ) :
    let Q := 36 + 36 * a + 16 * a ^ 2 + 2 * a ^ 3
    let Lr := 84 * a + 24 * a ^ 2
    let Ls := -Real.sqrt 3 * (36 * a + 24 * a ^ 2)
    let C := 120 * a + 60 * a ^ 2 + 16 * a ^ 3 + 2 * a ^ 4
    4 * Q * C - Lr ^ 2 - Ls ^ 2 =
      16 * a * (a ^ 6 + 16 * a ^ 5 + 112 * a ^ 4 + 318 * a ^ 3 +
        588 * a ^ 2 + 936 * a + 1080) := by
  dsimp
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem minimumDeltaSqCoeff_pos
    {a r s : ℝ} (ha : 0 < a) : 0 < minimumDeltaSqCoeff a r s := by
  let Q : ℝ := 36 + 36 * a + 16 * a ^ 2 + 2 * a ^ 3
  let Lr : ℝ := 84 * a + 24 * a ^ 2
  let Ls : ℝ := -Real.sqrt 3 * (36 * a + 24 * a ^ 2)
  let C : ℝ := 120 * a + 60 * a ^ 2 + 16 * a ^ 3 + 2 * a ^ 4
  have hQ : 0 < Q := by
    dsimp [Q]
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha.le _
    nlinarith
  have hpoly : 0 < a ^ 6 + 16 * a ^ 5 + 112 * a ^ 4 + 318 * a ^ 3 +
      588 * a ^ 2 + 936 * a + 1080 := by
    have ha2 : 0 ≤ a ^ 2 := pow_nonneg ha.le _
    have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha.le _
    have ha4 : 0 ≤ a ^ 4 := pow_nonneg ha.le _
    have ha5 : 0 ≤ a ^ 5 := pow_nonneg ha.le _
    have ha6 : 0 ≤ a ^ 6 := pow_nonneg ha.le _
    nlinarith
  have hres : 0 < 4 * Q * C - Lr ^ 2 - Ls ^ 2 := by
    rw [show 4 * Q * C - Lr ^ 2 - Ls ^ 2 =
        16 * a * (a ^ 6 + 16 * a ^ 5 + 112 * a ^ 4 + 318 * a ^ 3 +
          588 * a ^ 2 + 936 * a + 1080) by
      simpa [Q, Lr, Ls, C] using minimumDeltaSqCoeff_residual a]
    positivity
  have hquad := real_quadratic_two_pos (r := r) (s := s) hQ hres
  rw [minimumDeltaSqCoeff_collected]
  simpa [Q, Lr, Ls, C, sub_eq_add_neg] using hquad

end PermanentalDominance.N4.A4GeometricGeneral
