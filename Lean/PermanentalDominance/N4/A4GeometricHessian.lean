import PermanentalDominance.N4.A4GeometricAssembly

/-!
# Exact Hessian expansions for the geometric `A₄` proof

This module restores the non-collinear algebra from the lost geometric proof.
For the two-dimensional Gram matrix

`G = [[a, g], [star g, b]]`,  with  `g = r - i s`,

it defines the old rank-two perturbation `T = lambda I + M G`, its base
constant `P₀`, and the Schur-complement numerator

`N = Re(P₀ det T - l* G adj(T) l)`.

The two public expansion theorems identify, exactly and without positivity
assumptions, the coefficients of `a³ det T` and `a³ N` after substituting
`b = (r²+s²+delta)/a`.  Their coefficients are the scalar certificates from
`A4GeometricGram` and `A4GeometricGeneral`.

The sign in `g = r - i s` is intentional: `A4Certificate.omega` is the root
with negative imaginary part, whereas the old manuscript used the conjugate
root convention.
-/

noncomputable section

open Complex Matrix

namespace PermanentalDominance.N4.A4GeometricHessian

open PermanentalDominance.N4
open PermanentalDominance.N4.A4Certificate
open PermanentalDominance.N4.A4GeometricGeneral
open PermanentalDominance.N4.A4GeometricGram
open PermanentalDominance.N4.A4GeometricAssembly

/-- Off-diagonal Gram coordinate, conjugated to match the chosen `omega`. -/
def g (r s : ℝ) : ℂ := (r : ℂ) - (s : ℂ) * I

/-- The `2 × 2` Gram matrix of the independent pair. -/
def G (a b r s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![
  (a : ℂ), g r s;
  star (g r s), (b : ℂ)]

/-- The rank-two coefficient matrix in the old Hessian formula. -/
def M (a b r s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![
  (1 + b : ℝ), 2 - omega + (1 - omega) * g r s;
  2 - omega ^ 2 + (1 - omega ^ 2) * star (g r s), (1 + a : ℝ)]

/-- The Hessian `T = lambda I + M G` of the non-collinear quadratic. -/
def T (a b r s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((geometricLambda a b r s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
    M a b r s * G a b r s

private def TE (a b r s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![
  (geometricLambda a b r s : ℂ) + (1 + b : ℝ) * (a : ℂ) +
    (2 - omega + (1 - omega) * g r s) * star (g r s),
  (1 + b : ℝ) * g r s +
    (2 - omega + (1 - omega) * g r s) * (b : ℂ);
  (2 - omega ^ 2 + (1 - omega ^ 2) * star (g r s)) * (a : ℂ) +
    (1 + a : ℝ) * star (g r s),
  (geometricLambda a b r s : ℂ) +
    (2 - omega ^ 2 + (1 - omega ^ 2) * star (g r s)) * g r s +
      (1 + a : ℝ) * (b : ℂ)]

private theorem T_eq_TE (a b r s : ℝ) : T a b r s = TE a b r s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, TE, M, G, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Collinear constant term in the scaled determinant expansion. -/
def D0 (a r s : ℝ) : ℝ :=
  a ^ 3 * (T a ((r ^ 2 + s ^ 2) / a) r s).det.re

/-- Constant term `P₀` of the quadratic in the third Gram vector. -/
def P0 (a b r s : ℝ) : ℝ :=
  24 + 6 * (a + b + 2 * r) + a * b + (r ^ 2 + s ^ 2)

/-- Linear coefficient vector of the non-collinear quadratic. -/
def l (a b r s : ℝ) : Fin 2 → ℂ := ![
  6 + (2 - omega) * g r s + (2 - omega ^ 2) * (b : ℂ),
  6 + (2 - omega) * (a : ℂ) + (2 - omega ^ 2) * star (g r s)]

/-- Schur-complement numerator `Re(P₀ det T - l* G adj(T) l)`. -/
def N (a b r s : ℝ) : ℝ :=
  ((P0 a b r s : ℂ) * (T a b r s).det -
    dotProduct (star (l a b r s))
      ((G a b r s * (T a b r s).adjugate) *ᵥ l a b r s)).re

/-- Collinear constant term in the scaled numerator expansion. -/
def N0 (a r s : ℝ) : ℝ :=
  a ^ 3 * N a ((r ^ 2 + s ^ 2) / a) r s

set_option maxHeartbeats 2000000 in
theorem hessianDeterminant_expansion (a r s δ : ℝ) (ha : a ≠ 0) :
    a ^ 3 * (T a ((r ^ 2 + s ^ 2 + δ) / a) r s).det.re =
      determinantExpansion a r s δ (D0 a r s) := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have how2 : omega ^ 2 =
      ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith
  simp [T, M, G, g, geometricLambda, D0, determinantExpansion,
    determinantDeltaCoeff, determinantDeltaSqCoeff,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    omega, pow_two, Complex.I_mul_I, how2,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def]
  field_simp [ha]
  ring_nf
  rw [hsqrt]
  ring

private def NC3 (a : ℝ) : ℝ := a ^ 3 + 2 * a ^ 2 + 6 * a + 12

private def NC2 (a r s : ℝ) : ℝ :=
  -24 * Real.sqrt 3 * a * s - 36 * Real.sqrt 3 * s +
  2 * a ^ 3 - a ^ 2 * r ^ 2 - a ^ 2 * s ^ 2 + 16 * a ^ 2 +
  10 * a * r ^ 2 + 24 * a * r + 10 * a * s ^ 2 + 60 * a +
  18 * r ^ 2 + 84 * r + 18 * s ^ 2 + 120

private def NC1 (a r s : ℝ) : ℝ :=
  -24 * Real.sqrt 3 * a ^ 2 * s - 24 * Real.sqrt 3 * a * r ^ 2 * s -
  84 * Real.sqrt 3 * a * r * s - 24 * Real.sqrt 3 * a * s ^ 3 -
  168 * Real.sqrt 3 * a * s - 36 * Real.sqrt 3 * r ^ 2 * s -
  168 * Real.sqrt 3 * r * s - 36 * Real.sqrt 3 * s ^ 3 -
  240 * Real.sqrt 3 * s + 6 * a ^ 3 + 10 * a ^ 2 * r ^ 2 +
  24 * a ^ 2 * r + 10 * a ^ 2 * s ^ 2 + 60 * a ^ 2 +
  5 * a * r ^ 4 + 20 * a * r ^ 3 + 10 * a * r ^ 2 * s ^ 2 +
  22 * a * r ^ 2 + 20 * a * r * s ^ 2 + 72 * a * r +
  5 * a * s ^ 4 + 106 * a * s ^ 2 + 168 * a + 12 * r ^ 4 +
  108 * r ^ 3 + 24 * r ^ 2 * s ^ 2 + 372 * r ^ 2 +
  108 * r * s ^ 2 + 624 * r + 12 * s ^ 4 + 204 * s ^ 2 + 432

private def NC0 (a r s : ℝ) : ℝ :=
  -36 * Real.sqrt 3 * a ^ 2 * s - 36 * Real.sqrt 3 * a * r ^ 2 * s -
  168 * Real.sqrt 3 * a * r * s - 36 * Real.sqrt 3 * a * s ^ 3 -
  240 * Real.sqrt 3 * a * s - 12 * Real.sqrt 3 * r ^ 4 * s -
  108 * Real.sqrt 3 * r ^ 3 * s - 24 * Real.sqrt 3 * r ^ 2 * s ^ 3 -
  372 * Real.sqrt 3 * r ^ 2 * s - 108 * Real.sqrt 3 * r * s ^ 3 -
  624 * Real.sqrt 3 * r * s - 12 * Real.sqrt 3 * s ^ 5 -
  132 * Real.sqrt 3 * s ^ 3 - 432 * Real.sqrt 3 * s +
  12 * a ^ 3 + 18 * a ^ 2 * r ^ 2 + 84 * a ^ 2 * r +
  18 * a ^ 2 * s ^ 2 + 120 * a ^ 2 + 12 * a * r ^ 4 +
  108 * a * r ^ 3 + 24 * a * r ^ 2 * s ^ 2 + 372 * a * r ^ 2 +
  108 * a * r * s ^ 2 + 624 * a * r + 12 * a * s ^ 4 +
  204 * a * s ^ 2 + 432 * a + 7 * r ^ 6 + 88 * r ^ 5 +
  21 * r ^ 4 * s ^ 2 + 478 * r ^ 4 + 176 * r ^ 3 * s ^ 2 +
  1404 * r ^ 3 + 21 * r ^ 2 * s ^ 4 + 584 * r ^ 2 * s ^ 2 +
  2352 * r ^ 2 + 88 * r * s ^ 4 + 876 * r * s ^ 2 + 2160 * r +
  7 * s ^ 6 + 106 * s ^ 4 + 576 * s ^ 2 + 864

private def NP (a b r s : ℝ) : ℝ :=
  NC0 a r s + b * NC1 a r s + b ^ 2 * NC2 a r s + b ^ 3 * NC3 a

private def t00 (a b r s : ℝ) : ℂ := TE a b r s 0 0
private def t01 (a b r s : ℝ) : ℂ := TE a b r s 0 1
private def t10 (a b r s : ℝ) : ℂ := TE a b r s 1 0
private def t11 (a b r s : ℝ) : ℂ := TE a b r s 1 1
private def ell0 (a b r s : ℝ) : ℂ := l a b r s 0
private def ell1 (a b r s : ℝ) : ℂ := l a b r s 1

private def t00Re (a b r s : ℝ) : ℝ :=
  (-3 * Real.sqrt 3 * s + 2 * a * b + 4 * a + 2 * b +
    5 * r ^ 2 + 15 * r + 5 * s ^ 2 + 12) / 2

private def t00Im (r s : ℝ) : ℝ :=
  (Real.sqrt 3 * r ^ 2 + Real.sqrt 3 * r +
    Real.sqrt 3 * s ^ 2 + 5 * s) / 2

private def t01Re (b r s : ℝ) : ℝ :=
  (Real.sqrt 3 * b * s + 5 * b * r + 5 * b + 2 * r) / 2

private def t01Im (b r s : ℝ) : ℝ :=
  (Real.sqrt 3 * b * r + Real.sqrt 3 * b - 5 * b * s - 2 * s) / 2

private def t10Re (a r s : ℝ) : ℝ :=
  (Real.sqrt 3 * a * s + 5 * a * r + 5 * a + 2 * r) / 2

private def t10Im (a r s : ℝ) : ℝ :=
  (-Real.sqrt 3 * a * r - Real.sqrt 3 * a + 5 * a * s + 2 * s) / 2

private def t11Re (a b r s : ℝ) : ℝ :=
  (-3 * Real.sqrt 3 * s + 2 * a * b + 2 * a + 4 * b +
    5 * r ^ 2 + 15 * r + 5 * s ^ 2 + 12) / 2

private def t11Im (r s : ℝ) : ℝ := -t00Im r s

private def ell0Re (b r s : ℝ) : ℝ :=
  (12 + 5 * r + Real.sqrt 3 * s + 5 * b) / 2

private def ell0Im (b r s : ℝ) : ℝ :=
  (Real.sqrt 3 * r - 5 * s - Real.sqrt 3 * b) / 2

private def ell1Re (a r s : ℝ) : ℝ :=
  (12 + 5 * a + 5 * r + Real.sqrt 3 * s) / 2

private def ell1Im (a r s : ℝ) : ℝ :=
  (Real.sqrt 3 * a + 5 * s - Real.sqrt 3 * r) / 2

private theorem omega_sq_explicit : omega ^ 2 =
    ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem t00_explicit (a b r s : ℝ) :
    t00 a b r s = (t00Re a b r s : ℂ) + (t00Im r s : ℂ) * I := by
  simp [t00, TE, g, geometricLambda, t00Re, t00Im, omega,
    Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem t01_explicit (a b r s : ℝ) :
    t01 a b r s = (t01Re b r s : ℂ) + (t01Im b r s : ℂ) * I := by
  simp [t01, TE, g, t01Re, t01Im, omega,
    Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem t10_explicit (a b r s : ℝ) :
    t10 a b r s = (t10Re a r s : ℂ) + (t10Im a r s : ℂ) * I := by
  rw [show t10 a b r s =
      (2 - omega ^ 2 + (1 - omega ^ 2) * star (g r s)) * (a : ℂ) +
        (1 + a : ℝ) * star (g r s) by rfl]
  rw [omega_sq_explicit]
  simp [g, t10Re, t10Im, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem t11_explicit (a b r s : ℝ) :
    t11 a b r s = (t11Re a b r s : ℂ) + (t11Im r s : ℂ) * I := by
  rw [show t11 a b r s =
      (geometricLambda a b r s : ℂ) +
        (2 - omega ^ 2 + (1 - omega ^ 2) * star (g r s)) * g r s +
          (1 + a : ℝ) * (b : ℂ) by rfl]
  rw [omega_sq_explicit]
  simp [g, geometricLambda, t11Re, t11Im, t00Im,
    Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem ell0_explicit (a b r s : ℝ) :
    ell0 a b r s = (ell0Re b r s : ℂ) + (ell0Im b r s : ℂ) * I := by
  rw [show ell0 a b r s =
      6 + (2 - omega) * g r s + (2 - omega ^ 2) * (b : ℂ) by rfl]
  rw [omega_sq_explicit]
  simp [g, ell0Re, ell0Im, omega, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem ell1_explicit (a b r s : ℝ) :
    ell1 a b r s = (ell1Re a r s : ℂ) + (ell1Im a r s : ℂ) * I := by
  rw [show ell1 a b r s =
      6 + (2 - omega) * (a : ℂ) + (2 - omega ^ 2) * star (g r s) by rfl]
  rw [omega_sq_explicit]
  simp [g, ell1Re, ell1Im, omega, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private def NE (a b r s : ℝ) : ℝ :=
  ((P0 a b r s : ℂ) *
      (t00 a b r s * t11 a b r s - t01 a b r s * t10 a b r s) -
    (star (ell0 a b r s) *
        (((a : ℂ) * t11 a b r s - g r s * t10 a b r s) * ell0 a b r s +
          (-((a : ℂ) * t01 a b r s) + g r s * t00 a b r s) * ell1 a b r s) +
      star (ell1 a b r s) *
        ((star (g r s) * t11 a b r s - (b : ℂ) * t10 a b r s) * ell0 a b r s +
          (-(star (g r s) * t01 a b r s) + (b : ℂ) * t00 a b r s) *
            ell1 a b r s))).re

private theorem N_eq_NE (a b r s : ℝ) : N a b r s = NE a b r s := by
  unfold N
  rw [T_eq_TE]
  simp [NE, t00, t01, t10, t11, ell0, ell1,
    Matrix.det_fin_two, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, G]
  ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
private theorem NE_eq_NP (a b r s : ℝ) : NE a b r s = NP a b r s := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  rw [show NE a b r s =
      ((P0 a b r s : ℂ) *
          (t00 a b r s * t11 a b r s - t01 a b r s * t10 a b r s) -
        (star (ell0 a b r s) *
            (((a : ℂ) * t11 a b r s - g r s * t10 a b r s) * ell0 a b r s +
              (-((a : ℂ) * t01 a b r s) + g r s * t00 a b r s) *
                ell1 a b r s) +
          star (ell1 a b r s) *
            ((star (g r s) * t11 a b r s - (b : ℂ) * t10 a b r s) *
                ell0 a b r s +
              (-(star (g r s) * t01 a b r s) + (b : ℂ) * t00 a b r s) *
                ell1 a b r s))).re by rfl]
  rw [t00_explicit, t01_explicit, t10_explicit, t11_explicit,
    ell0_explicit, ell1_explicit]
  simp only [NP, NC0, NC1, NC2, NC3, P0, g,
    t00Re, t00Im, t01Re, t01Im, t10Re, t10Im,
    t11Re, t11Im, ell0Re, ell0Im, ell1Re, ell1Im]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub,
    one_mul, mul_one, neg_zero]
  ring_nf
  rw [hsqrt, hsqrt3]
  ring

private theorem N_eq_NP (a b r s : ℝ) : N a b r s = NP a b r s :=
  (N_eq_NE a b r s).trans (NE_eq_NP a b r s)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
private theorem NP_expand (a r s δ : ℝ) (ha : a ≠ 0) :
    a ^ 3 * NP a ((r ^ 2 + s ^ 2 + δ) / a) r s =
      minimumNumeratorExpansion a r s δ
        (a ^ 3 * NP a ((r ^ 2 + s ^ 2) / a) r s) := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  have hsqrt4 : (Real.sqrt 3) ^ 4 = 9 := by
    calc
      (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hsqrt]; norm_num
  simp [NP, NC0, NC1, NC2, NC3,
    minimumNumeratorExpansion, minimumLinearCoeff,
    coefficientOne, coefficientTwo, coefficientThree, coefficientFour,
    minimumDeltaSqCoeff, minimumDeltaCubeCoeff]
  field_simp [ha]
  ring_nf
  rw [hsqrt, hsqrt3, hsqrt4]
  ring

theorem minimumNumerator_expansion (a r s δ : ℝ) (ha : a ≠ 0) :
    a ^ 3 * N a ((r ^ 2 + s ^ 2 + δ) / a) r s =
      minimumNumeratorExpansion a r s δ (N0 a r s) := by
  rw [N_eq_NP]
  rw [NP_expand a r s δ ha]
  simp only [N0, N_eq_NP]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
/-- On the rank-one Gram boundary, the scaled minimum numerator is the
cleared-denominator discriminant of the scalar line quadratic. -/
theorem collinearNumerator_scaled_identity (a r s : ℝ) (ha : a ≠ 0) :
    a ^ 3 * N a ((r ^ 2 + s ^ 2) / a) r s =
      a ^ 2 * geometricLambda a ((r ^ 2 + s ^ 2) / a) r s *
        (a * P0 a ((r ^ 2 + s ^ 2) / a) r s *
            (2 * geometricLambda a ((r ^ 2 + s ^ 2) / a) r s - 6 +
              4 * (r ^ 2 + s ^ 2)) -
          normSq
            ((a : ℂ) * l a ((r ^ 2 + s ^ 2) / a) r s 0 +
              g r s * l a ((r ^ 2 + s ^ 2) / a) r s 1)) := by
  rw [N_eq_NP]
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  simp [NP, NC0, NC1, NC2, NC3, P0, l, g, geometricLambda,
    A4Certificate.omega, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def,
    pow_two, Complex.I_mul_I]
  field_simp [ha]
  ring_nf
  rw [hsqrt, hsqrt3]
  ring

end PermanentalDominance.N4.A4GeometricHessian
