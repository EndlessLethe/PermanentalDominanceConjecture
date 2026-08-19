import PermanentalDominance.PSD
import Mathlib.Analysis.MeanInequalities

/-!
# The non-real `A₄` certificate

This file records the corrected algebraic data for the last non-real-character case.  The root of
unity is chosen with **negative** imaginary part.  With the other primitive cube root, the signs in
the off-diagonal entries below must all be conjugated.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4Certificate

/-- The primitive cube root used by the certificate. -/
def omega : ℂ := (-1 / 2 : ℝ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I

/-- A normalized `3 × 3` Hermitian correlation matrix. -/
def correlation (u v w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![
  1, u, v;
  star u, 1, w;
  star v, star w, 1]

/-- The scalar part of the non-real `A₄` gap. -/
def c0 (u v w : ℂ) : ℝ :=
  normSq u + normSq v + normSq w +
    2 * ((1 - omega) * u * w * star v).re

/-- The corrected Schur-complement matrix. -/
def gapMatrix (u v w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![
  1,
    (1 - omega ^ 2) * u + v * star w,
    u * w + (1 - omega) * v;
  (1 - omega) * star u + w * star v,
    1,
    (1 - omega ^ 2) * w + v * star u;
  star u * star w + (1 - omega ^ 2) * star v,
    (1 - omega) * star w + u * star v,
    1]

/-- The matrix whose positivity closes the non-real-character `A₄` obstruction. -/
def certificate (u v w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (correlation u v w).det • gapMatrix u v w +
    (c0 u v w : ℂ) • (correlation u v w).adjugate

/-- The congruent form of the certificate in the positive-determinant case. -/
def interiorReduced (u v w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  correlation u v w * gapMatrix u v w * correlation u v w +
    (c0 u v w : ℂ) • correlation u v w

@[simp] theorem omega_re : omega.re = -1 / 2 := by
  simp [omega]

@[simp] theorem omega_im : omega.im = -(Real.sqrt 3 / 2) := by
  simp [omega]

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [omega] at this

@[simp] theorem star_omega : star omega = omega ^ 2 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

@[simp] theorem omega_cube : omega ^ 3 = 1 := by
  have h : omega ^ 3 - 1 = 0 := by
    calc
      omega ^ 3 - 1 = (omega - 1) * (omega ^ 2 + omega + 1) := by ring
      _ = 0 := by rw [omega_sq_add_omega_add_one, mul_zero]
  exact sub_eq_zero.mp h

@[simp] theorem omega_pow_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cube, one_mul]

theorem correlation_isHermitian (u v w : ℂ) : (correlation u v w).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [correlation]

theorem gapMatrix_isHermitian (u v w : ℂ) : (gapMatrix u v w).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapMatrix, star_omega, map_pow]
  all_goals ring_nf
  all_goals first | exact Or.inl omega_pow_four | rw [omega_pow_four]

theorem det_correlation_star (u v w : ℂ) :
    star (correlation u v w).det = (correlation u v w).det := by
  rw [← Matrix.det_conjTranspose, (correlation_isHermitian u v w).eq]

theorem certificate_isHermitian (u v w : ℂ) :
    (certificate u v w).IsHermitian := by
  rw [Matrix.IsHermitian, certificate, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    (gapMatrix_isHermitian u v w).eq,
    (correlation_isHermitian u v w).adjugate.eq,
    det_correlation_star]
  simp

theorem interiorReduced_isHermitian (u v w : ℂ) :
    (interiorReduced u v w).IsHermitian := by
  have hB := correlation_isHermitian u v w
  have hK := gapMatrix_isHermitian u v w
  have hc : star (c0 u v w : ℂ) = (c0 u v w : ℂ) := by simp
  rw [Matrix.IsHermitian]
  simp only [interiorReduced, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_smul]
  rw [hB.eq, hK.eq, hc]
  rw [Matrix.mul_assoc]

theorem mul_certificate_mul (u v w : ℂ) :
    correlation u v w * certificate u v w * correlation u v w =
      (correlation u v w).det • interiorReduced u v w := by
  simp only [certificate, interiorReduced, Matrix.mul_add, Matrix.add_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_adjugate, Matrix.one_mul]
  module

theorem det_correlation (u v w : ℂ) :
    (correlation u v w).det =
      1 - u * star u - v * star v - w * star w +
        u * w * star v + v * star u * star w := by
  simp [correlation, Matrix.det_fin_three]
  ring

theorem det_correlation_nonneg {u v w : ℂ} (hB : IsPSD (correlation u v w)) :
    0 ≤ (correlation u v w).det :=
  IsPSD.det_nonneg hB

theorem normSq_u_le_one {u v w : ℂ} (hB : IsPSD (correlation u v w)) :
    normSq u ≤ 1 := by
  have hq := hB.2 ![-u, 1, 0]
  have hr := (RCLike.nonneg_iff.mp hq).1
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ] at hr
  rw [Complex.normSq_apply]
  nlinarith

theorem normSq_v_le_one {u v w : ℂ} (hB : IsPSD (correlation u v w)) :
    normSq v ≤ 1 := by
  have hq := hB.2 ![-v, 0, 1]
  have hr := (RCLike.nonneg_iff.mp hq).1
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ] at hr
  rw [Complex.normSq_apply]
  nlinarith

theorem normSq_w_le_one {u v w : ℂ} (hB : IsPSD (correlation u v w)) :
    normSq w ≤ 1 := by
  have hq := hB.2 ![0, -w, 1]
  have hr := (RCLike.nonneg_iff.mp hq).1
  simp [correlation, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ] at hr
  rw [Complex.normSq_apply]
  nlinarith

theorem three_var_amgm_cubic {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 : ℝ) / 3) (w₂ := (1 : ℝ) / 3) (w₃ := (1 : ℝ) / 3)
    (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc] at h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg (mul_nonneg ha hb) hc) _) h 3
  rw [← Real.rpow_natCast] at hpow
  rw [← Real.rpow_mul (mul_nonneg (mul_nonneg ha hb) hc)] at hpow
  norm_num at hpow ⊢
  nlinarith

theorem c0_expansion (u v w : ℂ) : c0 u v w =
    normSq u + normSq v + normSq w + 3 * (u * w * star v).re -
      Real.sqrt 3 * (u * w * star v).im := by
  simp [c0, omega, Complex.mul_re, Complex.mul_im]
  ring

theorem det_correlation_real_nonneg {u v w : ℂ} (hB : IsPSD (correlation u v w)) :
    0 ≤ 1 - (normSq u + normSq v + normSq w) + 2 * (u * w * star v).re := by
  have hd := det_correlation_nonneg hB
  have hr := (RCLike.nonneg_iff.mp hd).1
  rw [det_correlation] at hr
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] at hr ⊢
  nlinarith

theorem c0_nonneg {u v w : ℂ} (hB : IsPSD (correlation u v w)) : 0 ≤ c0 u v w := by
  let a : ℝ := normSq u
  let b : ℝ := normSq v
  let c : ℝ := normSq w
  let S : ℝ := a + b + c
  let q : ℂ := u * w * star v
  let x : ℝ := q.re
  let y : ℝ := q.im
  let r : ℝ := Real.sqrt 3
  have ha : 0 ≤ a := Complex.normSq_nonneg u
  have hb : 0 ≤ b := Complex.normSq_nonneg v
  have hc : 0 ≤ c := Complex.normSq_nonneg w
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hau : a ≤ 1 := by simpa [a] using normSq_u_le_one hB
  have hbu : b ≤ 1 := by simpa [b] using normSq_v_le_one hB
  have hcu : c ≤ 1 := by simpa [c] using normSq_w_le_one hB
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = 3 := by dsimp [r]; exact Real.sq_sqrt (by norm_num)
  have hnorm : x ^ 2 + y ^ 2 = a * b * c := by
    calc
      x ^ 2 + y ^ 2 = normSq q := by simp [x, y, Complex.normSq_apply]; ring
      _ = a * b * c := by simp [q, a, b, c]; ring
  have hamgm : 27 * a * b * c ≤ S ^ 3 := by
    simpa [S, add_assoc] using three_var_amgm_cubic ha hb hc
  have hdet : 0 ≤ 1 - S + 2 * x := by
    simpa [S, x, q, a, b, c] using det_correlation_real_nonneg hB
  rw [show c0 u v w = S + 3 * x - r * y by
    simpa [S, x, y, q, r, a, b, c] using c0_expansion u v w]
  by_cases hsmall : S ≤ 9 / 4
  · have hcube : S ^ 3 ≤ (9 / 4) * S ^ 2 := by
      have hz : 0 ≤ S ^ 2 * (9 / 4 - S) :=
        mul_nonneg (sq_nonneg S) (sub_nonneg.mpr hsmall)
      nlinarith
    have hprod₁ : 12 * (a * b * c) ≤ (4 / 9) * S ^ 3 := by
      calc
        12 * (a * b * c) = (4 / 9 : ℝ) * (27 * a * b * c) := by ring
        _ ≤ (4 / 9 : ℝ) * S ^ 3 := mul_le_mul_of_nonneg_left hamgm (by norm_num)
    have hprod₂ : (4 / 9) * S ^ 3 ≤ S ^ 2 := by
      calc
        (4 / 9 : ℝ) * S ^ 3 ≤ (4 / 9 : ℝ) * ((9 / 4) * S ^ 2) :=
          mul_le_mul_of_nonneg_left hcube (by norm_num)
        _ = S ^ 2 := by ring
    have hprod : 12 * (a * b * c) ≤ S ^ 2 := hprod₁.trans hprod₂
    have hlin : (3 * x - r * y) ^ 2 ≤ 12 * (x ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (x + r * y)]
    rw [hnorm] at hlin
    have htSq : (3 * x - r * y) ^ 2 ≤ S ^ 2 := hlin.trans hprod
    have ht : -S ≤ 3 * x - r * y := by nlinarith
    linarith
  · have hlarge : 9 / 4 ≤ S := le_of_not_ge hsmall
    have hab : a * b ≤ 1 := by
      calc
        a * b ≤ 1 * b := mul_le_mul_of_nonneg_right hau hb
        _ ≤ 1 := by simpa using hbu
    have habc : a * b * c ≤ 1 := by
      calc
        a * b * c ≤ 1 * c := mul_le_mul_of_nonneg_right hab hc
        _ ≤ 1 := by simpa using hcu
    have hy_sq : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hy : y ≤ 1 := by nlinarith [sq_nonneg (y - 1)]
    have hr_le_two : r ≤ 2 := by nlinarith
    have hry : r * y ≤ r := by simpa using mul_le_mul_of_nonneg_left hy hr0
    have hx2 : S - 1 ≤ 2 * x := by linarith [hdet]
    have hx : (S - 1) / 2 ≤ x := by
      calc
        (S - 1) / 2 ≤ (2 * x) / 2 := div_le_div_of_nonneg_right hx2 (by norm_num)
        _ = x := by ring
    have hlower : (5 * S - 3) / 2 - r ≤ S + 3 * x - r * y := by linarith
    have hpos : 0 ≤ (5 * S - 3) / 2 - r := by linarith
    exact hpos.trans hlower

theorem certificate_diag_zero (u v w : ℂ) :
    (certificate u v w) 0 0 =
      (correlation u v w).det + (c0 u v w : ℂ) * (1 - normSq w) := by
  have hw : w * star w = (normSq w : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      ring
  simp [certificate, gapMatrix, correlation, Matrix.adjugate_fin_three, hw]
  exact Or.inl hw

theorem certificate_diag_one (u v w : ℂ) :
    (certificate u v w) 1 1 =
      (correlation u v w).det + (c0 u v w : ℂ) * (1 - normSq v) := by
  have hv : v * star v = (normSq v : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      ring
  simp [certificate, gapMatrix, correlation, Matrix.adjugate_fin_three, hv]
  exact Or.inl hv

theorem certificate_diag_two (u v w : ℂ) :
    (certificate u v w) 2 2 =
      (correlation u v w).det + (c0 u v w : ℂ) * (1 - normSq u) := by
  have hu : u * star u = (normSq u : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      ring
  simp [certificate, gapMatrix, correlation, Matrix.adjugate_fin_three, hu]
  exact Or.inl hu

theorem certificate_diagonal_nonneg {u v w : ℂ}
    (hB : IsPSD (correlation u v w)) (i : Fin 3) :
    0 ≤ ((certificate u v w) i i).re := by
  have hd := (RCLike.nonneg_iff.mp (det_correlation_nonneg hB)).1
  have hc := c0_nonneg hB
  fin_cases i
  · change 0 ≤ ((certificate u v w) (0 : Fin 3) 0).re
    rw [certificate_diag_zero]
    simp only [map_add, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact add_nonneg hd (mul_nonneg hc (sub_nonneg.mpr (normSq_w_le_one hB)))
  · change 0 ≤ ((certificate u v w) (1 : Fin 3) 1).re
    rw [certificate_diag_one]
    simp only [map_add, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact add_nonneg hd (mul_nonneg hc (sub_nonneg.mpr (normSq_v_le_one hB)))
  · change 0 ≤ ((certificate u v w) (2 : Fin 3) 2).re
    rw [certificate_diag_two]
    simp only [map_add, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact add_nonneg hd (mul_nonneg hc (sub_nonneg.mpr (normSq_u_le_one hB)))

theorem interior_reduction {u v w : ℂ}
    (hdet : 0 < (correlation u v w).det) :
    IsPSD (certificate u v w) ↔ IsPSD (interiorReduced u v w) := by
  let B := correlation u v w
  let T := certificate u v w
  let R := interiorReduced u v w
  let d : ℝ := B.det.re
  have hB : B.IsHermitian := correlation_isHermitian u v w
  have hd : 0 < d := (RCLike.pos_iff.mp hdet).1
  have hdcast : (d : ℂ) = B.det := by
    apply Complex.ext
    · rfl
    · simpa [d] using (RCLike.pos_iff.mp hdet).2.symm
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdet)
  constructor
  · intro hT
    have hc := hT.conjTranspose_mul_mul_same B
    rw [hB.eq] at hc
    have hscaled : IsPSD (B.det • R) := by
      dsimp [B, T] at hc
      rw [mul_certificate_mul] at hc
      simpa [B, R] using hc
    rw [← hdcast] at hscaled
    have hunscale := IsPSD.nonneg_smul hscaled (show 0 ≤ d⁻¹ by positivity)
    have hinv : ((d⁻¹ : ℝ) : ℂ) * (d : ℂ) = 1 := by
      exact_mod_cast inv_mul_cancel₀ (ne_of_gt hd)
    change IsPSD R
    simpa only [smul_smul, hinv, one_smul] using hunscale
  · intro hR
    have hscaled : IsPSD (B.det • R) := by
      rw [← hdcast]
      exact IsPSD.nonneg_smul hR hd.le
    have hmiddle : IsPSD (B * T * B) := by
      dsimp [B, T, R]
      rw [mul_certificate_mul]
      simpa [B, R] using hscaled
    have hc := hmiddle.conjTranspose_mul_mul_same B⁻¹
    have hBinv : B⁻¹.IsHermitian := hB.inv
    rw [hBinv.eq] at hc
    have heq : B⁻¹ * (B * T * B) * B⁻¹ = T := by
      calc
        B⁻¹ * (B * T * B) * B⁻¹ = (B⁻¹ * B) * T * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
        _ = T := by
          rw [Matrix.nonsing_inv_mul B hu, Matrix.mul_nonsing_inv B hu]
          simp
    rw [heq] at hc
    exact hc

theorem certificate_posSemidef_of_det_eq_zero {u v w : ℂ}
    (hB : IsPSD (correlation u v w)) (hdet : (correlation u v w).det = 0) :
    IsPSD (certificate u v w) := by
  rw [certificate, hdet, zero_smul, zero_add]
  exact IsPSD.nonneg_smul (IsPSD.adjugate hB) (c0_nonneg hB)

theorem certificate_posSemidef_of_interiorReduced {u v w : ℂ}
    (hB : IsPSD (correlation u v w))
    (hR : IsPSD (interiorReduced u v w)) :
    IsPSD (certificate u v w) := by
  by_cases hz : (correlation u v w).det = 0
  · exact certificate_posSemidef_of_det_eq_zero hB hz
  · have hd0 := det_correlation_nonneg hB
    have hd : 0 < (correlation u v w).det := lt_of_le_of_ne hd0 (Ne.symm hz)
    exact (interior_reduction hd).2 hR

end PermanentalDominance.N4.A4Certificate

