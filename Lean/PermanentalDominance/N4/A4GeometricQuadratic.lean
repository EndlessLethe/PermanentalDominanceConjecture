import PermanentalDominance.N4.A4GeometricNoncollinear

/-!
# General quadratic form for the geometric `A₄` polynomial

This module identifies the dependence of `geometricP` on the third Gram
vector.  The two inner products form a vector `h`; the quadratic is

`P₀ + 2 Re(l* h) + λ n₃ + Re(h* M h)`.

For positive Gram defect, writing `h = G z` turns its Hessian into `G T`,
where `T = λ I + M G` is the matrix whose determinant and minimum numerator
were certified in the preceding modules.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4GeometricQuadratic

open A4Certificate A4GeometricHessian A4GeometricNormalization
open A4GeometricGeneral A4GeometricCollinear A4GeometricNoncollinear

/-- The two inner products of the third Gram vector with the fixed pair. -/
def thirdInner (p q : ℂ) : Fin 2 → ℂ := ![p, q]

/-- Canonical coordinates for a `2 × 2` Hermitian matrix. -/
def hermitianTwo (α d : ℝ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![
  (α : ℂ), u;
  star u, (d : ℂ)]

theorem hermitianTwo_isHermitian (α d : ℝ) (u : ℂ) :
    (hermitianTwo α d u).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermitianTwo]

theorem hermitianTwo_det_re (α d : ℝ) (u : ℂ) :
    (hermitianTwo α d u).det.re = α * d - normSq u := by
  simp [hermitianTwo, Matrix.det_fin_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.star_def]

theorem isHermitian_eq_hermitianTwo
    {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : Q.IsHermitian) :
    Q = hermitianTwo (Q 0 0).re (Q 1 1).re (Q 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact (hQ.coe_re_apply_self 0).symm
  · rfl
  · simpa [hermitianTwo] using (hQ.apply 1 0).symm
  · exact (hQ.coe_re_apply_self 1).symm

theorem hermitianTwo_quadratic_re
    (α d : ℝ) (u : ℂ) (x : Fin 2 → ℂ) (hα : 0 < α) :
    (dotProduct (star x) (hermitianTwo α d u *ᵥ x)).re =
      α * normSq (x 0 + u / (α : ℂ) * x 1) +
        (α * d - normSq u) / α * normSq (x 1) := by
  simp [hermitianTwo, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
    Complex.star_def]
  field_simp [hα.ne']
  ring

theorem hermitianTwo_quadratic_im
    (α d : ℝ) (u : ℂ) (x : Fin 2 → ℂ) :
    (dotProduct (star x) (hermitianTwo α d u *ᵥ x)).im = 0 := by
  simp [hermitianTwo, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def]
  ring

/-- The `2 × 2` Hermitian form is positive definite when its first leading
minor and determinant are positive. -/
theorem hermitianTwo_posDef
    {α d : ℝ} {u : ℂ} (hα : 0 < α)
    (hdet : 0 < α * d - normSq u) :
    (hermitianTwo α d u).PosDef := by
  refine ⟨hermitianTwo_isHermitian α d u, ?_⟩
  intro x hx
  apply (RCLike.pos_iff).2
  constructor
  · change 0 < (dotProduct (star x) (hermitianTwo α d u *ᵥ x)).re
    rw [hermitianTwo_quadratic_re α d u x hα]
    by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        funext i
        fin_cases i <;> assumption
      simpa [hx1] using
        mul_pos hα (Complex.normSq_pos.mpr hx0)
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg hα.le (normSq_nonneg _))
        (mul_pos (div_pos hdet hα) (Complex.normSq_pos.mpr hx1))
  · exact hermitianTwo_quadratic_im α d u x

theorem posDef_of_isHermitian_entry_det
    {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : Q.IsHermitian)
    (h00 : 0 < (Q 0 0).re) (hdet : 0 < Q.det.re) :
    Q.PosDef := by
  have hQeq := isHermitian_eq_hermitianTwo hQ
  rw [hQeq] at hdet ⊢
  apply hermitianTwo_posDef h00
  simpa only [hermitianTwo_det_re] using hdet

set_option maxHeartbeats 3000000 in
/-- Exact quadratic decomposition of `geometricP` in its third Gram data. -/
theorem geometricP_quadratic
    (a b c r s : ℝ) (p q : ℂ) :
    geometricP a b c (g r s) p q =
      P0 a b r s +
        2 * (dotProduct (star (l a b r s)) (thirdInner p q)).re +
        geometricLambda a b r s * c +
        (dotProduct (star (thirdInner p q))
          (M a b r s *ᵥ thirdInner p q)).re := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have how2 : omega ^ 2 =
      ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith
  simp only [geometricP, symmetricTensorFourierNormSq]
  rw [how2]
  norm_num [symmetricTensorSumNormSq,
    symmetricTensorFourierNormSq, pairTensorDiag,
    tensorInner1213, tensorInner1223, tensorInner1323,
    geometricGamma, geometricTau,
    P0, l, g, M, thirdInner, geometricLambda,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    omega, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def,
    pow_two, Complex.I_mul_I]
  simp only [map_inv₀, map_ofNat]
  norm_num [Complex.inv_re, Complex.inv_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  rw [hsqrt]
  ring

/-- The Hermitian coordinate Hessian after writing the third Gram vector as
`thirdInner = G z`. -/
def coordinateHessian (a b r s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  G a b r s * T a b r s

theorem G_isHermitian (a b r s : ℝ) :
    (G a b r s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [G]

theorem M_isHermitian (a b r s : ℝ) :
    (M a b r s).IsHermitian := by
  have how4 : (omega ^ 2) ^ 2 = omega := by
    calc
      (omega ^ 2) ^ 2 = (star omega) ^ 2 := by rw [star_omega]
      _ = star (omega ^ 2) :=
        (map_pow (starRingEnd ℂ) omega 2).symm
      _ = star (star omega) := (congrArg star star_omega).symm
      _ = omega := star_star omega
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [M, star_omega, map_pow, how4]

theorem coordinateHessian_isHermitian (a b r s : ℝ) :
    (coordinateHessian a b r s).IsHermitian := by
  have hG := G_isHermitian a b r s
  have hM := M_isHermitian a b r s
  have hscalar :
      (((geometricLambda a b r s : ℂ) • G a b r s)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [G]
  have hmiddle :
      (G a b r s * M a b r s * G a b r s).IsHermitian := by
    simpa [hG.eq] using
      (isHermitian_conjTranspose_mul_mul (G a b r s) hM)
  rw [show coordinateHessian a b r s =
      ((geometricLambda a b r s : ℂ) • G a b r s) +
        G a b r s * M a b r s * G a b r s by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateHessian, T, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring]
  exact hscalar.add hmiddle

theorem G_det (a b r s : ℝ) :
    (G a b r s).det = (gramDefect a b r s : ℂ) := by
  apply Complex.ext <;>
    norm_num [G, g, gramDefect, Matrix.det_fin_two,
      Complex.mul_re, Complex.mul_im, Complex.star_def, pow_two] <;>
    ring

theorem coordinateHessian_det_re (a b r s : ℝ) :
    (coordinateHessian a b r s).det.re =
      gramDefect a b r s * (T a b r s).det.re := by
  rw [coordinateHessian, Matrix.det_mul, G_det]
  simp

set_option maxHeartbeats 2000000 in
/-- The first leading minor is the positive collinear value plus a positive
multiple of the Gram defect. -/
theorem coordinateHessian_zero_zero
    (a b r s : ℝ) (ha : a ≠ 0) :
    (coordinateHessian a b r s 0 0).re =
      a * collinearH a r s + gramDefect a b r s * (a + 1) := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num [coordinateHessian, T, M, G, g, collinearH, collinearB,
    gramDefect, geometricLambda, Matrix.mul_apply, Fin.sum_univ_two,
    omega, pow_two, Complex.I_mul_I,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def]
  field_simp [ha]
  ring_nf

theorem coordinateHessian_zero_zero_pos
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ gramDefect a b r s) :
    0 < (coordinateHessian a b r s 0 0).re := by
  rw [coordinateHessian_zero_zero a b r s ha.ne']
  exact add_pos_of_pos_of_nonneg
    (mul_pos ha (collinearH_pos ha))
    (mul_nonneg hδ (by linarith))

theorem coordinateHessian_det_pos
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 < gramDefect a b r s) :
    0 < (coordinateHessian a b r s).det.re := by
  rw [coordinateHessian_det_re]
  exact mul_pos hδ (hessianDeterminant_pos ha hδ.le)

/-- In the genuinely non-collinear case, the coordinate Hessian is positive
definite. -/
theorem coordinateHessian_posDef
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 < gramDefect a b r s) :
    (coordinateHessian a b r s).PosDef :=
  posDef_of_isHermitian_entry_det
    (coordinateHessian_isHermitian a b r s)
    (coordinateHessian_zero_zero_pos ha hδ.le)
    (coordinateHessian_det_pos ha hδ)

end PermanentalDominance.N4.A4GeometricQuadratic
