import PermanentalDominance.N4.A4GeometricNormalization

/-!
# Rank-one part of the geometric `A₄` proof

In the old four-vector proof the three residual Gram vectors are first treated
when they are collinear, say `wᵢ = zᵢ f`.  The remaining scalar is a sum of a
Fourier square and three times `R₀`.  This file gives the exact complex
quadratic completion proving `R₀ ≥ 0`; it is independent of the spectral
coefficient certificate.
-/

noncomputable section

open Complex

namespace PermanentalDominance.N4.A4GeometricRankOne

open A4Certificate A4GeometricNormalization

/-- The scalar `R₀` in the collinear part of the old proof. -/
def rankOneR0 (x y z : ℂ) : ℝ :=
  4 + normSq (x + y + z) + normSq (x * y + x * z + y * z) -
    (normSq (x * y) + normSq (x * z) + normSq (y * z)) +
    normSq (x * y * z)

/-- A general complex quadratic is nonnegative when its scalar discriminant
is nonpositive.  This is the exact completion-of-the-square step used by the
rank-one proof. -/
theorem complex_quadratic_nonneg
    {K C : ℝ} {L z : ℂ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hdisc : normSq L ≤ C * K) :
    0 ≤ K * normSq z + 2 * (L * z).re + C := by
  by_cases hK0 : K = 0
  · have hL0 : normSq L = 0 := by
      have : normSq L ≤ 0 := by simpa [hK0] using hdisc
      exact le_antisymm this (normSq_nonneg L)
    have hL : L = 0 := normSq_eq_zero.mp hL0
    simp [hK0, hL, hC]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have hid :
        K * normSq z + 2 * (L * z).re + C =
          K * normSq (z + star L / (K : ℂ)) +
            (C * K - normSq L) / K := by
      norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
        Complex.star_def]
      field_simp [hK0]
      ring
    rw [hid]
    exact add_nonneg
      (mul_nonneg hK (normSq_nonneg _))
      (div_nonneg (sub_nonneg.mpr hdisc) hK)

private def s0 (x y : ℂ) : ℂ := x + y
private def p0 (x y : ℂ) : ℂ := x * y
private def K0 (x y : ℂ) : ℝ := normSq (1 + star x * y)
private def L0 (x y : ℂ) : ℂ := star (s0 x y) + star (p0 x y) * s0 x y
private def C0 (x y : ℂ) : ℝ := 4 + normSq (s0 x y)

/-- Collecting `R₀` as a quadratic in its third complex variable. -/
theorem rankOneR0_quadratic (x y z : ℂ) :
    rankOneR0 x y z =
      K0 x y * normSq z + 2 * (L0 x y * z).re + C0 x y := by
  norm_num [rankOneR0, K0, L0, C0, s0, p0,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.star_def]
  ring

/-- The exact discriminant identity retained in the old proof. -/
theorem rankOne_discriminant (x y : ℂ) :
    C0 x y * K0 x y - normSq (L0 x y) =
      4 * (1 + (star x * y).re) ^ 2 := by
  norm_num [K0, L0, C0, s0, p0, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def]
  ring

/-- Nonnegativity of the old collinear residual. -/
theorem rankOneR0_nonneg (x y z : ℂ) : 0 ≤ rankOneR0 x y z := by
  rw [rankOneR0_quadratic]
  apply complex_quadratic_nonneg
  · exact normSq_nonneg _
  · dsimp [C0]
    nlinarith [normSq_nonneg (s0 x y)]
  · rw [← sub_nonneg, rankOne_discriminant]
    positivity

/-- The final sum-of-squares shape of the rank-one branch.  The Fourier term
`q₁` is kept abstract here; its precise root-of-unity expression is supplied
by the later Gram normalization layer. -/
theorem rankOne_fourier_sos_nonneg (x y z q₁ : ℂ) :
    0 ≤ 3 * rankOneR0 x y z + normSq q₁ :=
  add_nonneg (mul_nonneg (by norm_num) (rankOneR0_nonneg x y z))
    (normSq_nonneg q₁)

/-- The complementary Fourier mode in the collinear Gram calculation. -/
def rankOneFourier (x y z : ℂ) : ℂ :=
  x * y + omega * x * z + omega ^ 2 * y * z

set_option maxHeartbeats 2000000 in
/-- Exact identification of the collinear constant term in the geometric
normalization with the rank-one sum of squares.  This is the missing algebraic
link between `A4GeometricNormalization` and the independent rank-one proof. -/
theorem geometricP_collinear_identity (x y z : ℂ) :
    geometricP
        (normSq x) (normSq y) (normSq z)
        (star x * y) (star x * z) (star y * z) =
      2 * (3 * rankOneR0 x y z + normSq (rankOneFourier x y z)) := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsqrt]
  have hsqrt4 : (Real.sqrt 3) ^ 4 = 9 := by
    calc
      (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hsqrt]; norm_num
  have how2 : omega ^ 2 =
      ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith
  simp only [geometricP, symmetricTensorFourierNormSq]
  rw [how2]
  norm_num [rankOneR0, rankOneFourier,
    symmetricTensorSumNormSq, pairTensorDiag,
    tensorInner1213, tensorInner1223, tensorInner1323,
    geometricGamma, geometricTau,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.star_def, omega,
    pow_two, Complex.I_mul_I]
  ring_nf
  rw [hsqrt, hsqrt3, hsqrt4]
  ring

/-- The geometric polynomial is nonnegative on every collinear residual Gram
triple, now as a direct consequence of the verified rank-one SOS. -/
theorem geometricP_collinear_nonneg (x y z : ℂ) :
    0 ≤ geometricP
      (normSq x) (normSq y) (normSq z)
      (star x * y) (star x * z) (star y * z) := by
  rw [geometricP_collinear_identity]
  exact mul_nonneg (by norm_num)
    (rankOne_fourier_sos_nonneg x y z (rankOneFourier x y z))

end PermanentalDominance.N4.A4GeometricRankOne
