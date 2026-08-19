import PermanentalDominance.N4.A4Geometric

/-!
# Exact normalization identity for the geometric `A₄` proof

The old proof realizes a `4 × 4` correlation matrix as the Gram matrix of
unit vectors `ξ₁, ξ₂, ξ₃, e`.  After diagonal-unitary normalization the last
column is real and positive, say `qᵢ = aᵢ`, and

`ξᵢ = aᵢ (e + wᵢ)`,  with  `aᵢ² (1 + ‖wᵢ‖²) = 1`.

Writing `nᵢ = ‖wᵢ‖²` and `hᵢⱼ = ⟪wᵢ,wⱼ⟫`, the principal correlations are

`u = a₁a₂(1+h₁₂)`, `v = a₁a₃(1+h₁₃)`,
`w = a₂a₃(1+h₂₃)`.

This module checks the exact algebraic identity

`fourVectorGap u v w q = (a₁a₂a₃)² geometricP(n,h)`.

The tensor expressions are represented by their Gram expansions, keeping this
layer independent of a particular tensor-product implementation.  The choice
of `omega` in `A4Certificate` has negative imaginary part.  Accordingly we
use the conjugated triple product
`tau = h₁₃ * star h₁₂ * star h₂₃`; this preserves the manuscript's
`+ sqrt 3 * Im tau` convention.
-/

noncomputable section

open Complex Matrix

namespace PermanentalDominance.N4.A4GeometricNormalization

open A4Certificate A4Geometric

/-- Sum of the three diagonal squared norms of the normalized symmetric
tensor pairs `X₁₂`, `X₁₃`, `X₂₃`. -/
def pairTensorDiag (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℝ :=
  n₁ * n₂ + normSq h₁₂ + n₁ * n₃ + normSq h₁₃ +
    n₂ * n₃ + normSq h₂₃

/-- `⟪X₁₂,X₁₃⟫` in scalar Gram coordinates. -/
def tensorInner1213 (n₁ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℂ :=
  (n₁ : ℂ) * h₂₃ + h₁₃ * star h₁₂

/-- `⟪X₁₂,X₂₃⟫` in scalar Gram coordinates. -/
def tensorInner1223 (n₂ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℂ :=
  h₁₂ * h₂₃ + (n₂ : ℂ) * h₁₃

/-- `⟪X₁₃,X₂₃⟫` in scalar Gram coordinates. -/
def tensorInner1323 (n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℂ :=
  (n₃ : ℂ) * h₁₂ + h₁₃ * star h₂₃

/-- Squared norm of `X₁₂ + X₁₃ + X₂₃`, expanded through its Gram matrix. -/
def symmetricTensorSumNormSq
    (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℝ :=
  pairTensorDiag n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ +
    2 * (tensorInner1213 n₁ h₁₂ h₁₃ h₂₃ +
      tensorInner1223 n₂ h₁₂ h₁₃ h₂₃ +
      tensorInner1323 n₃ h₁₂ h₁₃ h₂₃).re

/-- Squared norm of `X₁₂ + omega² X₁₃ + omega X₂₃`, expanded through
its Gram matrix. -/
def symmetricTensorFourierNormSq
    (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℝ :=
  pairTensorDiag n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ +
    2 * ((omega ^ 2) * tensorInner1213 n₁ h₁₂ h₁₃ h₂₃ +
      omega * tensorInner1223 n₂ h₁₂ h₁₃ h₂₃ +
      (omega ^ 2) * tensorInner1323 n₃ h₁₂ h₁₃ h₂₃).re

/-- Conjugated triple product matching the negative-imaginary-root convention. -/
def geometricTau (h₁₂ h₁₃ h₂₃ : ℂ) : ℂ :=
  h₁₃ * star h₁₂ * star h₂₃

/-- The cubic Gram correction `Gamma` from the old proof. -/
def geometricGamma
    (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℝ :=
  n₃ * normSq h₁₂ + n₂ * normSq h₁₃ + n₁ * normSq h₂₃ +
    3 * (geometricTau h₁₂ h₁₃ h₂₃).re +
      Real.sqrt 3 * (geometricTau h₁₂ h₁₃ h₂₃).im

/-- The normalized geometric polynomial `P(w₁,w₂,w₃)`, written entirely
in scalar Gram coordinates. -/
def geometricP
    (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : ℝ :=
  24 + 6 * (n₁ + n₂ + n₃ + 2 * (h₁₂ + h₁₃ + h₂₃).re) +
    2 * symmetricTensorSumNormSq n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ -
      symmetricTensorFourierNormSq n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ +
        geometricGamma n₁ n₂ n₃ h₁₂ h₁₃ h₂₃

set_option maxHeartbeats 2000000 in
/-- Exact bridge from the matrix gap to the normalized geometric polynomial.
No positivity hypothesis is needed: this is a polynomial identity modulo the
three unit-vector normalization equations. -/
theorem fourVectorGap_normalization
    (a₁ a₂ a₃ n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ)
    (ha₁ : a₁ ^ 2 * (1 + n₁) = 1)
    (ha₂ : a₂ ^ 2 * (1 + n₂) = 1)
    (ha₃ : a₃ ^ 2 * (1 + n₃) = 1) :
    fourVectorGap
        ((a₁ * a₂ : ℝ) * (1 + h₁₂))
        ((a₁ * a₃ : ℝ) * (1 + h₁₃))
        ((a₂ * a₃ : ℝ) * (1 + h₂₃))
        ![(a₁ : ℂ), (a₂ : ℂ), (a₃ : ℂ)] =
      (a₁ * a₂ * a₃) ^ 2 *
        geometricP n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have how2 : omega ^ 2 =
      ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith
  simp only [geometricP, symmetricTensorFourierNormSq]
  rw [how2]
  norm_num [fourVectorGap, c0, gapMatrix,
    symmetricTensorSumNormSq, pairTensorDiag,
    tensorInner1213, tensorInner1223, tensorInner1323,
    geometricGamma, geometricTau,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.star_def, omega,
    pow_two, Complex.I_mul_I]
  ring_nf at ha₁ ha₂ ha₃ ⊢
  rw [hsqrt] at ⊢
  linear_combination
    (-a₂ ^ 2 * a₃ ^ 2 *
      (Real.sqrt 3 * h₂₃.im + n₂ + n₃ + h₂₃.re ^ 2 +
        5 * h₂₃.re + h₂₃.im ^ 2 + 6)) * ha₁ +
    (-a₃ ^ 2 *
      (-a₁ ^ 2 * Real.sqrt 3 * h₁₃.im + a₁ ^ 2 * n₃ +
        a₁ ^ 2 * h₁₃.re ^ 2 + 5 * a₁ ^ 2 * h₁₃.re +
        a₁ ^ 2 * h₁₃.im ^ 2 + 5 * a₁ ^ 2 + 1)) * ha₂ +
    (-a₁ ^ 2 * a₂ ^ 2 * Real.sqrt 3 * h₁₂.im -
      a₁ ^ 2 * a₂ ^ 2 * h₁₂.re ^ 2 -
      5 * a₁ ^ 2 * a₂ ^ 2 * h₁₂.re -
      a₁ ^ 2 * a₂ ^ 2 * h₁₂.im ^ 2 -
      4 * a₁ ^ 2 * a₂ ^ 2 - a₁ ^ 2 - a₂ ^ 2) * ha₃

end PermanentalDominance.N4.A4GeometricNormalization
