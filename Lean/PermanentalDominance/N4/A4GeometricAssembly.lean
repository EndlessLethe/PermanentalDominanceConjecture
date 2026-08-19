import PermanentalDominance.N4.A4GeometricGram

/-!
# Assembly lemmas for the old geometric A₄ proof

The manuscript expands the determinant of its two-dimensional Hessian and the
numerator of the quadratic minimum in powers of the Gram defect
delta = ab - |g|².  The hard coefficient inequalities are proved in
A4GeometricGeneral and A4GeometricGram.  This file packages their final use;
the exact expansion identities are supplied by A4GeometricHessian and the
downstream modules connect the collinear and general cases.
-/

noncomputable section

namespace PermanentalDominance.N4.A4GeometricAssembly

open A4GeometricGeneral A4GeometricGram

/-- The positive quadratic coefficient D₂ in the determinant expansion. -/
def determinantDeltaSqCoeff (a : ℝ) : ℝ :=
  a * (a + 1) * (a + 2)

theorem determinantDeltaSqCoeff_pos {a : ℝ} (ha : 0 < a) :
    0 < determinantDeltaSqCoeff a := by
  dsimp [determinantDeltaSqCoeff]
  positivity

/-- Abstract form of the old determinant expansion. -/
def determinantExpansion
    (a r s delta determinantAtZero : ℝ) : ℝ :=
  determinantAtZero +
    delta * determinantDeltaCoeff a r s +
    delta ^ 2 * determinantDeltaSqCoeff a

/-- Once the exact determinant expansion has been checked, positivity follows
only from the collinear constant term and the two restored coefficient
certificates. -/
theorem determinantExpansion_pos
    {a r s delta determinantAtZero : ℝ}
    (ha : 0 < a) (hdelta : 0 ≤ delta)
    (hzero : 0 < determinantAtZero) :
    0 < determinantExpansion a r s delta determinantAtZero := by
  have h1 := determinantDeltaCoeff_pos (r := r) (s := s) ha
  have h2 := determinantDeltaSqCoeff_pos ha
  dsimp [determinantExpansion]
  positivity

/-- The positive cubic coefficient N₃ in the minimum-numerator expansion. -/
def minimumDeltaCubeCoeff (a : ℝ) : ℝ :=
  (a + 2) * (a ^ 2 + 6)

theorem minimumDeltaCubeCoeff_pos {a : ℝ} (ha : 0 < a) :
    0 < minimumDeltaCubeCoeff a := by
  dsimp [minimumDeltaCubeCoeff]
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  positivity

/-- Abstract form of the old minimum-numerator expansion.  The rational
coordinates for N₁ are X = r and Y = sqrt 3 * s. -/
def minimumNumeratorExpansion
    (a r s delta numeratorAtZero : ℝ) : ℝ :=
  numeratorAtZero +
    delta * minimumLinearCoeff a r (Real.sqrt 3 * s) +
    delta ^ 2 * minimumDeltaSqCoeff a r s +
    delta ^ 3 * minimumDeltaCubeCoeff a

/-- Final nonnegativity assembly for the old minimum numerator. -/
theorem minimumNumeratorExpansion_nonneg
    {a r s delta numeratorAtZero : ℝ}
    (ha : 0 < a) (hdelta : 0 ≤ delta)
    (hzero : 0 ≤ numeratorAtZero) :
    0 ≤ minimumNumeratorExpansion a r s delta numeratorAtZero := by
  have h1 := minimumLinearCoeff_pos ha r (Real.sqrt 3 * s)
  have h2 := minimumDeltaSqCoeff_pos (r := r) (s := s) ha
  have h3 := minimumDeltaCubeCoeff_pos ha
  dsimp [minimumNumeratorExpansion]
  positivity

/-- In the genuinely non-collinear case the old numerator is strictly
positive, independently of whether the collinear constant term vanishes. -/
theorem minimumNumeratorExpansion_pos_of_delta
    {a r s delta numeratorAtZero : ℝ}
    (ha : 0 < a) (hdelta : 0 < delta)
    (hzero : 0 ≤ numeratorAtZero) :
    0 < minimumNumeratorExpansion a r s delta numeratorAtZero := by
  have h1 := minimumLinearCoeff_pos ha r (Real.sqrt 3 * s)
  have h2 := minimumDeltaSqCoeff_pos (r := r) (s := s) ha
  have h3 := minimumDeltaCubeCoeff_pos ha
  dsimp [minimumNumeratorExpansion]
  have hdelta1 :
      0 < delta * minimumLinearCoeff a r (Real.sqrt 3 * s) :=
    mul_pos hdelta h1
  have hdelta2 :
      0 ≤ delta ^ 2 * minimumDeltaSqCoeff a r s :=
    mul_nonneg (sq_nonneg delta) h2.le
  have hdelta3 :
      0 ≤ delta ^ 3 * minimumDeltaCubeCoeff a :=
    mul_nonneg (pow_nonneg hdelta.le _) h3.le
  linarith

end PermanentalDominance.N4.A4GeometricAssembly
