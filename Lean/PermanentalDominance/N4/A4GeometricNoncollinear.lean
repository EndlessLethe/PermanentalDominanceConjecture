import PermanentalDominance.N4.A4GeometricCollinear

/-!
# Non-collinear scalar assembly for the geometric `A₄` proof

This module combines the exact determinant and minimum-numerator expansions
with the collinear boundary estimates.  It packages the sign conclusions for
an arbitrary nonnegative Gram defect

`δ = a b - (r² + s²)`.
-/

noncomputable section

open Complex Matrix

namespace PermanentalDominance.N4.A4GeometricNoncollinear

open A4GeometricAssembly A4GeometricCollinear A4GeometricHessian

/-- The determinant defect of the `2 × 2` real Gram data. -/
def gramDefect (a b r s : ℝ) : ℝ :=
  a * b - (r ^ 2 + s ^ 2)

theorem b_eq_gramDefect_coordinate
    (a b r s : ℝ) (ha : a ≠ 0) :
    b = (r ^ 2 + s ^ 2 + gramDefect a b r s) / a := by
  dsimp [gramDefect]
  field_simp [ha]

/-- Positivity of the scaled Hessian determinant for every nonnegative Gram
defect. -/
theorem hessianDeterminant_scaled_pos
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ gramDefect a b r s) :
    0 < a ^ 3 * (T a b r s).det.re := by
  let δ := gramDefect a b r s
  have hexp := hessianDeterminant_expansion a r s δ ha.ne'
  rw [← b_eq_gramDefect_coordinate a b r s ha.ne'] at hexp
  rw [hexp]
  exact determinantExpansion_pos ha hδ (D0_pos ha)

/-- Strict positivity of the Hessian determinant itself. -/
theorem hessianDeterminant_pos
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ gramDefect a b r s) :
    0 < (T a b r s).det.re := by
  have hscaled := hessianDeterminant_scaled_pos ha hδ
  have ha3 : 0 < a ^ 3 := pow_pos ha _
  nlinarith

/-- Nonnegativity of the scaled Schur-complement numerator for every
nonnegative Gram defect. -/
theorem minimumNumerator_scaled_nonneg
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ gramDefect a b r s) :
    0 ≤ a ^ 3 * N a b r s := by
  let δ := gramDefect a b r s
  have hexp := minimumNumerator_expansion a r s δ ha.ne'
  rw [← b_eq_gramDefect_coordinate a b r s ha.ne'] at hexp
  rw [hexp]
  exact minimumNumeratorExpansion_nonneg ha hδ (N0_nonneg ha)

/-- Nonnegativity of the Schur-complement numerator. -/
theorem minimumNumerator_nonneg
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ gramDefect a b r s) :
    0 ≤ N a b r s := by
  have hscaled := minimumNumerator_scaled_nonneg ha hδ
  have ha3 : 0 < a ^ 3 := pow_pos ha _
  nlinarith

/-- In the genuinely non-collinear case, the Schur-complement numerator is
strictly positive. -/
theorem minimumNumerator_pos
    {a b r s : ℝ} (ha : 0 < a)
    (hδ : 0 < gramDefect a b r s) :
    0 < N a b r s := by
  let δ := gramDefect a b r s
  have hexp := minimumNumerator_expansion a r s δ ha.ne'
  rw [← b_eq_gramDefect_coordinate a b r s ha.ne'] at hexp
  have hscaled : 0 < a ^ 3 * N a b r s := by
    rw [hexp]
    exact minimumNumeratorExpansion_pos_of_delta ha hδ (N0_nonneg ha)
  have ha3 : 0 < a ^ 3 := pow_pos ha _
  nlinarith

end PermanentalDominance.N4.A4GeometricNoncollinear
