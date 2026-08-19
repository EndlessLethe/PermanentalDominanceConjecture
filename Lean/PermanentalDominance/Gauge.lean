import PermanentalDominance.PSD

/-!
# Finite-dimensional complex gauge normalization

This file packages the dimension-independent phase and nonzero-coordinate
perturbations used when normalizing Gram completions.
-/

noncomputable section

open Complex Matrix

namespace PermanentalDominance.Gauge

theorem unit_mul (d : ℂ) (hd : normSq d = 1) : star d * d = 1 := by
  apply Complex.ext
  · simpa [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.star_def] using hd
  · simp [Complex.mul_im, Complex.star_def]
    ring

def polarRadius (z : ℂ) : ℝ := Real.sqrt (normSq z)

def polarPhase (z : ℂ) : ℂ :=
  star z / (polarRadius z : ℂ)

theorem polarRadius_pos {z : ℂ} (hz : z ≠ 0) :
    0 < polarRadius z := by
  apply Real.sqrt_pos.2
  exact lt_of_le_of_ne (normSq_nonneg z)
    (Ne.symm (mt normSq_eq_zero.mp hz))

theorem polarRadius_sq (z : ℂ) :
    polarRadius z ^ 2 = normSq z :=
  Real.sq_sqrt (normSq_nonneg z)

theorem polarPhase_mul_radius {z : ℂ} (hz : z ≠ 0) :
    polarPhase z * (polarRadius z : ℂ) = star z := by
  exact div_mul_cancel₀ _ (by exact_mod_cast (polarRadius_pos hz).ne')

theorem star_polarPhase_mul_radius {z : ℂ} (hz : z ≠ 0) :
    star (polarPhase z) * (polarRadius z : ℂ) = z := by
  have h := congrArg star (polarPhase_mul_radius hz)
  simpa [map_mul, mul_comm] using h

theorem polarPhase_normSq {z : ℂ} (hz : z ≠ 0) :
    normSq (polarPhase z) = 1 := by
  have hn : normSq z ≠ 0 := mt normSq_eq_zero.mp hz
  rw [show normSq (polarPhase z) =
      normSq z / (polarRadius z * polarRadius z) by
    simp [polarPhase, Complex.normSq_div, Complex.normSq_conj,
      Complex.star_def, Complex.normSq_ofReal]]
  rw [show polarRadius z * polarRadius z = normSq z by
    simpa [pow_two] using polarRadius_sq z]
  exact div_self hn

/-- Diagonal phase matrix on an arbitrary finite coordinate set. -/
def phaseDiagonal {n : Type*} [DecidableEq n] (d : n → ℂ) :
    Matrix n n ℂ :=
  Matrix.diagonal d

/-- Coordinatewise action of the adjoint diagonal phase. -/
def phaseVector {n : Type*} (d q : n → ℂ) : n → ℂ :=
  fun i => star (d i) * q i

theorem phaseVector_eq
    {n : Type*} [Fintype n] [DecidableEq n] (d q : n → ℂ) :
    phaseVector d q = (phaseDiagonal d)ᴴ *ᵥ q := by
  rw [phaseDiagonal, Matrix.diagonal_conjTranspose]
  ext i
  simp [phaseVector, Matrix.mulVec]

theorem phaseDiagonal_unit
    {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ)
    (hd : ∀ i, normSq (d i) = 1) :
    phaseDiagonal d * (phaseDiagonal d)ᴴ = 1 := by
  have hunit : ∀ i, d i * star (d i) = 1 := fun i => by
    simpa [mul_comm] using unit_mul (d i) (hd i)
  rw [phaseDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      starRingEnd_apply] using hunit i
  · simp [hij]

/-- A Hermitian quadratic form is unchanged when both its matrix and vector
are transported by the same diagonal unitary gauge. -/
theorem quadratic_phase_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (d q : n → ℂ)
    (hd : ∀ i, normSq (d i) = 1) :
    dotProduct (star (phaseVector d q))
        (((phaseDiagonal d)ᴴ * K * phaseDiagonal d) *ᵥ phaseVector d q) =
      dotProduct (star q) (K *ᵥ q) := by
  let D := phaseDiagonal d
  have hD : D * Dᴴ = 1 := phaseDiagonal_unit d hd
  rw [phaseVector_eq]
  change dotProduct (star (Dᴴ *ᵥ q)) ((Dᴴ * K * D) *ᵥ (Dᴴ *ᵥ q)) = _
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
    Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.dotProduct_mulVec]
  simp only [← Matrix.mul_assoc, hD, one_mul]
  rw [← Matrix.dotProduct_mulVec]
  rw [Matrix.mul_assoc, hD, Matrix.mul_one]

/-- A unit phase chosen so that the open segment from `z` to that phase does
not meet zero. -/
def perturbPhase (z : ℂ) : ℂ := if z.re = 0 then 1 else I

@[simp] theorem normSq_perturbPhase (z : ℂ) :
    normSq (perturbPhase z) = 1 := by
  by_cases hz : z.re = 0 <;> simp [perturbPhase, hz]

theorem convex_perturbPhase_ne_zero (z : ℂ) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * perturbPhase z) ≠ 0 := by
  by_cases hz : z.re = 0
  · intro h
    have hre := congrArg Complex.re h
    simp [perturbPhase, hz] at hre
    linarith
  · intro h
    have hre := congrArg Complex.re h
    simp [perturbPhase, hz] at hre
    have ht : 1 - t ≠ 0 := by linarith
    exact ht hre

def perturbVector {n : Type*} (q : n → ℂ) (t : ℝ) : n → ℂ :=
  fun i => (((1 - t : ℝ) : ℂ) * q i + (t : ℂ) * perturbPhase (q i))

theorem perturbVector_ne_zero
    {n : Type*} (q : n → ℂ) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (i : n) :
    perturbVector q t i ≠ 0 :=
  convex_perturbPhase_ne_zero (q i) ht₀ ht₁

end PermanentalDominance.Gauge
