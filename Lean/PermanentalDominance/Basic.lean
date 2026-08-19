import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Normalized generalized matrix functions

This file fixes the normalization used throughout the development.  If `V` is an irreducible
representation of a subgroup `H ≤ Sₙ`, its normalized generalized matrix function is

`(1 / dim V) * ∑ σ : H, character V σ * ∏ i, A i (σ i)`.

The division by `dim V = character V 1` is essential: without it the claimed inequality already
fails at the identity matrix for every irreducible character of degree greater than one.
-/

noncomputable section

open scoped BigOperators
open scoped ComplexOrder

namespace PermanentalDominance

abbrev Perm (n : Type*) := Equiv.Perm n

/-- The positive-semidefinite cone used throughout the development. -/
abbrev IsPSD {n : Type*} [Fintype n] (A : Matrix n n ℂ) : Prop :=
  A.PosSemidef

namespace IsPSD

theorem add {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (hA : IsPSD A) (hB : IsPSD B) : IsPSD (A + B) :=
  Matrix.PosSemidef.add hA hB

theorem nonneg_smul {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : IsPSD A) {r : ℝ} (hr : 0 ≤ r) : IsPSD ((r : ℂ) • A) := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    simpa using congrArg (fun X : Matrix n n ℂ => (r : ℂ) • X) hA.1
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg (by exact_mod_cast hr) (hA.2 x)

/-- A Hermitian complex matrix is positive semidefinite once the real part of
each quadratic form is nonnegative. -/
theorem of_re_dotProduct_nonneg {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ x : n → ℂ, 0 ≤ (dotProduct (star x) (Matrix.mulVec A x)).re) :
    IsPSD A := by
  refine ⟨hA, fun x => RCLike.nonneg_iff.mpr ⟨h x, ?_⟩⟩
  have hstar :
      star (dotProduct (star x) (Matrix.mulVec A x)) =
        dotProduct (star x) (Matrix.mulVec A x) := by
    change (starRingEnd ℂ) (dotProduct (star x) (Matrix.mulVec A x)) =
      dotProduct (star x) (Matrix.mulVec A x)
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul,
      starRingEnd_apply, star_star]
    have hentry (i j : n) : star (A i j) = A j i := by
      simpa using hA.apply j i
    simp_rw [hentry]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.star_apply, star_star]
    ring
  have him := congrArg Complex.im hstar
  change -(dotProduct (star x) (Matrix.mulVec A x)).im =
    (dotProduct (star x) (Matrix.mulVec A x)).im at him
  change (dotProduct (star x) (Matrix.mulVec A x)).im = 0
  linarith

theorem det_nonneg {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsPSD A) : 0 ≤ A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  let e : n → ℝ := hA.isHermitian.eigenvalues
  change 0 ≤ ∏ i, (e i : ℂ)
  have hparts : ∀ s : Finset n,
      (∏ i ∈ s, (e i : ℂ)).re = ∏ i ∈ s, e i ∧
      (∏ i ∈ s, (e i : ℂ)).im = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp [ha, Complex.mul_re, Complex.mul_im, ih.1, ih.2]
  have hp := hparts Finset.univ
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0 ≤ (∏ i, (e i : ℂ)).re
    rw [hp.1]
    exact Finset.prod_nonneg fun i _ => by simpa [e] using hA.eigenvalues_nonneg i
  · change (∏ i, (e i : ℂ)).im = 0
    exact hp.2

end IsPSD

/-- The matrix monomial attached to a permutation. -/
def permutationMonomial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (σ : Perm n) : ℂ :=
  ∏ i : n, A i (σ i)

/-- The (unnormalized) generalized matrix function attached to an arbitrary coefficient
function on a subgroup of the symmetric group. -/
def generalizedMatrixFunction {n : Type*} [Fintype n] [DecidableEq n]
    (H : Subgroup (Perm n)) (χ : H → ℂ) (A : Matrix n n ℂ) : ℂ :=
  letI : Fintype H := Fintype.ofFinite H
  ∑ σ : H, χ σ * permutationMonomial A σ.1

/-- A generalized matrix function normalized by the supplied character degree.  In applications
`degree = χ 1`; keeping the coefficient function abstract lets the analytic part of the proof stay
independent of the representation-theory API. -/
def normalizedMatrixFunction {n : Type*} [Fintype n] [DecidableEq n]
    (H : Subgroup (Perm n)) (χ : H → ℂ) (degree : ℂ) (A : Matrix n n ℂ) : ℂ :=
  generalizedMatrixFunction H χ A / degree

/-- The pointwise normalized permanental-dominance assertion. -/
def DominatesAt {n : Type*} [Fintype n] [DecidableEq n]
    (H : Subgroup (Perm n)) (χ : H → ℂ) (degree : ℂ) (A : Matrix n n ℂ) : Prop :=
  (normalizedMatrixFunction H χ degree A).re ≤ A.permanent.re

end PermanentalDominance
