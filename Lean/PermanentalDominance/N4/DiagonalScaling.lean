import PermanentalDominance.N4.TableClosure

/-!
# Diagonal congruence and homogeneous scaling

These identities isolate the algebraic part of passing between a positive
diagonal matrix and its correlation normalization.  They do not assume that
the scale factors are nonzero.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.DiagonalScaling

def scaleMatrix (s : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i => (s i : ℂ)) * A *
    Matrix.diagonal (fun i => (s i : ℂ))

@[simp] theorem scaleMatrix_apply (s : Fin 4 → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    scaleMatrix s A i j = (s i : ℂ) * A i j * (s j : ℂ) := by
  simp [scaleMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem scaleMatrix_psd {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A)
    (s : Fin 4 → ℝ) : IsPSD (scaleMatrix s A) := by
  let D : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun i => (s i : ℂ)
  have hD : D.conjTranspose = D := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [D, Matrix.conjTranspose_apply]
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, hji]
  simpa [scaleMatrix, D, hD] using hA.mul_mul_conjTranspose_same D

theorem column_eq_zero_of_diagonal_eq_zero
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) (i : Fin 4)
    (hii : A i i = 0) : ∀ j, A j i = 0 := by
  let x : Fin 4 → ℂ := Pi.single i 1
  have hquad : dotProduct (star x) (Matrix.mulVec A x) = 0 := by
    simp_rw [x, Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_dotProduct, one_mul, Matrix.transpose_apply, hii]
  have hx : Matrix.mulVec A x = 0 :=
    (hA.dotProduct_mulVec_zero_iff x).1 hquad
  intro j
  have hj := congrFun hx j
  simpa [x, Matrix.mulVec_single_one] using hj

theorem row_eq_zero_of_diagonal_eq_zero
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) (i : Fin 4)
    (hii : A i i = 0) : ∀ j, A i j = 0 := by
  intro j
  calc
    A i j = star (A j i) := (hA.isHermitian.apply i j).symm
    _ = star 0 := by rw [column_eq_zero_of_diagonal_eq_zero hA i hii j]
    _ = 0 := map_zero (starRingEnd ℂ)

theorem permutationMonomial_eq_zero_of_diagonal_eq_zero
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) (i : Fin 4)
    (hii : A i i = 0) (sigma : S4) : permutationMonomial A sigma = 0 := by
  rw [permutationMonomial, Finset.prod_eq_zero (Finset.mem_univ i)]
  exact row_eq_zero_of_diagonal_eq_zero hA i hii (sigma i)

theorem permanent_eq_zero_of_diagonal_eq_zero
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) (i : Fin 4)
    (hii : A i i = 0) : A.permanent = 0 := by
  rw [Matrix.permanent]
  apply Finset.sum_eq_zero
  intro sigma _
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  exact column_eq_zero_of_diagonal_eq_zero hA i hii (sigma i)

theorem tableMatrixFunction_eq_zero_of_diagonal_eq_zero
    {H : Subgroup S4} (row : IrrepDatum H)
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) (i : Fin 4)
    (hii : A i i = 0) : row.tableMatrixFunction A = 0 := by
  rw [row.tableMatrixFunction_eq_sum]
  apply Finset.sum_eq_zero
  intro sigma _
  rw [permutationMonomial_eq_zero_of_diagonal_eq_zero hA i hii]
  ring

theorem product_comp_perm (s : Fin 4 → ℝ) (sigma : S4) :
    (∏ i, (s (sigma i) : ℂ)) = ∏ i, (s i : ℂ) := by
  apply Fintype.prod_equiv sigma
  simp

theorem permutationMonomial_scale (s : Fin 4 → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (sigma : S4) :
    permutationMonomial (scaleMatrix s A) sigma =
      ((∏ i, (s i : ℂ)) ^ 2) * permutationMonomial A sigma := by
  simp only [permutationMonomial, scaleMatrix_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, product_comp_perm]
  ring

theorem columnMonomial_scale (s : Fin 4 → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℂ) (sigma : S4) :
    (∏ i, scaleMatrix s A (sigma i) i) =
      ((∏ i, (s i : ℂ)) ^ 2) * ∏ i, A (sigma i) i := by
  simp only [scaleMatrix_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, product_comp_perm]
  ring

theorem permanent_scale (s : Fin 4 → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (scaleMatrix s A).permanent =
      ((∏ i, (s i : ℂ)) ^ 2) * A.permanent := by
  rw [Matrix.permanent, Matrix.permanent]
  simp_rw [columnMonomial_scale]
  rw [Finset.mul_sum]

theorem tableMatrixFunction_scale {H : Subgroup S4} (row : IrrepDatum H)
    (s : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    row.tableMatrixFunction (scaleMatrix s A) =
      ((∏ i, (s i : ℂ)) ^ 2) * row.tableMatrixFunction A := by
  rw [row.tableMatrixFunction_eq_sum, row.tableMatrixFunction_eq_sum]
  simp_rw [permutationMonomial_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  ring

end PermanentalDominance.N4.DiagonalScaling
