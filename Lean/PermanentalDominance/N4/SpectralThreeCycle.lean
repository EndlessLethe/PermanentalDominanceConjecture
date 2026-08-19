import PermanentalDominance.N4.CycleCoordinates

/-!
# The four-eigenvalue moment certificate

For nonnegative eigenvalues, Cauchy--Schwarz in moment form is the elementary
sum-of-squares identity

`(Σλ)(Σλ³) - (Σλ²)² = Σ_{i<j} λᵢλⱼ(λᵢ-λⱼ)²`.

The second theorem is the exact arithmetic conversion used for the `[22]`
character row.
-/

namespace PermanentalDominance.N4.SpectralThreeCycle

open scoped BigOperators
open scoped ComplexOrder

open Matrix

theorem trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal ((↑) ∘ hA.eigenvalues)
  have hUU : star U * U = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := by
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hspec : A = U * D * star U := by
    simpa [U, D] using hA.spectral_theorem
  have hpow : ∀ m : ℕ, A ^ m = U * D ^ m * star U := by
    intro m
    induction m with
    | zero => simpa [hUU']
    | succ m ih =>
        calc
          A ^ (m + 1) = A ^ m * A := pow_succ A m
          _ = (U * D ^ m * star U) * (U * D * star U) := by rw [ih, hspec]
          _ = U * D ^ m * (star U * U) * D * star U := by
            simp only [Matrix.mul_assoc]
          _ = U * (D ^ m * D) * star U := by rw [hUU]; simp [Matrix.mul_assoc]
          _ = U * D ^ (m + 1) * star U := by rw [pow_succ]
  have hDpow : D ^ k = diagonal (fun i => (hA.eigenvalues i : ℂ) ^ k) := by
    induction k with
    | zero => simp [D]
    | succ k ih =>
        rw [pow_succ, ih, Matrix.diagonal_mul_diagonal]
        ext i j
        simp [D, pow_succ]
  rw [hpow k, Matrix.trace_mul_cycle, hUU]
  rw [hDpow]
  simpa using Matrix.trace_diagonal (fun i => (hA.eigenvalues i : ℂ) ^ k)

theorem four_moment_cauchy (lambda : Fin 4 → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) :
    (∑ i, lambda i ^ 2) ^ 2 ≤ (∑ i, lambda i) * (∑ i, lambda i ^ 3) := by
  have h01 : 0 ≤ lambda 0 * lambda 1 * (lambda 0 - lambda 1) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 0) (hlambda 1)) (sq_nonneg _)
  have h02 : 0 ≤ lambda 0 * lambda 2 * (lambda 0 - lambda 2) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 0) (hlambda 2)) (sq_nonneg _)
  have h03 : 0 ≤ lambda 0 * lambda 3 * (lambda 0 - lambda 3) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 0) (hlambda 3)) (sq_nonneg _)
  have h12 : 0 ≤ lambda 1 * lambda 2 * (lambda 1 - lambda 2) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 1) (hlambda 2)) (sq_nonneg _)
  have h13 : 0 ≤ lambda 1 * lambda 3 * (lambda 1 - lambda 3) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 1) (hlambda 3)) (sq_nonneg _)
  have h23 : 0 ≤ lambda 2 * lambda 3 * (lambda 2 - lambda 3) ^ 2 :=
    mul_nonneg (mul_nonneg (hlambda 2) (hlambda 3)) (sq_nonneg _)
  simp only [Fin.sum_univ_four]
  nlinarith

theorem aggregate_bound_of_moments {lambda : Fin 4 → ℝ} {T C : ℝ}
    (hlambda : ∀ i, 0 ≤ lambda i)
    (h₁ : ∑ i, lambda i = 4)
    (h₂ : ∑ i, lambda i ^ 2 = 4 + 2 * T)
    (h₃ : ∑ i, lambda i ^ 3 = 4 + 6 * T + 3 * C) :
    T ^ 2 / 2 ≤ T + 3 * C / 2 := by
  have h := four_moment_cauchy lambda hlambda
  rw [h₁, h₂, h₃] at h
  nlinarith

open CycleCoordinates CorrelationReduction

theorem correlation_trace (a b c d e f : ℂ) :
    (correlation a b c d e f).trace = 4 := by
  simp [Matrix.trace, Matrix.diag_apply, correlation, Fin.sum_univ_four]
  norm_num

theorem correlation_trace_sq (a b c d e f : ℂ) :
    ((correlation a b c d e f) ^ 2).trace =
      (4 + 2 * T a b c d e f : ℝ) := by
  apply Complex.ext <;>
    simp [Matrix.trace, pow_two, Matrix.mul_apply, correlation, T,
      Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem correlation_trace_cube (a b c d e f : ℂ) :
    ((correlation a b c d e f) ^ 3).trace =
      (4 + 6 * T a b c d e f + 3 * C a b c d e f : ℝ) := by
  apply Complex.ext <;>
    simp [Matrix.trace, show (3 : ℕ) = 2 + 1 by omega, pow_succ, pow_two,
      Matrix.mul_apply, correlation, T, C, Fin.sum_univ_succ,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem correlation_spectral_bound {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    T a b c d e f ^ 2 / 2 ≤
      T a b c d e f + 3 * C a b c d e f / 2 := by
  let lambda : Fin 4 → ℝ := hA.isHermitian.eigenvalues
  apply aggregate_bound_of_moments (lambda := lambda)
  · intro i
    simpa [lambda] using hA.eigenvalues_nonneg i
  · have h := trace_pow_eq_sum_eigenvalues_pow hA.isHermitian 1
    rw [pow_one, correlation_trace] at h
    have hr := congrArg Complex.re h
    simpa [lambda] using hr.symm
  · have h := trace_pow_eq_sum_eigenvalues_pow hA.isHermitian 2
    rw [correlation_trace_sq] at h
    have hr := congrArg Complex.re h
    have hre2 (x : ℝ) : ((x : ℂ) ^ 2).re = x ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hr' : 4 + 2 * T a b c d e f =
        ∑ i, (((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ^ 2).re := by
      simpa only [map_sum, Complex.ofReal_re] using hr
    have hsum2 :
        (∑ i, (((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ^ 2).re) =
          ∑ i, hA.isHermitian.eigenvalues i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hre2 _
    rw [hsum2] at hr'
    simpa [lambda] using hr'.symm
  · have h := trace_pow_eq_sum_eigenvalues_pow hA.isHermitian 3
    rw [correlation_trace_cube] at h
    have hr := congrArg Complex.re h
    have hre3 (x : ℝ) : ((x : ℂ) ^ 3).re = x ^ 3 := by
      norm_num [pow_succ, pow_two, Complex.mul_re, Complex.mul_im]
    have hr' : 4 + 6 * T a b c d e f + 3 * C a b c d e f =
        ∑ i, (((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ^ 3).re := by
      simpa only [map_sum, Complex.ofReal_re] using hr
    have hsum3 :
        (∑ i, (((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ^ 3).re) =
          ∑ i, hA.isHermitian.eigenvalues i ^ 3 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hre3 _
    rw [hsum3] at hr'
    simpa [lambda] using hr'.symm

end PermanentalDominance.N4.SpectralThreeCycle
