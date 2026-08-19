import PermanentalDominance.N4.A4Certificate
import PermanentalDominance.N4.CorrelationReduction
import PermanentalDominance.Completion
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The geometric route to the non-real `A₄` certificate

The original proof of the remaining `A₄` row does not start from the
characteristic polynomial used in `A4Interior`.  Its central input is instead
the four-vector inequality

`c₀ + qᴴ K q ≥ 0`

for every positive-semidefinite correlation completion of the principal block
`B`.  A Schur-complement argument then implies

`K + c₀ B⁻¹ ⪰ 0`,

and hence the matrix certificate

`det(B) K + c₀ adj(B) ⪰ 0`.

This module restores that geometric interface and the Schur-complement half of
the old proof.  The theorem `certificate_posSemidef_of_fourVector` is independent
of the spectral coefficient certificate: it assumes only the four-vector
inequality, which the downstream direct Gram/SOS proof supplies.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4Geometric

open A4Certificate
open PermanentalDominance.Completion

private abbrev fin3OneEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv

@[simp] private theorem fin3OneEquiv_symm_zero :
    fin3OneEquiv.symm (0 : Fin 4) = Sum.inl 0 := by native_decide

@[simp] private theorem fin3OneEquiv_symm_one :
    fin3OneEquiv.symm (1 : Fin 4) = Sum.inl 1 := by native_decide

@[simp] private theorem fin3OneEquiv_symm_two :
    fin3OneEquiv.symm (2 : Fin 4) = Sum.inl 2 := by native_decide

@[simp] private theorem fin3OneEquiv_symm_three :
    fin3OneEquiv.symm (3 : Fin 4) = Sum.inr 0 := by native_decide

/-- The `4 × 4` correlation completion of the principal `A₄` block by a
three-vector `q`.  It is defined through a `3+1` block decomposition so that
Mathlib's Schur-complement theorem applies without a conversion layer. -/
def completion (u v w : ℂ) (q : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Matrix.fromBlocks (A4Certificate.correlation u v w) (column q)
    (column q)ᴴ (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
      fin3OneEquiv.symm fin3OneEquiv.symm

/-- The block definition agrees entrywise with the standard six-coordinate
correlation matrix used by the row-expansion modules. -/
theorem completion_eq_correlation (u v w : ℂ) (q : Fin 3 → ℂ) :
    completion u v w q =
      CorrelationReduction.correlation u v (q 0) w (q 1) (q 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CorrelationReduction.correlation, completion, column,
      A4Certificate.correlation, Matrix.fromBlocks]

/-- Recover the canonical `3 + 1` block form from the reindexed completion. -/
theorem completionBlock_posSemidef {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (completion u v w q)) :
    IsPSD (Matrix.fromBlocks (A4Certificate.correlation u v w) (column q)
      (column q)ᴴ (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  apply (Matrix.posSemidef_submatrix_equiv fin3OneEquiv.symm).mp
  simpa [completion] using hA

/-- Reindex a positive-semidefinite `3 + 1` block as the standard completion. -/
theorem completion_posSemidef_of_block {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (Matrix.fromBlocks (A4Certificate.correlation u v w)
      (column q) (column q)ᴴ (1 : Matrix (Fin 1) (Fin 1) ℂ))) :
    IsPSD (completion u v w q) := by
  simpa [completion] using hA.submatrix fin3OneEquiv.symm

/-- The rank-one matrix contributed by the last column of a completion. -/
def completionRankOne (q : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Completion.rankOne q

/-- Schur residual of the last unit diagonal entry in a completion. -/
def completionResidual (u v w : ℂ) (q : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  A4Certificate.correlation u v w - completionRankOne q

theorem completionResidual_posSemidef {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (completion u v w q)) :
    IsPSD (completionResidual u v w q) := by
  have hschur := Completion.residual_posSemidef_of_fromBlocks
    (completionBlock_posSemidef hA)
  simpa [completionResidual, completionRankOne, Completion.residual,
    Completion.rankOne] using hschur

/-- The scalar gap occurring in the old four-vector proof. -/
def fourVectorGap (u v w : ℂ) (q : Fin 3 → ℂ) : ℝ :=
  c0 u v w + (dotProduct (star q) (gapMatrix u v w *ᵥ q)).re

@[fun_prop] theorem continuous_starRingEnd_comp {X : Type*}
    [TopologicalSpace X] {f : X → ℂ} (hf : Continuous f) :
    Continuous fun x => (starRingEnd ℂ) (f x) := by
  simpa only [starRingEnd_apply] using continuous_star.comp hf

@[fun_prop] theorem continuous_gapMatrix_comp {X : Type*}
    [TopologicalSpace X] {u v w : X → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => gapMatrix (u x) (v x) (w x) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [gapMatrix] <;> fun_prop

@[fun_prop] theorem continuous_c0_comp {X : Type*}
    [TopologicalSpace X] {u v w : X → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => c0 (u x) (v x) (w x) := by
  unfold c0
  fun_prop

@[fun_prop] theorem continuous_fourVectorGap_comp {X : Type*}
    [TopologicalSpace X] {u v w : X → ℂ} {q : X → Fin 3 → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hq : Continuous q) :
    Continuous fun x => fourVectorGap (u x) (v x) (w x) (q x) := by
  unfold fourVectorGap
  fun_prop

/-- The precise geometric input used by the old proof. -/
def FourVectorProperty (u v w : ℂ) : Prop :=
  ∀ q : Fin 3 → ℂ, IsPSD (completion u v w q) →
    0 ≤ fourVectorGap u v w q

/-- The old Schur-complement argument: the four-vector inequality alone
implies positivity of the corrected `A₄` certificate. -/
theorem certificate_posSemidef_of_fourVector {u v w : ℂ}
    (hB : IsPSD (A4Certificate.correlation u v w))
    (hfour : FourVectorProperty u v w) :
    IsPSD (certificate u v w) := by
  rw [certificate]
  apply Completion.ellipsoidCertificate_posSemidef hB
    (gapMatrix_isHermitian u v w)
  intro q hblock
  have hcompletion := completion_posSemidef_of_block hblock
  simpa [fourVectorGap] using hfour q hcompletion

end PermanentalDominance.N4.A4Geometric
