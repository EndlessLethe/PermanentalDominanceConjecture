import PermanentalDominance.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Positive-semidefinite closure lemmas

The adjugate lemma is useful in the `A₄` Schur-complement certificate.  Its proof avoids a
singular/nonsingular case split: write `A = R * R` using the positive-semidefinite square root, use
`adj (R * R) = adj R * adj R`, and observe that `adj R` is Hermitian.
-/

noncomputable section

open scoped ComplexOrder

namespace PermanentalDominance.IsPSD

theorem adjugate {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsPSD A) : IsPSD A.adjugate := by
  rw [← hA.sqrt_mul_self, Matrix.adjugate_mul_distrib]
  have hAdj : (hA.sqrt.adjugate).IsHermitian := hA.posSemidef_sqrt.isHermitian.adjugate
  simpa [hAdj.eq] using Matrix.posSemidef_conjTranspose_mul_self hA.sqrt.adjugate

end PermanentalDominance.IsPSD


