import PermanentalDominance.N4.FischerContractions
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The `3+1` permanent contraction

For a Gram matrix, the permanental cofactors of a principal three-set form
the Gram matrix of the three symmetric two-tensors.  Hence the difference
between the full permanent and the principal `3 × 3` permanent is a
nonnegative quadratic form in the remaining three Gram coordinates.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.PrincipalPermanentContraction

open CorrelationReduction CycleCoordinates ScalarAggregates

private def euclideanOfFn {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    EuclideanSpace ℂ ι :=
  (WithLp.equiv 2 _).symm x

private def symmetricPair {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    EuclideanSpace ℂ (ι × ι) :=
  euclideanOfFn fun ij => x ij.1 * y ij.2 + y ij.1 * x ij.2

private theorem symmetricPair_inner {ι : Type*} [Fintype ι]
    (x y z w : ι → ℂ) :
    @inner ℂ _ _ (symmetricPair x y) (symmetricPair z w) =
      2 * ((∑ i, star (x i) * z i) * (∑ i, star (y i) * w i) +
        (∑ i, star (x i) * w i) * (∑ i, star (y i) * z i)) := by
  classical
  simp only [symmetricPair, euclideanOfFn, PiLp.inner_apply,
    RCLike.inner_apply', WithLp.equiv_symm_pi_apply, map_add, map_mul,
    starRingEnd_apply]
  rw [Fintype.sum_prod_type]
  have hpoint (i j : ι) :
      (star (x i) * star (y j) + star (y i) * star (x j)) *
          (z i * w j + w i * z j) =
        (star (x i) * z i) * (star (y j) * w j) +
        (star (x i) * w i) * (star (y j) * z j) +
        (star (y i) * z i) * (star (x j) * w j) +
        (star (y i) * w i) * (star (x j) * z j) := by
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have hC :
      (∑ i, ∑ j, (star (y i) * z i) * (star (x j) * w j)) =
        ∑ i, ∑ j, (star (x i) * w i) * (star (y j) * z j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD :
      (∑ i, ∑ j, (star (y i) * w i) * (star (x j) * z j)) =
        ∑ i, ∑ j, (star (x i) * z i) * (star (y j) * w j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hAcomm :
      (∑ i, ∑ j, (star (x i) * z i) * (star (y j) * w j)) =
        ∑ i, ∑ j, (star (x j) * z j) * (star (y i) * w i) := by
    rw [Finset.sum_comm]
  have hBcomm :
      (∑ i, ∑ j, (star (x i) * w i) * (star (y j) * z j)) =
        ∑ i, ∑ j, (star (x j) * w j) * (star (y i) * z i) := by
    rw [Finset.sum_comm]
  rw [hC, hD, hAcomm, hBcomm]
  ring

private def sqrtColumn {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A)
    (j : Fin 4) : Fin 4 → ℂ :=
  fun i => hA.sqrt i j

private theorem sqrtColumn_gram {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) (i j : Fin 4) :
    ∑ k, star (sqrtColumn hA i k) * sqrtColumn hA j k = A i j := by
  classical
  have hherm := hA.posSemidef_sqrt.isHermitian
  calc
    ∑ k, star (sqrtColumn hA i k) * sqrtColumn hA j k =
        ∑ k, hA.sqrt i k * hA.sqrt k j := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [sqrtColumn]
          rw [hherm.apply i k]
    _ = (hA.sqrt * hA.sqrt) i j := by rw [Matrix.mul_apply]
    _ = A i j := by rw [hA.sqrt_mul_self]

def principalPermanent012 (a b d : ℂ) : ℝ :=
  1 + normSq a + normSq b + normSq d + 2 * (a * d * star b).re

/-- Permanent Fischer for the principal set `{0,1,2}` and the singleton
`{3}`, whose diagonal entry is one. -/
theorem principal012_contraction {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    principalPermanent012 a b d ≤
      permanentForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  let x0 := sqrtColumn hA 0
  let x1 := sqrtColumn hA 1
  let x2 := sqrtColumn hA 2
  let y0 := symmetricPair x1 x2
  let y1 := symmetricPair x0 x2
  let y2 := symmetricPair x0 x1
  let v := (star c) • y0 + (star e) • y1 + (star f) • y2
  have h00 := sqrtColumn_gram hA 0 0
  have h01 := sqrtColumn_gram hA 0 1
  have h02 := sqrtColumn_gram hA 0 2
  have h10 := sqrtColumn_gram hA 1 0
  have h11 := sqrtColumn_gram hA 1 1
  have h12 := sqrtColumn_gram hA 1 2
  have h20 := sqrtColumn_gram hA 2 0
  have h21 := sqrtColumn_gram hA 2 1
  have h22 := sqrtColumn_gram hA 2 2
  have hv0 := (@inner_self_nonneg ℂ
    (EuclideanSpace ℂ (Fin 4 × Fin 4)) _ _ _ v)
  rw [RCLike.re_eq_complex_re] at hv0
  have hv : 0 ≤ (@inner ℂ _ _ v v).re := hv0
  have heq : (@inner ℂ _ _ v v).re =
      2 * (permanentForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) - principalPermanent012 a b d) := by
    simp only [v, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, map_add, Complex.add_re, map_mul, starRingEnd_apply,
      star_star]
    simp only [x0, x1, x2, y0, y1, y2]
    simp_rw [symmetricPair_inner]
    rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
    simp [correlation, permanentForm, principalPermanent012, T, D, C, F,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def]
    ring
  rw [heq] at hv
  linarith

/-- The principal three permanent dominates its leading `2 × 2`
permanent. -/
theorem principal012_ge_edge01 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    1 + normSq a ≤ principalPermanent012 a b d := by
  have ha := normSq_a_le_one hA
  have hgap := normSq_nonneg (b + a * d)
  have hrest : 0 ≤ (1 - normSq a) * normSq d :=
    mul_nonneg (sub_nonneg.mpr ha) (normSq_nonneg d)
  rw [← sub_nonneg]
  rw [show principalPermanent012 a b d - (1 + normSq a) =
      normSq (b + a * d) + (1 - normSq a) * normSq d by
    simp [principalPermanent012, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.star_def]
    ring]
  exact add_nonneg hgap hrest

end PermanentalDominance.N4.PrincipalPermanentContraction
