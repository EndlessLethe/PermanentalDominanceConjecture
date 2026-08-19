import PermanentalDominance.N4.CorrelationReduction
import PermanentalDominance.N4.A4Certificate
import PermanentalDominance.N4.CycleCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Principal-three contractions

The four displayed inequalities are precisely the determinant inequalities
for the four principal `3 × 3` submatrices of a correlation matrix.  They
are the elementary PSD input used repeatedly by the low-order character
rows.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.FischerContractions

open CorrelationReduction

private theorem principal012 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation a b d) := by
  have h := hA.submatrix (![0, 1, 2] : Fin 3 → Fin 4)
  have heq : (correlation a b c d e f).submatrix
      (![0, 1, 2] : Fin 3 → Fin 4) (![0, 1, 2] : Fin 3 → Fin 4) =
      A4Certificate.correlation a b d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CorrelationReduction.correlation, A4Certificate.correlation]
  rw [heq] at h
  exact h

private theorem principal013 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation a c e) := by
  have h := hA.submatrix (![0, 1, 3] : Fin 3 → Fin 4)
  have heq : (correlation a b c d e f).submatrix
      (![0, 1, 3] : Fin 3 → Fin 4) (![0, 1, 3] : Fin 3 → Fin 4) =
      A4Certificate.correlation a c e := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CorrelationReduction.correlation, A4Certificate.correlation]
  rw [heq] at h
  exact h

private theorem principal023 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation b c f) := by
  have h := hA.submatrix (![0, 2, 3] : Fin 3 → Fin 4)
  have heq : (correlation a b c d e f).submatrix
      (![0, 2, 3] : Fin 3 → Fin 4) (![0, 2, 3] : Fin 3 → Fin 4) =
      A4Certificate.correlation b c f := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CorrelationReduction.correlation, A4Certificate.correlation]
  rw [heq] at h
  exact h

private theorem principal123 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    IsPSD (A4Certificate.correlation d e f) := by
  have h := hA.submatrix (![1, 2, 3] : Fin 3 → Fin 4)
  have heq : (correlation a b c d e f).submatrix
      (![1, 2, 3] : Fin 3 → Fin 4) (![1, 2, 3] : Fin 3 → Fin 4) =
      A4Certificate.correlation d e f := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CorrelationReduction.correlation, A4Certificate.correlation]
  rw [heq] at h
  exact h

theorem triangle012 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ 1 - (normSq a + normSq b + normSq d) +
      2 * (a * d * star b).re :=
  A4Certificate.det_correlation_real_nonneg (principal012 hA)

theorem triangle013 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ 1 - (normSq a + normSq c + normSq e) +
      2 * (a * e * star c).re :=
  A4Certificate.det_correlation_real_nonneg (principal013 hA)

theorem triangle023 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ 1 - (normSq b + normSq c + normSq f) +
      2 * (b * f * star c).re :=
  A4Certificate.det_correlation_real_nonneg (principal023 hA)

theorem triangle123 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    0 ≤ 1 - (normSq d + normSq e + normSq f) +
      2 * (d * f * star e).re :=
  A4Certificate.det_correlation_real_nonneg (principal123 hA)

/-! ## The `2+2` symmetric contraction -/

private def pairNormSq (z₀ z₁ : ℂ) : ℝ := normSq z₀ + normSq z₁

private def pairInner (y₀ y₁ g₀ g₁ : ℂ) : ℂ :=
  star y₀ * g₀ + star y₁ * g₁

private theorem pair_lagrange (y₀ y₁ g₀ g₁ : ℂ) :
    normSq (pairInner y₀ y₁ g₀ g₁) + normSq (y₀ * g₁ - y₁ * g₀) =
      pairNormSq y₀ y₁ * pairNormSq g₀ g₁ := by
  simp [pairInner, pairNormSq, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.star_def]
  ring

private theorem pair_cauchy (y₀ y₁ g₀ g₁ : ℂ) :
    normSq (pairInner y₀ y₁ g₀ g₁) ≤
      pairNormSq y₀ y₁ * pairNormSq g₀ g₁ := by
  rw [← pair_lagrange]
  exact le_add_of_nonneg_right (normSq_nonneg _)

private theorem coupled_pair_nonneg {e y₀ y₁ g₀ g₁ : ℂ}
    (he : normSq e ≤ 1) :
    0 ≤ pairNormSq y₀ y₁ + pairNormSq g₀ g₁ +
      2 * (star e * pairInner y₀ y₁ g₀ g₁).re := by
  let Y := pairNormSq y₀ y₁
  let G := pairNormSq g₀ g₁
  let q := (star e * pairInner y₀ y₁ g₀ g₁).re
  have hY : 0 ≤ Y := by
    exact add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hG : 0 ≤ G := by
    exact add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hYG : 0 ≤ Y * G := mul_nonneg hY hG
  have hinner : normSq (pairInner y₀ y₁ g₀ g₁) ≤ Y * G :=
    pair_cauchy _ _ _ _
  have hprod : normSq (star e * pairInner y₀ y₁ g₀ g₁) ≤ Y * G := by
    rw [Complex.normSq_mul]
    simp only [Complex.star_def, Complex.normSq_conj]
    calc
      normSq e * normSq (pairInner y₀ y₁ g₀ g₁) ≤ 1 * (Y * G) :=
        mul_le_mul he hinner (normSq_nonneg _) (by norm_num)
      _ = Y * G := one_mul _
  have hqraw : (star e * pairInner y₀ y₁ g₀ g₁).re ^ 2 ≤ Y * G := by
    rw [Complex.normSq_apply] at hprod
    nlinarith [sq_nonneg (star e * pairInner y₀ y₁ g₀ g₁).im]
  have hq : q ^ 2 ≤ Y * G := by
    simpa only [q] using hqraw
  by_cases hY0 : Y = 0
  · have hq0 : q = 0 := by nlinarith
    dsimp [Y, G, q] at hY hG hq0 ⊢
    linarith
  · have hYpos : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
    have hmul : 0 ≤ Y * (Y + G + 2 * q) := by
      nlinarith [sq_nonneg (Y + q)]
    have := (mul_nonneg_iff_of_pos_left hYpos).mp hmul
    simpa [Y, G, q] using this

def blockPermanentRhs (a b c d e f : ℂ) : ℝ :=
  1 + normSq b + normSq e + CycleCoordinates.D a b c d e f +
    2 * (a * d * f * star c).re

/-- Exact matching identity for the split `{0,2}|{1,3}`. -/
private theorem permanent_block_gap_identity (a b c d e f : ℂ)
    (hb : normSq b ≤ 1) :
    let r : ℝ := Real.sqrt (1 - normSq b)
    let y₀ : ℂ := a + star d * b
    let y₁ : ℂ := star d * (r : ℂ)
    let g₀ : ℂ := c + f * b
    let g₁ : ℂ := f * (r : ℂ)
    ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) - blockPermanentRhs a b c d e f =
      pairNormSq y₀ y₁ + pairNormSq g₀ g₁ +
        2 * (star e * pairInner y₀ y₁ g₀ g₁).re := by
  dsimp
  simp [ScalarAggregates.permanentForm, CycleCoordinates.T, CycleCoordinates.D,
    CycleCoordinates.C, CycleCoordinates.F, blockPermanentRhs, pairNormSq,
    pairInner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def]
  ring_nf
  have hb' : b.re ^ 2 + b.im ^ 2 ≤ 1 := by
    simpa [Complex.normSq_apply, pow_two] using hb
  have hnon : 0 ≤ 1 + (-b.re ^ 2 - b.im ^ 2) := by
    nlinarith
  have hrs := Real.sq_sqrt hnon
  rw [hrs]
  ring

/-- The scalar core of the first `2+2` Fischer contraction.  Notice that
only the two edge bounds belonging to the diagonal blocks enter the
proof.  This formulation lets us use the same certificate after the two
other pairings of the four vertices. -/
theorem block_permanent_contraction_of_bounds {a b c d e f : ℂ}
    (hb : normSq b ≤ 1) (he : normSq e ≤ 1) :
    blockPermanentRhs a b c d e f ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
  let r : ℝ := Real.sqrt (1 - normSq b)
  let y₀ : ℂ := a + star d * b
  let y₁ : ℂ := star d * (r : ℂ)
  let g₀ : ℂ := c + f * b
  let g₁ : ℂ := f * (r : ℂ)
  have hnonneg : 0 ≤ pairNormSq y₀ y₁ + pairNormSq g₀ g₁ +
      2 * (star e * pairInner y₀ y₁ g₀ g₁).re :=
    coupled_pair_nonneg he
  rw [← permanent_block_gap_identity a b c d e f hb] at hnonneg
  linarith

/-- The first `2+2` Fischer contraction in normalized coordinates. -/
theorem block_permanent_contraction {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    blockPermanentRhs a b c d e f ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) :=
  block_permanent_contraction_of_bounds (normSq_b_le_one hA) (normSq_e_le_one hA)

/-! ## The alternating `2+2` contraction -/

/-- Put a raw coordinate vector into the standard finite-dimensional
Euclidean space. -/
private def euclideanOfFn {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    EuclideanSpace ℂ ι :=
  (WithLp.equiv 2 _).symm x

/-- The antisymmetric tensor `x ⊗ y - y ⊗ x`, represented on all ordered
pairs.  Using ordered pairs avoids choosing an enumeration of the six
two-element subsets. -/
private def exteriorPair {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    EuclideanSpace ℂ (ι × ι) :=
  euclideanOfFn fun ij => x ij.1 * y ij.2 - y ij.1 * x ij.2

/-- The elementary inner-product identity for antisymmetric tensors. -/
private theorem exteriorPair_inner {ι : Type*} [Fintype ι]
    (x y z w : ι → ℂ) :
    @inner ℂ _ _ (exteriorPair x y) (exteriorPair z w) =
      2 * ((∑ i, star (x i) * z i) * (∑ i, star (y i) * w i) -
        (∑ i, star (x i) * w i) * (∑ i, star (y i) * z i)) := by
  classical
  simp only [exteriorPair, euclideanOfFn, PiLp.inner_apply,
    RCLike.inner_apply', WithLp.equiv_symm_pi_apply, map_sub, map_mul,
    starRingEnd_apply]
  rw [Fintype.sum_prod_type]
  have hpoint (i j : ι) :
      (star (x i) * star (y j) - star (y i) * star (x j)) *
          (z i * w j - w i * z j) =
        (star (x i) * z i) * (star (y j) * w j) -
        (star (x i) * w i) * (star (y j) * z j) -
        (star (y i) * z i) * (star (x j) * w j) +
        (star (y i) * w i) * (star (x j) * z j) := by
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
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

/-- Columns of the positive square root have Gram matrix `A`. -/
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

/-- Exterior Cauchy--Schwarz for the two complementary pairs
`{0,2}` and `{1,3}`.  This is the normalized `2 × 2` minor inequality
used in the alternating dihedral row. -/
theorem exterior_minor_bound {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    normSq (a * f - c * star d) ≤
      (1 - normSq b) * (1 - normSq e) := by
  let x0 := sqrtColumn hA 0
  let x1 := sqrtColumn hA 1
  let x2 := sqrtColumn hA 2
  let x3 := sqrtColumn hA 3
  let u := exteriorPair x0 x2
  let v := exteriorPair x1 x3
  have h00 := sqrtColumn_gram hA 0 0
  have h01 := sqrtColumn_gram hA 0 1
  have h02 := sqrtColumn_gram hA 0 2
  have h03 := sqrtColumn_gram hA 0 3
  have h10 := sqrtColumn_gram hA 1 0
  have h11 := sqrtColumn_gram hA 1 1
  have h12 := sqrtColumn_gram hA 1 2
  have h13 := sqrtColumn_gram hA 1 3
  have h20 := sqrtColumn_gram hA 2 0
  have h21 := sqrtColumn_gram hA 2 1
  have h22 := sqrtColumn_gram hA 2 2
  have h23 := sqrtColumn_gram hA 2 3
  have h30 := sqrtColumn_gram hA 3 0
  have h31 := sqrtColumn_gram hA 3 1
  have h32 := sqrtColumn_gram hA 3 2
  have h33 := sqrtColumn_gram hA 3 3
  have huv : @inner ℂ _ _ u v = 2 * (a * f - c * star d) := by
    rw [exteriorPair_inner]
    simp only [x0, x1, x2, x3]
    rw [h01, h23, h03, h21]
    simp [correlation] <;> ring
  have hvu : @inner ℂ _ _ v u = 2 * (star a * star f - star c * d) := by
    rw [exteriorPair_inner]
    simp only [x0, x1, x2, x3]
    rw [h10, h32, h12, h30]
    simp [correlation] <;> ring
  have huu : @inner ℂ _ _ u u = (2 * (1 - normSq b) : ℝ) := by
    rw [exteriorPair_inner]
    simp only [x0, x2]
    rw [h00, h22, h02, h20]
    simp [correlation, Complex.normSq_eq_conj_mul_self]
    ring
  have hvv : @inner ℂ _ _ v v = (2 * (1 - normSq e) : ℝ) := by
    rw [exteriorPair_inner]
    simp only [x1, x3]
    rw [h11, h33, h13, h31]
    simp [correlation, Complex.normSq_eq_conj_mul_self]
    ring
  have hcs : normSq (@inner ℂ _ _ u v) ≤
      (@inner ℂ _ _ u u).re * (@inner ℂ _ _ v v).re := by
    calc
      normSq (@inner ℂ _ _ u v) =
          ‖@inner ℂ _ _ u v‖ * ‖@inner ℂ _ _ u v‖ :=
        (Complex.norm_mul_self_eq_normSq _).symm
      _ = ‖@inner ℂ _ _ u v‖ * ‖@inner ℂ _ _ v u‖ := by
        rw [norm_inner_symm v u]
      _ ≤ (@inner ℂ _ _ u u).re * (@inner ℂ _ _ v v).re :=
        inner_mul_inner_self_le u v
  rw [huv, huu, hvv] at hcs
  simp only [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.ofReal_re] at hcs
  norm_num at hcs
  have hfour : 4 * normSq (a * f - c * star d) ≤
      4 * ((1 - normSq b) * (1 - normSq e)) := by
    ring_nf at hcs ⊢
    exact hcs
  nlinarith [hfour]

/-- The alternating block expression attached to the same split. -/
def blockDeterminantRhs (a b c d e f : ℂ) : ℝ :=
  (1 - normSq b) * (1 - normSq e) + normSq (a * f - c * star d)

/-- The two relabelled symmetric contractions give the two matching
lower bounds needed in the alternating estimate. -/
theorem permanent_ge_matching_af {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    (1 + normSq a) * (1 + normSq f) ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
  have h := block_permanent_contraction_of_bounds
    (a := b) (b := a) (c := c) (d := star d) (e := f) (f := e)
    (normSq_a_le_one hA) (normSq_f_le_one hA)
  have hP : ScalarAggregates.permanentForm
      (CycleCoordinates.T b a c (star d) f e)
      (CycleCoordinates.D b a c (star d) f e)
      (CycleCoordinates.C b a c (star d) f e)
      (CycleCoordinates.F b a c (star d) f e) =
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
    simp [ScalarAggregates.permanentForm, CycleCoordinates.T, CycleCoordinates.D,
      CycleCoordinates.C, CycleCoordinates.F, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def]
    ring
  have hR : (1 + normSq a) * (1 + normSq f) ≤
      blockPermanentRhs b a c (star d) f e := by
    have heq : blockPermanentRhs b a c (star d) f e =
        (1 + normSq a) * (1 + normSq f) +
          normSq (b * e + c * d) := by
      simp [blockPermanentRhs, CycleCoordinates.D, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.star_def]
      ring
    rw [heq]
    exact le_add_of_nonneg_right (normSq_nonneg _)
  rw [hP] at h
  exact hR.trans h

private theorem permanent_ge_matching_cd {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    (1 + normSq c) * (1 + normSq d) ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
  have h := block_permanent_contraction_of_bounds
    (a := b) (b := c) (c := a) (d := f) (e := star d) (f := star e)
    (normSq_c_le_one hA) (by simpa using normSq_d_le_one hA)
  have hP : ScalarAggregates.permanentForm
      (CycleCoordinates.T b c a f (star d) (star e))
      (CycleCoordinates.D b c a f (star d) (star e))
      (CycleCoordinates.C b c a f (star d) (star e))
      (CycleCoordinates.F b c a f (star d) (star e)) =
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
    simp [ScalarAggregates.permanentForm, CycleCoordinates.T, CycleCoordinates.D,
      CycleCoordinates.C, CycleCoordinates.F, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def]
    ring
  have hR : (1 + normSq c) * (1 + normSq d) ≤
      blockPermanentRhs b c a f (star d) (star e) := by
    have heq : blockPermanentRhs b c a f (star d) (star e) =
        (1 + normSq c) * (1 + normSq d) +
          normSq (b * star e + a * star f) := by
      simp [blockPermanentRhs, CycleCoordinates.D, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.star_def]
      ring
    rw [heq]
    exact le_add_of_nonneg_right (normSq_nonneg _)
  rw [hP] at h
  exact hR.trans h

/-- A convenient consequence of the two relabelled matching bounds: the
permanent dominates one plus the sum of the two opposite-edge products
`|a f|²` and `|c d|²`. -/
theorem permanent_ge_one_plus_opposite_products {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    1 + normSq a * normSq f + normSq c * normSq d ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
  let x := normSq a * normSq f
  let y := normSq c * normSq d
  let P := ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
    (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
    (CycleCoordinates.F a b c d e f)
  have ha0 := normSq_nonneg a
  have hc0 := normSq_nonneg c
  have hd0 := normSq_nonneg d
  have hf0 := normSq_nonneg f
  have ha1 := normSq_a_le_one hA
  have hd1 := normSq_d_le_one hA
  have hf1 := normSq_f_le_one hA
  have haf := permanent_ge_matching_af hA
  have hcd := permanent_ge_matching_cd hA
  change 1 + x + y ≤ P
  by_cases hxy : x ≤ y
  · have hyc : y ≤ normSq c := by
      dsimp [y]
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hd1)]
    change (1 + normSq c) * (1 + normSq d) ≤ P at hcd
    calc
      1 + x + y ≤ 1 + normSq c + normSq d + y := by nlinarith
      _ = (1 + normSq c) * (1 + normSq d) := by simp only [y]; ring
      _ ≤ P := hcd
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hxa : x ≤ normSq a := by
      dsimp [x]
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hf1)]
    change (1 + normSq a) * (1 + normSq f) ≤ P at haf
    calc
      1 + x + y ≤ 1 + normSq a + normSq f + x := by nlinarith
      _ = (1 + normSq a) * (1 + normSq f) := by simp only [x]; ring
      _ ≤ P := haf

/-- The determinant/exterior `2+2` contraction. -/
theorem block_determinant_contraction {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    blockDeterminantRhs a b c d e f ≤
      ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
        (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
        (CycleCoordinates.F a b c d e f) := by
  let p := normSq b
  let q := normSq e
  let s := Real.sqrt (normSq (a * f - c * star d))
  let x := normSq a * normSq f
  let y := normSq c * normSq d
  let P := ScalarAggregates.permanentForm (CycleCoordinates.T a b c d e f)
    (CycleCoordinates.D a b c d e f) (CycleCoordinates.C a b c d e f)
    (CycleCoordinates.F a b c d e f)
  have hp0 : 0 ≤ p := normSq_nonneg _
  have hq0 : 0 ≤ q := normSq_nonneg _
  have hp1 : p ≤ 1 := normSq_b_le_one hA
  have hq1 : q ≤ 1 := normSq_e_le_one hA
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = normSq (a * f - c * star d) :=
    Real.sq_sqrt (normSq_nonneg _)
  have hext : s ^ 2 ≤ (1 - p) * (1 - q) := by
    rw [hs2]
    exact exterior_minor_bound hA
  have hxy : s ≤ Real.sqrt x + Real.sqrt y := by
    have htri := norm_sub_le (a * f) (c * star d)
    have hxroot : Real.sqrt x = ‖a * f‖ := by
      simp [x, Complex.normSq_eq_norm_sq, Real.sqrt_mul (sq_nonneg ‖a‖),
        Real.sqrt_sq (norm_nonneg _), norm_mul]
    have hyroot : Real.sqrt y = ‖c * star d‖ := by
      simp [y, Complex.normSq_eq_norm_sq, Real.sqrt_mul (sq_nonneg ‖c‖),
        Real.sqrt_sq (norm_nonneg _), norm_mul]
    have hsroot : s = ‖a * f - c * star d‖ := by
      simp [s, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    simpa [hsroot, hxroot, hyroot] using htri
  have haf := permanent_ge_matching_af hA
  have hcd := permanent_ge_matching_cd hA
  have hx0 : 0 ≤ x := mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hy0 : 0 ≤ y := mul_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hxm : (1 + Real.sqrt x) ^ 2 ≤ P := by
    change (1 + normSq a) * (1 + normSq f) ≤ P at haf
    have hxprod : Real.sqrt x =
        Real.sqrt (normSq a) * Real.sqrt (normSq f) := by
      simp only [x]
      exact Real.sqrt_mul (normSq_nonneg a) _
    have ham : 2 * Real.sqrt x ≤ normSq a + normSq f := by
      rw [hxprod]
      nlinarith [sq_nonneg (Real.sqrt (normSq a) - Real.sqrt (normSq f)),
        Real.sq_sqrt (normSq_nonneg a), Real.sq_sqrt (normSq_nonneg f)]
    calc
      (1 + Real.sqrt x) ^ 2 = 1 + 2 * Real.sqrt x + Real.sqrt x ^ 2 := by ring
      _ = 1 + 2 * Real.sqrt x + x := by rw [Real.sq_sqrt hx0]
      _ ≤ 1 + normSq a + normSq f + x := by linarith
      _ = (1 + normSq a) * (1 + normSq f) := by simp only [x]; ring
      _ ≤ P := haf
  have hym : (1 + Real.sqrt y) ^ 2 ≤ P := by
    change (1 + normSq c) * (1 + normSq d) ≤ P at hcd
    have hyprod : Real.sqrt y =
        Real.sqrt (normSq c) * Real.sqrt (normSq d) := by
      simp only [y]
      exact Real.sqrt_mul (normSq_nonneg c) _
    have ham : 2 * Real.sqrt y ≤ normSq c + normSq d := by
      rw [hyprod]
      nlinarith [sq_nonneg (Real.sqrt (normSq c) - Real.sqrt (normSq d)),
        Real.sq_sqrt (normSq_nonneg c), Real.sq_sqrt (normSq_nonneg d)]
    calc
      (1 + Real.sqrt y) ^ 2 = 1 + 2 * Real.sqrt y + Real.sqrt y ^ 2 := by ring
      _ = 1 + 2 * Real.sqrt y + y := by rw [Real.sq_sqrt hy0]
      _ ≤ 1 + normSq c + normSq d + y := by linarith
      _ = (1 + normSq c) * (1 + normSq d) := by simp only [y]; ring
      _ ≤ P := hcd
  have hm : (1 + s / 2) ^ 2 ≤ P := by
    by_cases hle : Real.sqrt x ≤ Real.sqrt y
    · have : s / 2 ≤ Real.sqrt y := by nlinarith
      nlinarith [sq_nonneg (Real.sqrt y - s / 2)]
    · have : s / 2 ≤ Real.sqrt x := by
        have := le_of_not_ge hle
        nlinarith
      nlinarith [sq_nonneg (Real.sqrt x - s / 2)]
  have hscalar : (1 - p) * (1 - q) + s ^ 2 ≤ (1 + s / 2) ^ 2 := by
    have hpq0 : 0 ≤ p + q - p * q := by
      calc
        0 ≤ p * (1 - q) + q :=
          add_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hq1)) hq0
        _ = p + q - p * q := by ring
    have hsle : s ≤ 1 := by
      have hpq : (1 - p) * (1 - q) ≤ 1 := by
        nlinarith [hpq0]
      nlinarith
    have hs_term : 0 ≤ s - 3 * s ^ 2 / 4 := by
      have := mul_nonneg hs0 (by nlinarith : 0 ≤ 1 - 3 * s / 4)
      nlinarith
    rw [← sub_nonneg]
    convert add_nonneg hpq0 hs_term using 1 <;> ring
  unfold blockDeterminantRhs
  rw [← hs2]
  change (1 - p) * (1 - q) + s ^ 2 ≤ P
  exact hscalar.trans hm

end PermanentalDominance.N4.FischerContractions
