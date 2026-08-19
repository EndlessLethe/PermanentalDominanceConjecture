import PermanentalDominance.N4.A4GeometricBridge
import PermanentalDominance.N4.FischerContractions
import PermanentalDominance.N4.CharacterTables
import PermanentalDominance.N4.PermutationEnumeration

/-!
# The non-real `A₄` gap

The character expansion is the scalar `c₀ + zᴴKz`.  This file first proves
its nonnegativity in the positive-determinant Schur case.  The certificate
identity makes the proof division-free except for the final use of
`det B > 0`.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4Gap

open A4Certificate A4GeometricBridge CorrelationReduction FischerContractions
open PermutationEnumeration CycleCoordinates ScalarAggregates

abbrev HA4 : Subgroup S4 := representative .a4

local instance : Fintype HA4 := Fintype.ofFinite HA4

def a4PositiveClass : Finset S4 :=
  (representativeCarrier .v4Normal).image fun v =>
    v * ConcretePerm.cycle012 * v⁻¹

/-- The primitive-root row whose root agrees with the corrected certificate. -/
def omegaCharacter (sigma : HA4) : ℂ :=
  if sigma.1 ∈ representativeCarrier .v4Normal then 1
  else if sigma.1 ∈ a4PositiveClass then A4Certificate.omega
  else A4Certificate.omega ^ 2

/-- The other non-real row, defined pointwise rather than through the invalid
`chi ↦ conj (chi ∘ inv)` shortcut. -/
def omegaConjugateCharacter (sigma : HA4) : ℂ :=
  star (omegaCharacter sigma)

/-- Enumerate the subgroup through its certified concrete carrier.  Using
`attach` makes every subtype witness definitional and avoids asking the
kernel to decide membership in an abstract subgroup. -/
def allA4Rows : Finset HA4 := (representativeCarrier .a4).attach

theorem allA4Rows_eq_univ : allA4Rows = Finset.univ := by
  ext sigma
  simp only [Finset.mem_univ, iff_true]
  exact Finset.mem_attach _ _

/-! A second, computational presentation of the same carrier is used only
for the twelve-term character expansion.  Each membership proof is checked
against the concrete registered carrier, while the names of the underlying
permutations match the shallow monomial lemmas in `PermutationEnumeration`. -/

def q0123 : HA4 := ⟨p0123, by change p0123 ∈ representativeCarrier .a4; native_decide⟩
def q0231 : HA4 := ⟨p0231, by change p0231 ∈ representativeCarrier .a4; native_decide⟩
def q0312 : HA4 := ⟨p0312, by change p0312 ∈ representativeCarrier .a4; native_decide⟩
def q1032 : HA4 := ⟨p1032, by change p1032 ∈ representativeCarrier .a4; native_decide⟩
def q1203 : HA4 := ⟨p1203, by change p1203 ∈ representativeCarrier .a4; native_decide⟩
def q1320 : HA4 := ⟨p1320, by change p1320 ∈ representativeCarrier .a4; native_decide⟩
def q2013 : HA4 := ⟨p2013, by change p2013 ∈ representativeCarrier .a4; native_decide⟩
def q2130 : HA4 := ⟨p2130, by change p2130 ∈ representativeCarrier .a4; native_decide⟩
def q2301 : HA4 := ⟨p2301, by change p2301 ∈ representativeCarrier .a4; native_decide⟩
def q3021 : HA4 := ⟨p3021, by change p3021 ∈ representativeCarrier .a4; native_decide⟩
def q3102 : HA4 := ⟨p3102, by change p3102 ∈ representativeCarrier .a4; native_decide⟩
def q3210 : HA4 := ⟨p3210, by change p3210 ∈ representativeCarrier .a4; native_decide⟩

def explicitA4RowsList : Multiset HA4 :=
  [q0123, q0231, q0312, q1032, q1203, q1320,
   q2013, q2130, q2301, q3021, q3102, q3210]

theorem explicitA4RowsList_nodup : explicitA4RowsList.Nodup := by native_decide

def explicitA4Rows : Finset HA4 :=
  ⟨explicitA4RowsList, explicitA4RowsList_nodup⟩

theorem explicitA4Rows_eq_allA4Rows : explicitA4Rows = allA4Rows := by
  native_decide

theorem omegaCharacter_q0123 : omegaCharacter q0123 = 1 := by
  rw [omegaCharacter, if_pos (by native_decide)]
theorem omegaCharacter_q0231 : omegaCharacter q0231 = A4Certificate.omega ^ 2 := by
  rw [omegaCharacter, if_neg (by native_decide), if_neg (by native_decide)]
theorem omegaCharacter_q0312 : omegaCharacter q0312 = A4Certificate.omega := by
  rw [omegaCharacter, if_neg (by native_decide), if_pos (by native_decide)]
theorem omegaCharacter_q1032 : omegaCharacter q1032 = 1 := by
  rw [omegaCharacter, if_pos (by native_decide)]
theorem omegaCharacter_q1203 : omegaCharacter q1203 = A4Certificate.omega := by
  rw [omegaCharacter, if_neg (by native_decide), if_pos (by native_decide)]
theorem omegaCharacter_q1320 : omegaCharacter q1320 = A4Certificate.omega ^ 2 := by
  rw [omegaCharacter, if_neg (by native_decide), if_neg (by native_decide)]
theorem omegaCharacter_q2013 : omegaCharacter q2013 = A4Certificate.omega ^ 2 := by
  rw [omegaCharacter, if_neg (by native_decide), if_neg (by native_decide)]
theorem omegaCharacter_q2130 : omegaCharacter q2130 = A4Certificate.omega := by
  rw [omegaCharacter, if_neg (by native_decide), if_pos (by native_decide)]
theorem omegaCharacter_q2301 : omegaCharacter q2301 = 1 := by
  rw [omegaCharacter, if_pos (by native_decide)]
theorem omegaCharacter_q3021 : omegaCharacter q3021 = A4Certificate.omega := by
  rw [omegaCharacter, if_neg (by native_decide), if_pos (by native_decide)]
theorem omegaCharacter_q3102 : omegaCharacter q3102 = A4Certificate.omega ^ 2 := by
  rw [omegaCharacter, if_neg (by native_decide), if_neg (by native_decide)]
theorem omegaCharacter_q3210 : omegaCharacter q3210 = 1 := by
  rw [omegaCharacter, if_pos (by native_decide)]

theorem omegaConjugateCharacter_q0123 : omegaConjugateCharacter q0123 = 1 := by
  simp [omegaConjugateCharacter, omegaCharacter_q0123]

theorem star_omega_sq : star (A4Certificate.omega ^ 2) = A4Certificate.omega := by
  change (starRingEnd ℂ) (A4Certificate.omega ^ 2) = A4Certificate.omega
  rw [map_pow]
  simp only [starRingEnd_apply, A4Certificate.star_omega]
  calc
    (A4Certificate.omega ^ 2) ^ 2 = A4Certificate.omega ^ 4 := by ring
    _ = A4Certificate.omega := A4Certificate.omega_pow_four

theorem omegaConjugateCharacter_q0231 :
    omegaConjugateCharacter q0231 = A4Certificate.omega := by
  rw [omegaConjugateCharacter, omegaCharacter_q0231, star_omega_sq]
theorem omegaConjugateCharacter_q0312 :
    omegaConjugateCharacter q0312 = A4Certificate.omega ^ 2 := by
  simp [omegaConjugateCharacter, omegaCharacter_q0312]
theorem omegaConjugateCharacter_q1032 : omegaConjugateCharacter q1032 = 1 := by
  simp [omegaConjugateCharacter, omegaCharacter_q1032]
theorem omegaConjugateCharacter_q1203 :
    omegaConjugateCharacter q1203 = A4Certificate.omega ^ 2 := by
  simp [omegaConjugateCharacter, omegaCharacter_q1203]
theorem omegaConjugateCharacter_q1320 :
    omegaConjugateCharacter q1320 = A4Certificate.omega := by
  rw [omegaConjugateCharacter, omegaCharacter_q1320, star_omega_sq]
theorem omegaConjugateCharacter_q2013 :
    omegaConjugateCharacter q2013 = A4Certificate.omega := by
  rw [omegaConjugateCharacter, omegaCharacter_q2013, star_omega_sq]
theorem omegaConjugateCharacter_q2130 :
    omegaConjugateCharacter q2130 = A4Certificate.omega ^ 2 := by
  simp [omegaConjugateCharacter, omegaCharacter_q2130]
theorem omegaConjugateCharacter_q2301 : omegaConjugateCharacter q2301 = 1 := by
  simp [omegaConjugateCharacter, omegaCharacter_q2301]
theorem omegaConjugateCharacter_q3021 :
    omegaConjugateCharacter q3021 = A4Certificate.omega ^ 2 := by
  simp [omegaConjugateCharacter, omegaCharacter_q3021]
theorem omegaConjugateCharacter_q3102 :
    omegaConjugateCharacter q3102 = A4Certificate.omega := by
  rw [omegaConjugateCharacter, omegaCharacter_q3102, star_omega_sq]
theorem omegaConjugateCharacter_q3210 : omegaConjugateCharacter q3210 = 1 := by
  simp [omegaConjugateCharacter, omegaCharacter_q3210]

/-- The odd relabelling which exchanges vertices zero and one. -/
def swap01Index : Fin 4 → Fin 4 := ![1, 0, 2, 3]

theorem submatrix_swap01_correlation (a b c d e f : ℂ) :
    (CorrelationReduction.correlation a b c d e f).submatrix
        swap01Index swap01Index =
      CorrelationReduction.correlation (star a) d e b c f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap01Index, CorrelationReduction.correlation]

theorem swap01_correlation_posSemidef {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    IsPSD (CorrelationReduction.correlation (star a) d e b c f) := by
  have hswap := hA.submatrix swap01Index
  rw [submatrix_swap01_correlation] at hswap
  exact hswap

/-- The real scalar represented by the corrected non-real `A₄` gap. -/
def gapForm (a b c d e f : ℂ) : ℝ :=
  c0 a b d +
    (dotProduct (star ![c, e, f])
      (gapMatrix a b d *ᵥ ![c, e, f])).re

/-- Schur-complement consequence of the geometric matrix certificate. -/
theorem gapForm_nonneg_of_det_pos {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f))
    (hdet : 0 < (A4Certificate.correlation a b d).det) :
    0 ≤ gapForm a b c d e f := by
  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    CorrelationReduction.correlation a b c d e f
  let B : Matrix (Fin 3) (Fin 3) ℂ := A4Certificate.correlation a b d
  let K : Matrix (Fin 3) (Fin 3) ℂ := A4Certificate.gapMatrix a b d
  let T : Matrix (Fin 3) (Fin 3) ℂ := A4Certificate.certificate a b d
  let z : Fin 3 → ℂ := ![c, e, f]
  let p : Fin 3 → ℂ := B⁻¹ *ᵥ z
  have hB : IsPSD B := by
    have hsub := hA.submatrix (fun i : Fin 3 => Fin.castSucc i)
    have heq :
        (CorrelationReduction.correlation a b c d e f).submatrix
            (fun i : Fin 3 => Fin.castSucc i) (fun i : Fin 3 => Fin.castSucc i) = B := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [heq] at hsub
    exact hsub
  have hT : IsPSD T := by
    simpa [T] using A4GeometricBridge.certificate_posSemidef_geometric hB
  have hd : 0 < B.det := by simpa [B] using hdet
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hd)
  have hp : B *ᵥ p = z := by
    calc
      B *ᵥ p = B *ᵥ (B⁻¹ *ᵥ z) := by rfl
      _ = (B * B⁻¹) *ᵥ z := by rw [Matrix.mulVec_mulVec]
      _ = z := by rw [Matrix.mul_nonsing_inv B hunit, Matrix.one_mulVec]
  have hp0 := congr_fun hp (0 : Fin 3)
  have hp1 := congr_fun hp (1 : Fin 3)
  have hp2 := congr_fun hp (2 : Fin 3)
  simp [B, z, A4Certificate.correlation, Matrix.mulVec,
    Fin.sum_univ_succ] at hp0 hp1 hp2
  change p 0 + (a * p 1 + b * p 2) = c at hp0
  change star a * p 0 + (p 1 + d * p 2) = e at hp1
  change star b * p 0 + (star d * p 1 + p 2) = f at hp2
  let x : Fin 4 → ℂ := ![-p 0, -p 1, -p 2, 1]
  have hAx : A *ᵥ x =
      ![0, 0, 0, 1 - dotProduct (star z) p] := by
    ext i
    fin_cases i
    · simp [A, x, CorrelationReduction.correlation, Matrix.mulVec,
        Fin.sum_univ_succ]
      linear_combination -hp0
    · simp [A, x, CorrelationReduction.correlation, Matrix.mulVec,
        Fin.sum_univ_succ]
      simp only [starRingEnd_apply]
      linear_combination -hp1
    · simp [A, x, CorrelationReduction.correlation, Matrix.mulVec,
        Fin.sum_univ_succ]
      simp only [starRingEnd_apply]
      linear_combination -hp2
    · simp [A, x, z, CorrelationReduction.correlation, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
      ring
  have hschurC := hA.2 x
  rw [show CorrelationReduction.correlation a b c d e f = A by rfl, hAx] at hschurC
  have hschur := (RCLike.nonneg_iff.mp hschurC).1
  simp [x, dotProduct, Fin.sum_univ_succ] at hschur
  have hadj : B.adjugate = B.det • B⁻¹ := by
    calc
      B.adjugate = 1 * B.adjugate := by rw [Matrix.one_mul]
      _ = (B⁻¹ * B) * B.adjugate := by
        rw [Matrix.nonsing_inv_mul B hunit]
      _ = B⁻¹ * (B * B.adjugate) := by rw [Matrix.mul_assoc]
      _ = B⁻¹ * (B.det • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
        rw [Matrix.mul_adjugate]
      _ = B.det • B⁻¹ := by
        rw [Matrix.mul_smul, Matrix.mul_one]
  have hcert :
      dotProduct (star z) (T *ᵥ z) =
        B.det * (dotProduct (star z) (K *ᵥ z) +
          (c0 a b d : ℂ) * dotProduct (star z) (B⁻¹ *ᵥ z)) := by
    dsimp [T, K]
    rw [A4Certificate.certificate, show A4Certificate.correlation a b d = B by rfl,
      hadj]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    ring
  let delta : ℝ := B.det.re
  have hdreal : 0 < delta := (RCLike.pos_iff.mp hd).1
  have hdcast : (delta : ℂ) = B.det := by
    apply Complex.ext
    · rfl
    · simpa [delta] using (RCLike.pos_iff.mp hd).2.symm
  have hcertReal :
      (dotProduct (star z) (T *ᵥ z)).re =
        delta * ((dotProduct (star z) (K *ᵥ z)).re +
          c0 a b d * (dotProduct (star z) (B⁻¹ *ᵥ z)).re) := by
    rw [hcert, ← hdcast]
    simp [Complex.mul_re]
  have hTquad := hT.re_dotProduct_nonneg z
  have hc0 := A4Certificate.c0_nonneg hB
  have hschur' : (dotProduct (star z) p).re ≤ 1 := by
    simpa [z, dotProduct, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im] using hschur
  have hcertReal' :
      (dotProduct (star z) (T *ᵥ z)).re =
        delta * ((dotProduct (star z) (K *ᵥ z)).re +
          c0 a b d * (dotProduct (star z) p).re) := by
    simpa [p] using hcertReal
  have hinner : 0 ≤ (dotProduct (star z) (K *ᵥ z)).re +
      c0 a b d * (dotProduct (star z) p).re := by
    by_contra! hn
    have hneg := mul_neg_of_pos_of_neg hdreal hn
    rw [← hcertReal'] at hneg
    exact (not_lt_of_ge hTquad) hneg
  have htail : 0 ≤ c0 a b d * (1 - (dotProduct (star z) p).re) :=
    mul_nonneg hc0 (sub_nonneg.mpr hschur')
  dsimp [gapForm]
  change 0 ≤ c0 a b d + (dotProduct (star z) (K *ᵥ z)).re
  nlinarith

theorem scaled_correlation (t : ℝ) (a b c d e f : ℂ) :
    CorrelationReduction.correlation (t * a) (t * b) (t * c)
        (t * d) (t * e) (t * f) =
      (t : ℂ) • CorrelationReduction.correlation a b c d e f +
        ((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CorrelationReduction.correlation]

theorem scaled_correlation_posSemidef {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    IsPSD (CorrelationReduction.correlation (t * a) (t * b) (t * c)
      (t * d) (t * e) (t * f)) := by
  rw [scaled_correlation]
  exact IsPSD.add (IsPSD.nonneg_smul hA ht0)
    (IsPSD.nonneg_smul Matrix.PosSemidef.one (sub_nonneg.mpr ht1))

theorem scaled_principal_det_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {a b d : ℂ} (hB : IsPSD (A4Certificate.correlation a b d)) :
    0 < (A4Certificate.correlation (t * a) (t * b) (t * d)).det := by
  have hmatrix :
      A4Certificate.correlation (t * a) (t * b) (t * d) =
        (t : ℂ) • A4Certificate.correlation a b d +
          ((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A4Certificate.correlation]
  have hdiag : Matrix.PosDef
      (((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    constructor
    · rw [Matrix.IsHermitian]
      simp
    · intro x hx
      rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_smul]
      have hs : 0 < ((1 - t : ℝ) : ℂ) := by
        apply RCLike.pos_iff.mpr
        exact ⟨sub_pos.mpr ht1, by simp⟩
      exact mul_pos hs (dotProduct_star_self_pos_iff.mpr hx)
  rw [hmatrix]
  exact (Matrix.PosDef.posSemidef_add (IsPSD.nonneg_smul hB ht0) hdiag).det_pos

/-- Boundary closure by the radial regularization
`A_t = (1-t)I+tA`, `t ↑ 1`. -/
theorem gapForm_nonneg {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    0 ≤ gapForm a b c d e f := by
  let q : ℕ → ℝ := fun n => (n : ℝ) / (n + 1)
  let g : ℝ → ℝ := fun t =>
    gapForm (t * a) (t * b) (t * c) (t * d) (t * e) (t * f)
  have hq : Filter.Tendsto q Filter.atTop (nhds 1) := by
    simpa [q] using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hgcont : Continuous g := by
    dsimp [g]
    simp [gapForm, A4Certificate.c0, A4Certificate.gapMatrix,
      A4Certificate.omega, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    fun_prop
  have hg : Filter.Tendsto (fun n => g (q n)) Filter.atTop (nhds (g 1)) :=
    hgcont.continuousAt.tendsto.comp hq
  have hn : ∀ n : ℕ, 0 ≤ g (q n) := by
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hq0 : 0 ≤ q n := by dsimp [q]; positivity
    have hq1 : q n < 1 := by
      dsimp [q]
      exact (div_lt_one hden).2 (by linarith)
    have hscaled := scaled_correlation_posSemidef hq0 hq1.le hA
    have hprincipal : IsPSD (A4Certificate.correlation a b d) := by
      have hsub := hA.submatrix (fun i : Fin 3 => Fin.castSucc i)
      have heq :
          (CorrelationReduction.correlation a b c d e f).submatrix
              (fun i : Fin 3 => Fin.castSucc i) (fun i : Fin 3 => Fin.castSucc i) =
            A4Certificate.correlation a b d := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [heq] at hsub
      exact hsub
    exact gapForm_nonneg_of_det_pos hscaled
      (scaled_principal_det_pos hq0 hq1 hprincipal)
  have hlim : 0 ≤ g 1 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hg hn
  simpa [g] using hlim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem omega_generalized_gap_expansion (a b c d e f : ℂ) :
    (CorrelationReduction.correlation a b c d e f).permanent.re -
        (generalizedMatrixFunction HA4 omegaCharacter
          (CorrelationReduction.correlation a b c d e f)).re =
      gapForm a b c d e f := by
  rw [PermutationEnumeration.permanent_expansion]
  rw [generalizedMatrixFunction, ← allA4Rows_eq_univ,
    ← explicitA4Rows_eq_allA4Rows]
  have how2 : A4Certificate.omega ^ 2 = -A4Certificate.omega - 1 := by
    linear_combination A4Certificate.omega_sq_add_omega_add_one
  have how2re : (A4Certificate.omega ^ 2).re = -(1 : ℝ) / 2 := by
    rw [how2]
    simp
    norm_num
  have how2im : (A4Certificate.omega ^ 2).im = Real.sqrt 3 / 2 := by
    rw [how2]
    simp
  simp [explicitA4Rows, explicitA4RowsList,
    omegaCharacter_q0123, omegaCharacter_q0231, omegaCharacter_q0312,
    omegaCharacter_q1032, omegaCharacter_q1203, omegaCharacter_q1320,
    omegaCharacter_q2013, omegaCharacter_q2130, omegaCharacter_q2301,
    omegaCharacter_q3021, omegaCharacter_q3102, omegaCharacter_q3210]
  simp only [q0123, q0231, q0312, q1032, q1203, q1320,
    q2013, q2130, q2301, q3021, q3102, q3210,
    PermutationEnumeration.monomial_p0123,
    PermutationEnumeration.monomial_p0231,
    PermutationEnumeration.monomial_p0312,
    PermutationEnumeration.monomial_p1032,
    PermutationEnumeration.monomial_p1203,
    PermutationEnumeration.monomial_p1320,
    PermutationEnumeration.monomial_p2013,
    PermutationEnumeration.monomial_p2130,
    PermutationEnumeration.monomial_p2301,
    PermutationEnumeration.monomial_p3021,
    PermutationEnumeration.monomial_p3102,
    PermutationEnumeration.monomial_p3210]
  simp only [ScalarAggregates.permanentForm, CycleCoordinates.T,
    CycleCoordinates.D, CycleCoordinates.C, CycleCoordinates.F, gapForm,
    A4Certificate.c0, Complex.normSq_apply]
  simp [A4Certificate.gapMatrix, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [how2re, how2im]
  ring_nf

/-- The requested normalized non-real `A₄` dominance statement on a
four-by-four correlation matrix. -/
theorem a4Omega_generalized_gap_nonneg {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    0 ≤ (CorrelationReduction.correlation a b c d e f).permanent.re -
      (generalizedMatrixFunction HA4 omegaCharacter
        (CorrelationReduction.correlation a b c d e f)).re := by
  rw [omega_generalized_gap_expansion]
  exact gapForm_nonneg hA

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem omegaConjugate_generalized_gap_expansion (a b c d e f : ℂ) :
    (CorrelationReduction.correlation a b c d e f).permanent.re -
        (generalizedMatrixFunction HA4 omegaConjugateCharacter
          (CorrelationReduction.correlation a b c d e f)).re =
      gapForm (star a) d e b c f := by
  rw [PermutationEnumeration.permanent_expansion]
  rw [generalizedMatrixFunction, ← allA4Rows_eq_univ,
    ← explicitA4Rows_eq_allA4Rows]
  have how2 : A4Certificate.omega ^ 2 = -A4Certificate.omega - 1 := by
    linear_combination A4Certificate.omega_sq_add_omega_add_one
  have how2re : (A4Certificate.omega ^ 2).re = -(1 : ℝ) / 2 := by
    rw [how2]
    simp
    norm_num
  have how2im : (A4Certificate.omega ^ 2).im = Real.sqrt 3 / 2 := by
    rw [how2]
    simp
  simp [explicitA4Rows, explicitA4RowsList,
    omegaConjugateCharacter_q0123, omegaConjugateCharacter_q0231,
    omegaConjugateCharacter_q0312, omegaConjugateCharacter_q1032,
    omegaConjugateCharacter_q1203, omegaConjugateCharacter_q1320,
    omegaConjugateCharacter_q2013, omegaConjugateCharacter_q2130,
    omegaConjugateCharacter_q2301, omegaConjugateCharacter_q3021,
    omegaConjugateCharacter_q3102, omegaConjugateCharacter_q3210]
  simp only [q0123, q0231, q0312, q1032, q1203, q1320,
    q2013, q2130, q2301, q3021, q3102, q3210,
    PermutationEnumeration.monomial_p0123,
    PermutationEnumeration.monomial_p0231,
    PermutationEnumeration.monomial_p0312,
    PermutationEnumeration.monomial_p1032,
    PermutationEnumeration.monomial_p1203,
    PermutationEnumeration.monomial_p1320,
    PermutationEnumeration.monomial_p2013,
    PermutationEnumeration.monomial_p2130,
    PermutationEnumeration.monomial_p2301,
    PermutationEnumeration.monomial_p3021,
    PermutationEnumeration.monomial_p3102,
    PermutationEnumeration.monomial_p3210]
  simp only [ScalarAggregates.permanentForm, CycleCoordinates.T,
    CycleCoordinates.D, CycleCoordinates.C, CycleCoordinates.F, gapForm,
    A4Certificate.c0, Complex.normSq_apply]
  simp [A4Certificate.gapMatrix, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [how2re, how2im]
  ring_nf

/-- Dominance for the second non-real row.  Its scalar gap is the first
row's gap after the explicit odd relabelling `swap01Index`; positivity is
therefore inherited from the relabelled correlation matrix. -/
theorem a4OmegaConjugate_generalized_gap_nonneg {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    0 ≤ (CorrelationReduction.correlation a b c d e f).permanent.re -
      (generalizedMatrixFunction HA4 omegaConjugateCharacter
        (CorrelationReduction.correlation a b c d e f)).re := by
  rw [omegaConjugate_generalized_gap_expansion]
  exact gapForm_nonneg (swap01_correlation_posSemidef hA)

end PermanentalDominance.N4.A4Gap
