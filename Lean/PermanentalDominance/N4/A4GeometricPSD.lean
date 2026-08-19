import PermanentalDominance.N4.A4GeometricMinimum

/-!
# Positive-semidefinite Gram input for the geometric polynomial

This module connects the scalar quadratic argument to a `3 × 3` residual
Gram matrix.  The non-collinear case is obtained by Cramer's coordinates and
the Schur slack tested on the vector `(-z, 1)`.
-/

noncomputable section

open Complex Matrix Filter Topology
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4GeometricPSD

open A4GeometricGeneral A4GeometricHessian A4GeometricNoncollinear
open A4GeometricQuadratic
open A4GeometricMinimum A4GeometricNormalization

/-- Hermitian Gram matrix of three residual vectors. -/
def residualGram
    (a b c : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![
  (a : ℂ), h₁₂, h₁₃;
  star h₁₂, (b : ℂ), h₂₃;
  star h₁₃, star h₂₃, (c : ℂ)]

theorem residualGram_topLeft (a b c r s : ℝ) (p q : ℂ) :
    (residualGram a b c (g r s) p q).submatrix
        Fin.castSucc Fin.castSucc = G a b r s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [residualGram, G]

theorem topLeft_posSemidef
    {a b c r s : ℝ} {p q : ℂ}
    (hR : IsPSD (residualGram a b c (g r s) p q)) :
    IsPSD (G a b r s) := by
  have hsub := hR.submatrix Fin.castSucc
  simpa [residualGram_topLeft] using hsub

theorem gramDefect_nonneg
    {a b c r s : ℝ} {p q : ℂ}
    (hR : IsPSD (residualGram a b c (g r s) p q)) :
    0 ≤ gramDefect a b r s := by
  have hdet := PermanentalDominance.IsPSD.det_nonneg (topLeft_posSemidef hR)
  rw [G_det] at hdet
  exact (RCLike.nonneg_iff.mp hdet).1

/-- Cramer's coordinates of the third inner-product column in the independent
pair. -/
def gramCoordinates (a b r s : ℝ) (p q : ℂ) : Fin 2 → ℂ :=
  (((gramDefect a b r s : ℂ)⁻¹) •
    ((G a b r s).adjugate *ᵥ thirdInner p q))

theorem G_mulVec_gramCoordinates
    {a b r s : ℝ} {p q : ℂ} (hδ : 0 < gramDefect a b r s) :
    G a b r s *ᵥ gramCoordinates a b r s p q = thirdInner p q := by
  simp only [gramCoordinates, Matrix.mulVec_smul_assoc,
    Matrix.mulVec_mulVec, Matrix.mul_adjugate, G_det,
    Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  ext i
  simp [Pi.smul_apply]
  field_simp [hδ.ne']

/-- The PSD quadratic form tested on `(-z,1)` is exactly the Schur slack. -/
theorem residualGram_slack_nonneg
    {a b c r s : ℝ} {p q : ℂ} (z : Fin 2 → ℂ)
    (hR : IsPSD (residualGram a b c (g r s) p q))
    (hz : thirdInner p q = G a b r s *ᵥ z) :
    (dotProduct (star z) (G a b r s *ᵥ z)).re ≤ c := by
  let e : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
  have hblock : IsPSD (Matrix.fromBlocks (G a b r s)
      (Completion.column (thirdInner p q))
      (Completion.column (thirdInner p q))ᴴ
      (fun _ _ => (c : ℂ))) := by
    have hs := hR.submatrix e
    have heq :
        (residualGram a b c (g r s) p q).submatrix e e =
          Matrix.fromBlocks (G a b r s)
            (Completion.column (thirdInner p q))
            (Completion.column (thirdInner p q))ᴴ
            (fun _ _ => (c : ℂ)) := by
      have he₀ : e (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by native_decide
      have he₁ : e (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by native_decide
      have he₂ : e (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by native_decide
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [e, residualGram, G, thirdInner, Completion.column,
          Matrix.fromBlocks, he₀, he₁, he₂]
    rw [← heq]
    exact hs
  exact PermanentalDominance.GramExtension.block_slack_nonneg hblock hz

/-- `geometricP` is nonnegative for every genuinely non-collinear PSD
residual Gram matrix. -/
theorem geometricP_nonneg_of_posSemidef_noncollinear
    {a b c r s : ℝ} {p q : ℂ} (ha : 0 < a)
    (hδ : 0 < gramDefect a b r s)
    (hR : IsPSD (residualGram a b c (g r s) p q)) :
    0 ≤ geometricP a b c (g r s) p q := by
  let z := gramCoordinates a b r s p q
  apply geometricP_nonneg_of_coordinates z ha hδ
  · exact (G_mulVec_gramCoordinates hδ).symm
  · exact residualGram_slack_nonneg z hR
      (G_mulVec_gramCoordinates hδ).symm

set_option maxHeartbeats 2000000 in
/-- The normalized geometric polynomial is nonnegative on every PSD residual
Gram matrix.  We add a positive diagonal, apply the non-collinear theorem, and
then close the PSD cone by continuity. -/
theorem geometricP_nonneg_of_posSemidef
    {a b c : ℝ} {h₁₂ h₁₃ h₂₃ : ℂ}
    (hR : IsPSD (residualGram a b c h₁₂ h₁₃ h₂₃)) :
    0 ≤ geometricP a b c h₁₂ h₁₃ h₂₃ := by
  let r := h₁₂.re
  let s := -h₁₂.im
  have hg : g r s = h₁₂ := by
    apply Complex.ext <;> simp [g, r, s]
  have hlim : Tendsto
      (fun n : ℕ => geometricP
        (a + 1 / ((n : ℝ) + 1))
        (b + 1 / ((n : ℝ) + 1))
        (c + 1 / ((n : ℝ) + 1)) h₁₂ h₁₃ h₂₃)
      atTop (nhds (geometricP a b c h₁₂ h₁₃ h₂₃)) := by
    have hcont : Continuous fun t : ℝ =>
        geometricP (a + t) (b + t) (c + t) h₁₂ h₁₃ h₂₃ := by
      unfold geometricP symmetricTensorSumNormSq
        symmetricTensorFourierNormSq pairTensorDiag geometricGamma
      fun_prop
    simpa using hcont.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply ge_of_tendsto hlim
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  let t : ℝ := 1 / ((n : ℝ) + 1)
  have ht : 0 < t := by positivity
  have hreg :
      residualGram (a + t) (b + t) (c + t) h₁₂ h₁₃ h₂₃ =
        residualGram a b c h₁₂ h₁₃ h₂₃ +
          (t : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [residualGram]
  have hRtPos : Matrix.PosDef
      (residualGram (a + t) (b + t) (c + t) h₁₂ h₁₃ h₂₃) := by
    rw [hreg]
    exact Completion.add_posDiagonal_posDef hR ht
  have hRt : IsPSD
      (residualGram (a + t) (b + t) (c + t) h₁₂ h₁₃ h₂₃) :=
    hRtPos.posSemidef
  have hRtPos' : Matrix.PosDef
      (residualGram (a + t) (b + t) (c + t) (g r s) h₁₃ h₂₃) := by
    simpa [hg] using hRtPos
  have hGt : Matrix.PosDef (G (a + t) (b + t) r s) := by
    have hs := Completion.posDef_submatrix hRtPos'
      Fin.castSucc (Fin.castSucc_injective 2)
    simpa [residualGram_topLeft] using hs
  have hδt : 0 < gramDefect (a + t) (b + t) r s := by
    have hdet := hGt.det_pos
    rw [G_det] at hdet
    exact (RCLike.pos_iff.mp hdet).1
  have hat : 0 < a + t := by
    let e : Fin 2 → ℂ := ![1, 0]
    have he := hGt.re_dotProduct_pos (x := e) (by simp [e])
    simpa [e, G, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ] using he
  have hPt := geometricP_nonneg_of_posSemidef_noncollinear
    (a := a + t) (b := b + t) (c := c + t)
    (r := r) (s := s) (p := h₁₃) (q := h₂₃) hat hδt
    (by simpa [hg] using hRt)
  simpa [t, hg] using hPt

end PermanentalDominance.N4.A4GeometricPSD
