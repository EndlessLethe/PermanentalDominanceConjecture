import PermanentalDominance.N4.A4GeometricPSD
import PermanentalDominance.Gauge

noncomputable section
open Complex Matrix Filter Topology
open scoped ComplexOrder
namespace PermanentalDominance.N4.A4GeometricFourVector

open A4Certificate A4Geometric A4GeometricPSD
open PermanentalDominance.Gauge

def phaseDiag (d₁ d₂ d₃ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Gauge.phaseDiagonal ![d₁, d₂, d₃]

theorem gap_phase (d₁ d₂ d₃ u v w : ℂ)
    (hd₁ : normSq d₁ = 1) (hd₂ : normSq d₂ = 1)
    (hd₃ : normSq d₃ = 1) :
    gapMatrix (star d₁ * d₂ * u) (star d₁ * d₃ * v)
        (star d₂ * d₃ * w) =
      (phaseDiag d₁ d₂ d₃)ᴴ * gapMatrix u v w *
        phaseDiag d₁ d₂ d₃ := by
  have h₁ := unit_mul d₁ hd₁
  have h₂ := unit_mul d₂ hd₂
  have h₃ := unit_mul d₃ hd₃
  have h₁' : d₁ * (starRingEnd ℂ) d₁ = 1 := by simpa [mul_comm] using h₁
  have h₂' : d₂ * (starRingEnd ℂ) d₂ = 1 := by simpa [mul_comm] using h₂
  have h₃' : d₃ * (starRingEnd ℂ) d₃ = 1 := by simpa [mul_comm] using h₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseDiag, Gauge.phaseDiagonal, gapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ,
      map_mul]
  · exact h₁.symm
  · linear_combination ((starRingEnd ℂ) d₁ * d₂ * v * (starRingEnd ℂ) w) * h₃'
  · linear_combination ((starRingEnd ℂ) d₁ * d₃ * u * w) * h₂'
  · linear_combination (d₁ * (starRingEnd ℂ) d₂ * w * (starRingEnd ℂ) v) * h₃'
  · exact h₂.symm
  · linear_combination ((starRingEnd ℂ) d₂ * d₃ * v * (starRingEnd ℂ) u) * h₁'
  · linear_combination (d₁ * (starRingEnd ℂ) d₃ * (starRingEnd ℂ) u * (starRingEnd ℂ) w) * h₂'
  · linear_combination (d₂ * (starRingEnd ℂ) d₃ * u * (starRingEnd ℂ) v) * h₁'
  · exact h₃.symm

def phaseVec (d₁ d₂ d₃ : ℂ) (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  Gauge.phaseVector ![d₁, d₂, d₃] q

theorem phaseVec_eq (d₁ d₂ d₃ : ℂ) (q : Fin 3 → ℂ) :
    phaseVec d₁ d₂ d₃ q =
      (phaseDiag d₁ d₂ d₃)ᴴ *ᵥ q := by
  exact Gauge.phaseVector_eq ![d₁, d₂, d₃] q

theorem phaseDiag_unit (d₁ d₂ d₃ : ℂ)
    (hd₁ : normSq d₁ = 1) (hd₂ : normSq d₂ = 1)
    (hd₃ : normSq d₃ = 1) :
    phaseDiag d₁ d₂ d₃ * (phaseDiag d₁ d₂ d₃)ᴴ = 1 := by
  simpa [phaseDiag] using
    Gauge.phaseDiagonal_unit ![d₁, d₂, d₃] (by
      intro i
      fin_cases i <;> assumption)

theorem quadratic_phase (d₁ d₂ d₃ u v w : ℂ) (q : Fin 3 → ℂ)
    (hd₁ : normSq d₁ = 1) (hd₂ : normSq d₂ = 1)
    (hd₃ : normSq d₃ = 1) :
    dotProduct (star (phaseVec d₁ d₂ d₃ q))
        (gapMatrix (star d₁ * d₂ * u) (star d₁ * d₃ * v)
          (star d₂ * d₃ * w) *ᵥ phaseVec d₁ d₂ d₃ q) =
      dotProduct (star q) (gapMatrix u v w *ᵥ q) := by
  rw [gap_phase d₁ d₂ d₃ u v w hd₁ hd₂ hd₃]
  exact Gauge.quadratic_phase_invariant
    (gapMatrix u v w) ![d₁, d₂, d₃] q (by
      intro i
      fin_cases i <;> assumption)

theorem c0_phase (d₁ d₂ d₃ u v w : ℂ)
    (hd₁ : normSq d₁ = 1) (hd₂ : normSq d₂ = 1)
    (hd₃ : normSq d₃ = 1) :
    c0 (star d₁ * d₂ * u) (star d₁ * d₃ * v)
        (star d₂ * d₃ * w) = c0 u v w := by
  have h₁ := unit_mul d₁ hd₁
  have h₂ := unit_mul d₂ hd₂
  have h₃ := unit_mul d₃ hd₃
  have h₁' : d₁ * star d₁ = 1 := by simpa [mul_comm] using h₁
  have h₂' : d₂ * star d₂ = 1 := by simpa [mul_comm] using h₂
  have h₃' : d₃ * star d₃ = 1 := by simpa [mul_comm] using h₃
  have ht :
      (star d₁ * d₂ * u) * (star d₂ * d₃ * w) *
          star (star d₁ * d₃ * v) = u * w * star v := by
    rw [show star (star d₁ * d₃ * v) = d₁ * star d₃ * star v by
      simp [map_mul]]
    calc
      _ = (d₁ * star d₁) * (d₂ * star d₂) *
          (d₃ * star d₃) * (u * w * star v) := by ring
      _ = u * w * star v := by rw [h₁', h₂', h₃']; ring
  have hu : normSq (star d₁ * d₂ * u) = normSq u := by
    simp [Complex.normSq_mul, Complex.normSq_conj, Complex.star_def, hd₁, hd₂]
  have hv : normSq (star d₁ * d₃ * v) = normSq v := by
    simp [Complex.normSq_mul, Complex.normSq_conj, Complex.star_def, hd₁, hd₃]
  have hw : normSq (star d₂ * d₃ * w) = normSq w := by
    simp [Complex.normSq_mul, Complex.normSq_conj, Complex.star_def, hd₂, hd₃]
  have htomega :
      (1 - omega) * (star d₁ * d₂ * u) * (star d₂ * d₃ * w) *
          star (star d₁ * d₃ * v) = (1 - omega) * u * w * star v := by
    calc
      _ = (1 - omega) *
          ((star d₁ * d₂ * u) * (star d₂ * d₃ * w) *
            star (star d₁ * d₃ * v)) := by ring
      _ = (1 - omega) * (u * w * star v) := by rw [ht]
      _ = (1 - omega) * u * w * star v := by ring
  unfold c0
  rw [hu, hv, hw, htomega]

theorem fourVectorGap_phase (d₁ d₂ d₃ u v w : ℂ) (q : Fin 3 → ℂ)
    (hd₁ : normSq d₁ = 1) (hd₂ : normSq d₂ = 1)
    (hd₃ : normSq d₃ = 1) :
    fourVectorGap (star d₁ * d₂ * u) (star d₁ * d₃ * v)
        (star d₂ * d₃ * w) (phaseVec d₁ d₂ d₃ q) =
      fourVectorGap u v w q := by
  simp only [fourVectorGap, c0_phase d₁ d₂ d₃ u v w hd₁ hd₂ hd₃,
    quadratic_phase d₁ d₂ d₃ u v w q hd₁ hd₂ hd₃]

open A4GeometricNormalization

/-- Exact geometric normalization for arbitrary complex last-column entries. -/
theorem fourVectorGap_complex_normalization
    (a₁ a₂ a₃ : ℂ) (n₁ n₂ n₃ : ℝ) (h₁₂ h₁₃ h₂₃ : ℂ)
    (ha₁ : normSq a₁ * (1 + n₁) = 1)
    (ha₂ : normSq a₂ * (1 + n₂) = 1)
    (ha₃ : normSq a₃ * (1 + n₃) = 1) :
    fourVectorGap
        (a₁ * star a₂ * (1 + h₁₂))
        (a₁ * star a₃ * (1 + h₁₃))
        (a₂ * star a₃ * (1 + h₂₃))
        ![a₁, a₂, a₃] =
      normSq (a₁ * a₂ * a₃) *
        geometricP n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ := by
  have ha₁0 : a₁ ≠ 0 := by
    intro h
    subst a₁
    norm_num at ha₁
  have ha₂0 : a₂ ≠ 0 := by
    intro h
    subst a₂
    norm_num at ha₂
  have ha₃0 : a₃ ≠ 0 := by
    intro h
    subst a₃
    norm_num at ha₃
  let r₁ := polarRadius a₁
  let r₂ := polarRadius a₂
  let r₃ := polarRadius a₃
  let d₁ := polarPhase a₁
  let d₂ := polarPhase a₂
  let d₃ := polarPhase a₃
  have hr₁ : 0 < r₁ := polarRadius_pos ha₁0
  have hr₂ : 0 < r₂ := polarRadius_pos ha₂0
  have hr₃ : 0 < r₃ := polarRadius_pos ha₃0
  have hrsq₁ : r₁ ^ 2 = normSq a₁ := polarRadius_sq a₁
  have hrsq₂ : r₂ ^ 2 = normSq a₂ := polarRadius_sq a₂
  have hrsq₃ : r₃ ^ 2 = normSq a₃ := polarRadius_sq a₃
  have hd₁r : d₁ * (r₁ : ℂ) = star a₁ := polarPhase_mul_radius ha₁0
  have hd₂r : d₂ * (r₂ : ℂ) = star a₂ := polarPhase_mul_radius ha₂0
  have hd₃r : d₃ * (r₃ : ℂ) = star a₃ := polarPhase_mul_radius ha₃0
  have hsd₁r : star d₁ * (r₁ : ℂ) = a₁ :=
    star_polarPhase_mul_radius ha₁0
  have hsd₂r : star d₂ * (r₂ : ℂ) = a₂ :=
    star_polarPhase_mul_radius ha₂0
  have hsd₃r : star d₃ * (r₃ : ℂ) = a₃ :=
    star_polarPhase_mul_radius ha₃0
  have hsd₁r' : (starRingEnd ℂ) d₁ * (r₁ : ℂ) = a₁ := by simpa using hsd₁r
  have hsd₂r' : (starRingEnd ℂ) d₂ * (r₂ : ℂ) = a₂ := by simpa using hsd₂r
  have hsd₃r' : (starRingEnd ℂ) d₃ * (r₃ : ℂ) = a₃ := by simpa using hsd₃r
  have hd₁ : normSq d₁ = 1 := polarPhase_normSq ha₁0
  have hd₂ : normSq d₂ = 1 := polarPhase_normSq ha₂0
  have hd₃ : normSq d₃ = 1 := polarPhase_normSq ha₃0

  have hnorm₁ : r₁ ^ 2 * (1 + n₁) = 1 := by rw [hrsq₁]; exact ha₁
  have hnorm₂ : r₂ ^ 2 * (1 + n₂) = 1 := by rw [hrsq₂]; exact ha₂
  have hnorm₃ : r₃ ^ 2 * (1 + n₃) = 1 := by rw [hrsq₃]; exact ha₃
  let q₀ : Fin 3 → ℂ := ![(r₁ : ℂ), (r₂ : ℂ), (r₃ : ℂ)]
  let u₀ : ℂ := ((r₁ * r₂ : ℝ) : ℂ) * (1 + h₁₂)
  let v₀ : ℂ := ((r₁ * r₃ : ℝ) : ℂ) * (1 + h₁₃)
  let w₀ : ℂ := ((r₂ * r₃ : ℝ) : ℂ) * (1 + h₂₃)
  have hu : star d₁ * d₂ * u₀ = a₁ * star a₂ * (1 + h₁₂) := by
    calc
      _ = (star d₁ * (r₁ : ℂ)) * (d₂ * (r₂ : ℂ)) *
          (1 + h₁₂) := by simp [u₀]; ring
      _ = a₁ * star a₂ * (1 + h₁₂) := by rw [hsd₁r, hd₂r]
  have hv : star d₁ * d₃ * v₀ = a₁ * star a₃ * (1 + h₁₃) := by
    calc
      _ = (star d₁ * (r₁ : ℂ)) * (d₃ * (r₃ : ℂ)) *
          (1 + h₁₃) := by simp [v₀]; ring
      _ = a₁ * star a₃ * (1 + h₁₃) := by rw [hsd₁r, hd₃r]
  have hw : star d₂ * d₃ * w₀ = a₂ * star a₃ * (1 + h₂₃) := by
    calc
      _ = (star d₂ * (r₂ : ℂ)) * (d₃ * (r₃ : ℂ)) *
          (1 + h₂₃) := by simp [w₀]; ring
      _ = a₂ * star a₃ * (1 + h₂₃) := by rw [hsd₂r, hd₃r]
  have hq : phaseVec d₁ d₂ d₃ q₀ = ![a₁, a₂, a₃] := by
    ext i
    fin_cases i <;>
      simp [phaseVec, Gauge.phaseVector, q₀, hsd₁r', hsd₂r', hsd₃r']
  have hphase := fourVectorGap_phase d₁ d₂ d₃ u₀ v₀ w₀ q₀ hd₁ hd₂ hd₃
  rw [hu, hv, hw, hq] at hphase
  have hbase := fourVectorGap_normalization r₁ r₂ r₃ n₁ n₂ n₃ h₁₂ h₁₃ h₂₃
    hnorm₁ hnorm₂ hnorm₃
  change fourVectorGap u₀ v₀ w₀ q₀ =
      (r₁ * r₂ * r₃) ^ 2 * geometricP n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ at hbase
  have hfactor : (r₁ * r₂ * r₃) ^ 2 = normSq (a₁ * a₂ * a₃) := by
    rw [Complex.normSq_mul, Complex.normSq_mul, ← hrsq₁, ← hrsq₂, ← hrsq₃]
    ring
  rw [hphase, hbase, hfactor]

/-- A completion with nonzero last-column coordinates gives the normalized
residual Gram matrix used by `geometricP`. -/
theorem normalizedResidual_posSemidef {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (completion u v w q))
    (hq₀ : q 0 ≠ 0) (hq₁ : q 1 ≠ 0) (hq₂ : q 2 ≠ 0) :
    IsPSD (residualGram
      ((1 - normSq (q 0)) / normSq (q 0))
      ((1 - normSq (q 1)) / normSq (q 1))
      ((1 - normSq (q 2)) / normSq (q 2))
      (u / (q 0 * star (q 1)) - 1)
      (v / (q 0 * star (q 2)) - 1)
      (w / (q 1 * star (q 2)) - 1)) := by
  have hR := completionResidual_posSemidef hA
  have hR' : IsPSD
      (Completion.residual (A4Certificate.correlation u v w) q) := by
    simpa [completionResidual, completionRankOne, Completion.residual,
      Completion.rankOne] using hR
  have hcong := Completion.normalizedResidual_posSemidef hR'
  have heq :
      Completion.normalizedResidual (A4Certificate.correlation u v w) q =
        residualGram
          ((1 - normSq (q 0)) / normSq (q 0))
          ((1 - normSq (q 1)) / normSq (q 1))
          ((1 - normSq (q 2)) / normSq (q 2))
          (u / (q 0 * star (q 1)) - 1)
          (v / (q 0 * star (q 2)) - 1)
          (w / (q 1 * star (q 2)) - 1) := by
    have hq : ∀ i, q i ≠ 0 := by
      intro i
      fin_cases i <;> assumption
    ext i j
    rw [Completion.normalizedResidual_apply _ _ _ _ (hq i) (hq j)]
    fin_cases i <;> fin_cases j <;>
      simp [correlation, residualGram,
        Complex.normSq_eq_conj_mul_self] <;>
      ring_nf <;>
      field_simp [hq₀, hq₁, hq₂]
  rw [← heq]
  exact hcong

/-- The four-vector gap is nonnegative for PSD completions whose three
last-column coordinates are nonzero. -/
theorem fourVectorGap_nonneg_of_completion_nonzero
    {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (completion u v w q))
    (hq₀ : q 0 ≠ 0) (hq₁ : q 1 ≠ 0) (hq₂ : q 2 ≠ 0) :
    0 ≤ fourVectorGap u v w q := by
  let n₁ : ℝ := (1 - normSq (q 0)) / normSq (q 0)
  let n₂ : ℝ := (1 - normSq (q 1)) / normSq (q 1)
  let n₃ : ℝ := (1 - normSq (q 2)) / normSq (q 2)
  let h₁₂ : ℂ := u / (q 0 * star (q 1)) - 1
  let h₁₃ : ℂ := v / (q 0 * star (q 2)) - 1
  let h₂₃ : ℂ := w / (q 1 * star (q 2)) - 1
  have hnq₀ : normSq (q 0) ≠ 0 := mt normSq_eq_zero.mp hq₀
  have hnq₁ : normSq (q 1) ≠ 0 := mt normSq_eq_zero.mp hq₁
  have hnq₂ : normSq (q 2) ≠ 0 := mt normSq_eq_zero.mp hq₂
  have hn₁ : normSq (q 0) * (1 + n₁) = 1 := by
    dsimp [n₁]
    field_simp [hnq₀]
  have hn₂ : normSq (q 1) * (1 + n₂) = 1 := by
    dsimp [n₂]
    field_simp [hnq₁]
  have hn₃ : normSq (q 2) * (1 + n₃) = 1 := by
    dsimp [n₃]
    field_simp [hnq₂]
  have hu : q 0 * star (q 1) * (1 + h₁₂) = u := by
    dsimp [h₁₂]
    field_simp [hq₀, hq₁]
  have hv : q 0 * star (q 2) * (1 + h₁₃) = v := by
    dsimp [h₁₃]
    field_simp [hq₀, hq₂]
  have hw : q 1 * star (q 2) * (1 + h₂₃) = w := by
    dsimp [h₂₃]
    field_simp [hq₁, hq₂]
  have hq : ![q 0, q 1, q 2] = q := by
    funext i
    fin_cases i <;> rfl
  have hbridge := fourVectorGap_complex_normalization
    (q 0) (q 1) (q 2) n₁ n₂ n₃ h₁₂ h₁₃ h₂₃ hn₁ hn₂ hn₃
  rw [hu, hv, hw, hq] at hbridge
  have hR : IsPSD (residualGram n₁ n₂ n₃ h₁₂ h₁₃ h₂₃) := by
    exact normalizedResidual_posSemidef hA hq₀ hq₁ hq₂
  have hP := geometricP_nonneg_of_posSemidef hR
  rw [hbridge]
  exact mul_nonneg (normSq_nonneg _) hP

theorem phaseCompletion_posSemidef (p : Fin 3 → ℂ)
    (hp : ∀ i, normSq (p i) = 1) :
    IsPSD (completion
      (p 0 * star (p 1)) (p 0 * star (p 2)) (p 1 * star (p 2)) p) := by
  apply completion_posSemidef_of_block
  have hpunit : ∀ i, p i * (starRingEnd ℂ) (p i) = 1 := fun i => by
    simpa [mul_comm] using unit_mul (p i) (hp i)
  have hpunit' : ∀ i, 1 = p i * (starRingEnd ℂ) (p i) := fun i => by
    simpa only [starRingEnd_apply] using (hpunit i).symm
  have hB :
      A4Certificate.correlation
          (p 0 * star (p 1)) (p 0 * star (p 2)) (p 1 * star (p 2)) =
        Completion.rankOne p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A4Certificate.correlation, Completion.rankOne,
        Complex.normSq_eq_conj_mul_self, mul_comm] <;>
      exact hpunit' _
  rw [hB]
  exact Completion.rankOne_fromBlocks_posSemidef p

def perturbQ (q : Fin 3 → ℂ) (t : ℝ) : Fin 3 → ℂ :=
  perturbVector q t

def perturbU (u : ℂ) (q : Fin 3 → ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * u +
    (t : ℂ) * (perturbPhase (q 0) * star (perturbPhase (q 1)))

def perturbV (v : ℂ) (q : Fin 3 → ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * v +
    (t : ℂ) * (perturbPhase (q 0) * star (perturbPhase (q 2)))

def perturbW (w : ℂ) (q : Fin 3 → ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * w +
    (t : ℂ) * (perturbPhase (q 1) * star (perturbPhase (q 2)))

theorem perturb_completion_posSemidef
    {u v w : ℂ} {q : Fin 3 → ℂ} (hA : IsPSD (completion u v w q))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsPSD (completion (perturbU u q t) (perturbV v q t) (perturbW w q t)
      (perturbQ q t)) := by
  let p : Fin 3 → ℂ := fun i => perturbPhase (q i)
  have hpunit : ∀ i, p i * (starRingEnd ℂ) (p i) = 1 := fun i => by
    simpa [mul_comm] using unit_mul (p i) (normSq_perturbPhase (q i))
  have hpunit' : ∀ i, 1 = p i * (starRingEnd ℂ) (p i) := fun i => by
    simpa only [starRingEnd_apply] using (hpunit i).symm
  have hphaseunit : ∀ i,
      1 = perturbPhase (q i) * (starRingEnd ℂ) (perturbPhase (q i)) :=
    fun i => by simpa [p] using hpunit' i
  apply completion_posSemidef_of_block
  have hconvex := Completion.convex_rankOne_fromBlocks_posSemidef
    (completionBlock_posSemidef hA) p ht₀ ht₁
  have hB :
      A4Certificate.correlation
          (perturbU u q t) (perturbV v q t) (perturbW w q t) =
        ((1 - t : ℝ) : ℂ) • A4Certificate.correlation u v w +
          (t : ℂ) • Completion.rankOne p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [perturbU, perturbV, perturbW, p, A4Certificate.correlation,
        Completion.rankOne, map_add, map_mul]
    all_goals try { rw [← hphaseunit _]; ring }
    all_goals exact Or.inl (mul_comm _ _)
  let q' : Fin 3 → ℂ := fun i =>
    (((1 - t : ℝ) : ℂ) * q i + (t : ℂ) * p i)
  have hq' : perturbQ q t = q' := by
    rfl
  rw [hB]
  rw [hq']
  simpa [q', p] using hconvex

theorem perturbQ_ne_zero (q : Fin 3 → ℂ) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (i : Fin 3) :
    perturbQ q t i ≠ 0 :=
  Gauge.perturbVector_ne_zero q ht₀ ht₁ i

def perturbGap (u v w : ℂ) (q : Fin 3 → ℂ) (t : ℝ) : ℝ :=
  fourVectorGap (perturbU u q t) (perturbV v q t) (perturbW w q t)
    (perturbQ q t)

theorem perturbGap_tendsto (u v w : ℂ) (q : Fin 3 → ℂ) :
    Tendsto (perturbGap u v w q) (nhds 0) (nhds (fourVectorGap u v w q)) := by
  have hcont : Continuous (perturbGap u v w q) := by
    unfold perturbGap perturbU perturbV perturbW perturbQ
    unfold Gauge.perturbVector
    fun_prop
  have hQzero : perturbQ q 0 = q := by
    funext i
    simp [perturbQ, Gauge.perturbVector]
  have hzero : perturbGap u v w q 0 = fourVectorGap u v w q := by
    simp [perturbGap, perturbU, perturbV, perturbW, hQzero]
  rw [← hzero]
  exact hcont.continuousAt

/-- Positivity for every PSD completion, including zero last-column
coordinates, by a PSD rank-one perturbation and closure. -/
theorem fourVectorGap_nonneg_of_completion
    {u v w : ℂ} {q : Fin 3 → ℂ}
    (hA : IsPSD (completion u v w q)) :
    0 ≤ fourVectorGap u v w q := by
  have hlim : Tendsto
      (fun n : ℕ => perturbGap u v w q (1 / ((n : ℝ) + 1))) atTop
      (nhds (fourVectorGap u v w q)) :=
    (perturbGap_tendsto u v w q).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply ge_of_tendsto hlim
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht₀ : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
  have ht₁ : (1 / ((n : ℝ) + 1) : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith
  have hAt := perturb_completion_posSemidef hA ht₀.le ht₁.le
  have hq₀ := perturbQ_ne_zero q ht₀ ht₁ (0 : Fin 3)
  have hq₁ := perturbQ_ne_zero q ht₀ ht₁ (1 : Fin 3)
  have hq₂ := perturbQ_ne_zero q ht₀ ht₁ (2 : Fin 3)
  have hgap := fourVectorGap_nonneg_of_completion_nonzero hAt hq₀ hq₁ hq₂
  simpa [perturbGap] using hgap

/-- The geometric argument establishes the complete four-vector property. -/
theorem fourVectorProperty (u v w : ℂ) : FourVectorProperty u v w := by
  intro q hA
  exact fourVectorGap_nonneg_of_completion hA

end PermanentalDominance.N4.A4GeometricFourVector
