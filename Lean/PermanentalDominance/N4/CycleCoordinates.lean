import PermanentalDominance.N4.CorrelationReduction
import PermanentalDominance.N4.ScalarAggregates

/-!
# Cycle aggregates in six edge coordinates
-/

noncomputable section

open Complex

namespace PermanentalDominance.N4.CycleCoordinates

def T (a b c d e f : ℂ) : ℝ :=
  normSq a + normSq b + normSq c + normSq d + normSq e + normSq f

def D (a b c d e f : ℂ) : ℝ :=
  normSq a * normSq f + normSq b * normSq e + normSq c * normSq d

def C (a b c d e f : ℂ) : ℝ :=
  2 * ((a * d * star b).re + (a * e * star c).re +
    (b * f * star c).re + (d * f * star e).re)

def F (a b c d e f : ℂ) : ℝ :=
  2 * ((a * d * f * star c).re + (a * e * star f * star b).re +
    (b * star d * e * star c).re)

theorem T_nonneg (a b c d e f : ℂ) : 0 ≤ T a b c d e f := by
  simp only [T]
  nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b,
    Complex.normSq_nonneg c, Complex.normSq_nonneg d,
    Complex.normSq_nonneg e, Complex.normSq_nonneg f]

theorem D_nonneg (a b c d e f : ℂ) : 0 ≤ D a b c d e f := by
  simp only [D]
  exact add_nonneg (add_nonneg
    (mul_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg f))
    (mul_nonneg (Complex.normSq_nonneg b) (Complex.normSq_nonneg e)))
    (mul_nonneg (Complex.normSq_nonneg c) (Complex.normSq_nonneg d))

/-- The opposite-edge products obey the coarse AM--GM estimate used by the
`[22]` row. -/
theorem D_le_T_sq_div_four (a b c d e f : ℂ) :
    D a b c d e f ≤ T a b c d e f ^ 2 / 4 := by
  have ha := Complex.normSq_nonneg a
  have hb := Complex.normSq_nonneg b
  have hc := Complex.normSq_nonneg c
  have hd := Complex.normSq_nonneg d
  have he := Complex.normSq_nonneg e
  have hf := Complex.normSq_nonneg f
  simp only [T, D]
  nlinarith [sq_nonneg (normSq a - normSq f),
    sq_nonneg (normSq b - normSq e), sq_nonneg (normSq c - normSq d),
    mul_nonneg (add_nonneg ha hf) (add_nonneg hb he),
    mul_nonneg (add_nonneg ha hf) (add_nonneg hc hd),
    mul_nonneg (add_nonneg hb he) (add_nonneg hc hd)]

private theorem two_re_mul_lower (x y : ℂ) :
    -(normSq x + normSq y) ≤ 2 * (x * y).re := by
  have h := Complex.normSq_nonneg (x + star y)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re]
    at h ⊢
  nlinarith

private theorem two_re_mul_upper (x y : ℂ) :
    2 * (x * y).re ≤ normSq x + normSq y := by
  have h := Complex.normSq_nonneg (x - star y)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re]
    at h ⊢
  nlinarith

/-- Pair the three four-cycles by the three opposite-edge products. -/
theorem F_lower (a b c d e f : ℂ) :
    -2 * D a b c d e f ≤ F a b c d e f := by
  have h₁ := two_re_mul_lower (a * f) (d * star c)
  have h₂ := two_re_mul_lower (a * star f) (e * star b)
  have h₃ := two_re_mul_lower (b * e) (star d * star c)
  have heq₁ : ((a * f) * (d * star c)).re = (a * d * f * star c).re := by
    congr 1
    ring
  have heq₂ : ((a * star f) * (e * star b)).re =
      (a * e * star f * star b).re := by
    congr 1
    ring
  have heq₃ : ((b * e) * (star d * star c)).re =
      (b * star d * e * star c).re := by
    congr 1
    ring
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  rw [heq₃] at h₃
  simp only [Complex.star_def, Complex.normSq_mul, Complex.normSq_conj] at h₁ h₂ h₃
  calc
    -2 * D a b c d e f =
        -(normSq a * normSq f + normSq d * normSq c) +
        -(normSq a * normSq f + normSq e * normSq b) +
        -(normSq b * normSq e + normSq d * normSq c) := by simp [D]; ring
    _ ≤ 2 * (a * d * f * star c).re +
        2 * (a * e * star f * star b).re +
        2 * (b * star d * e * star c).re :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = F a b c d e f := by simp [F]; ring

theorem F_upper_two_D (a b c d e f : ℂ) :
    F a b c d e f ≤ 2 * D a b c d e f := by
  have h₁ := two_re_mul_upper (a * f) (d * star c)
  have h₂ := two_re_mul_upper (a * star f) (e * star b)
  have h₃ := two_re_mul_upper (b * e) (star d * star c)
  have heq₁ : ((a * f) * (d * star c)).re = (a * d * f * star c).re := by
    congr 1
    ring
  have heq₂ : ((a * star f) * (e * star b)).re =
      (a * e * star f * star b).re := by
    congr 1
    ring
  have heq₃ : ((b * e) * (star d * star c)).re =
      (b * star d * e * star c).re := by
    congr 1
    ring
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  rw [heq₃] at h₃
  simp only [Complex.star_def, Complex.normSq_mul, Complex.normSq_conj] at h₁ h₂ h₃
  calc
    F a b c d e f = 2 * (a * d * f * star c).re +
        2 * (a * e * star f * star b).re +
        2 * (b * star d * e * star c).re := by simp [F]; ring
    _ ≤ (normSq a * normSq f + normSq d * normSq c) +
        (normSq a * normSq f + normSq e * normSq b) +
        (normSq b * normSq e + normSq d * normSq c) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = 2 * D a b c d e f := by simp [D]; ring

theorem two_D_le_T_of_edges_le_one {a b c d e f : ℂ}
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1)
    (hd : normSq d ≤ 1) (he : normSq e ≤ 1) (hf : normSq f ≤ 1) :
    2 * D a b c d e f ≤ T a b c d e f := by
  have ha0 := Complex.normSq_nonneg a
  have hb0 := Complex.normSq_nonneg b
  have hc0 := Complex.normSq_nonneg c
  have hd0 := Complex.normSq_nonneg d
  have he0 := Complex.normSq_nonneg e
  have hf0 := Complex.normSq_nonneg f
  simp only [T, D]
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hf),
    mul_nonneg hf0 (sub_nonneg.mpr ha),
    mul_nonneg hb0 (sub_nonneg.mpr he),
    mul_nonneg he0 (sub_nonneg.mpr hb),
    mul_nonneg hc0 (sub_nonneg.mpr hd),
    mul_nonneg hd0 (sub_nonneg.mpr hc)]

theorem F_le_T_of_correlation {a b c d e f : ℂ}
    (hA : IsPSD (CorrelationReduction.correlation a b c d e f)) :
    F a b c d e f ≤ T a b c d e f :=
  (F_upper_two_D a b c d e f).trans <|
    two_D_le_T_of_edges_le_one
      (CorrelationReduction.normSq_a_le_one hA)
      (CorrelationReduction.normSq_b_le_one hA)
      (CorrelationReduction.normSq_c_le_one hA)
      (CorrelationReduction.normSq_d_le_one hA)
      (CorrelationReduction.normSq_e_le_one hA)
      (CorrelationReduction.normSq_f_le_one hA)

end PermanentalDominance.N4.CycleCoordinates
