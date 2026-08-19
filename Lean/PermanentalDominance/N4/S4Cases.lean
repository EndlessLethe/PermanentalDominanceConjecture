import PermanentalDominance.N4.SpectralThreeCycle

/-!
# Scalar certificates for the five `S₄` rows

The hypotheses here are exactly the analytic inequalities supplied by the
Fischer/spectral modules.  Separating this final arithmetic step makes it
possible to audit that no character row is lost in the table dispatch.
-/

namespace PermanentalDominance.N4.S4Cases

open ScalarAggregates

theorem trivial (T D C F : ℝ) :
    permanentForm T D C F ≤ permanentForm T D C F := le_rfl

/-- The sign row follows from `T + F ≥ 0`, equivalently `per ≥ det`. -/
theorem sign {T D C F : ℝ} (hTF : 0 ≤ T + F) :
    determinantForm T D C F ≤ permanentForm T D C F := by
  rw [← sub_nonneg]
  rw [permanent_sub_determinant]
  positivity

theorem sign_of_four_lower {T D C F : ℝ} (hfour : -2 * D ≤ F)
    (htwoD : 2 * D ≤ T) :
    determinantForm T D C F ≤ permanentForm T D C F := by
  apply sign
  linarith

theorem diagonal_le_permanent {T D C F : ℝ} (hT : 0 ≤ T)
    (hspectral : T ^ 2 / 2 ≤ T + 3 * C / 2)
    (hdouble : D ≤ T ^ 2 / 4) (hfour : -2 * D ≤ F) :
    1 ≤ permanentForm T D C F := by
  simp only [permanentForm]
  nlinarith

/-- For `[31]`, the input is the sum of the four principal-three Fischer
inequalities: `4 + 2T + C ≤ 4 per`. -/
theorem standard31 {T D C F : ℝ}
    (hprincipal : 4 + 2 * T + C ≤ 4 * permanentForm T D C F) :
    s4Standard31 T D C F ≤ permanentForm T D C F := by
  simp only [permanentForm, s4Standard31] at hprincipal ⊢
  linarith

theorem standard31_of_spectral {T D C F : ℝ}
    (hspectral : T ^ 2 / 2 ≤ T + 3 * C / 2)
    (hdouble : D ≤ T ^ 2 / 4) (hfour : -2 * D ≤ F) :
    s4Standard31 T D C F ≤ permanentForm T D C F := by
  apply standard31
  simp only [permanentForm]
  nlinarith

/-- The `[22]` certificate.  The three inputs are respectively the spectral
three-cycle estimate, the opposite-edge AM--GM estimate, and the elementary
four-cycle lower bound. -/
theorem standard22 {T D C F : ℝ}
    (hspectral : T ^ 2 / 2 ≤ T + 3 * C / 2)
    (hdouble : D ≤ T ^ 2 / 4) (hfour : -2 * D ≤ F) :
    s4Standard22 T D C F ≤ permanentForm T D C F := by
  simp only [permanentForm, s4Standard22]
  nlinarith

/-- The `[211]` row is at most one once `F ≤ T`; diagonal permanent
dominance then finishes it. -/
theorem standard211 {T D C F : ℝ} (hD : 0 ≤ D) (hfour : F ≤ T)
    (hdiag : 1 ≤ permanentForm T D C F) :
    s4Standard211 T D C F ≤ permanentForm T D C F := by
  have hrow : s4Standard211 T D C F ≤ 1 := by
    simp only [s4Standard211]
    linarith
  exact hrow.trans hdiag

open CycleCoordinates CorrelationReduction

private theorem correlation_inputs {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    let t := T a b c d e f
    let d₂ := D a b c d e f
    let c₃ := C a b c d e f
    let f₄ := F a b c d e f
    0 ≤ t ∧ 0 ≤ d₂ ∧ d₂ ≤ t ^ 2 / 4 ∧ -2 * d₂ ≤ f₄ ∧
      2 * d₂ ≤ t ∧ f₄ ≤ t ∧ t ^ 2 / 2 ≤ t + 3 * c₃ / 2 := by
  dsimp
  exact ⟨T_nonneg _ _ _ _ _ _, D_nonneg _ _ _ _ _ _,
    D_le_T_sq_div_four _ _ _ _ _ _, F_lower _ _ _ _ _ _,
    two_D_le_T_of_edges_le_one
      (normSq_a_le_one hA) (normSq_b_le_one hA) (normSq_c_le_one hA)
      (normSq_d_le_one hA) (normSq_e_le_one hA) (normSq_f_le_one hA),
    F_le_T_of_correlation hA, SpectralThreeCycle.correlation_spectral_bound hA⟩

theorem correlation_permanent_ge_one {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    1 ≤ permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) := by
  rcases correlation_inputs hA with ⟨hT, _, hD, hF, _, _, hS⟩
  exact diagonal_le_permanent hT hS hD hF

theorem correlation_sign {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    determinantForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) ≤
    permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) := by
  rcases correlation_inputs hA with ⟨_, _, _, hF, h2D, _, _⟩
  exact sign_of_four_lower hF h2D

theorem correlation_standard31 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    s4Standard31 (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) ≤
    permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) := by
  rcases correlation_inputs hA with ⟨_, _, hD, hF, _, _, hS⟩
  exact standard31_of_spectral hS hD hF

theorem correlation_standard22 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    s4Standard22 (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) ≤
    permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) := by
  rcases correlation_inputs hA with ⟨_, _, hD, hF, _, _, hS⟩
  exact standard22 hS hD hF

theorem correlation_standard211 {a b c d e f : ℂ}
    (hA : IsPSD (correlation a b c d e f)) :
    s4Standard211 (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) ≤
    permanentForm (T a b c d e f) (D a b c d e f)
      (C a b c d e f) (F a b c d e f) := by
  rcases correlation_inputs hA with ⟨_, hD0, _, _, _, hF, _⟩
  exact standard211 hD0 hF (correlation_permanent_ge_one hA)

end PermanentalDominance.N4.S4Cases
