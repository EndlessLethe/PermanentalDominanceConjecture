import PermanentalDominance.N4.A4GeometricGeneral
import PermanentalDominance.GramExtension
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.StarOrdered

/-!
# Exact Gram certificates from the geometric A₄ proof

The old proof reduces the only difficult coefficient of the minimum numerator
to three real polynomial inequalities.  The two quartic inequalities are
proved by direct square completion.  For the coupled sextic, its leading radial
square is removed first, leaving one exact rational `6 × 6` Gram certificate.

The remaining LDLᵀ data are private implementation details.  Its `L` matrix is
unit lower triangular, so the proof uses only exact rational identities and no
numerical eigenvalue argument.
-/

noncomputable section

open Matrix

namespace PermanentalDominance.N4.A4GeometricGram

open PermanentalDominance.GramExtension

private def realMatrix {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) : Matrix n n ℝ :=
  (Rat.castHom ℝ).mapMatrix A

private theorem realMatrix_posDef_of_ldl
    {n : Type} [Fintype n] [DecidableEq n]
    (K L : Matrix n n ℚ) (d : n → ℚ)
    (hldl : K = L * diagonal d * L.transpose)
    (hdet : L.det = 1)
    (hd : ∀ i, 0 < (d i : ℝ)) :
    (realMatrix K).PosDef := by
  let LR : Matrix n n ℝ := realMatrix L
  let dR : n → ℝ := fun i => (d i : ℝ)
  have hdetR : LR.det = 1 := by
    have hm := RingHom.map_det (Rat.castHom ℝ) L
    simpa [LR, realMatrix, hdet] using hm.symm
  have hunit : IsUnit LR :=
    (Matrix.isUnit_iff_isUnit_det LR).2 (by simp [hdetR])
  have hinj : Function.Injective LR.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hunit
  have hdiag : (diagonal dR).PosDef :=
    Matrix.PosDef.diagonal hd
  have hcongr := hdiag.mul_mul_conjTranspose_same hinj
  have hfactor :
      realMatrix K = LR * diagonal dR * LR.transpose := by
    dsimp [LR, dR, realMatrix]
    rw [hldl]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hfactor]
  simpa [Matrix.conjTranspose] using hcongr

/-! ## Direct square completions for B₂ and B₃ + 252 -/

/-- The manuscript's quartic B₂, in the rational coordinates
X = r, Y = sqrt 3 * s. -/
def coefficientTwo (X Y : ℝ) : ℝ :=
  432 + 624 * X - 240 * Y + 492 * X ^ 2 + 108 * Y ^ 2 - 168 * X * Y +
    (156 * X - 84 * Y) * (X ^ 2 + Y ^ 2 / 3) +
    38 * (X ^ 2 + Y ^ 2 / 3) ^ 2

private theorem coefficientTwo_sos (X Y : ℝ) :
    coefficientTwo X Y =
      38 * (X ^ 2 + Y ^ 2 / 3 + (39 / 19) * X - (21 / 19) * Y + 3 / 2) ^ 2 +
      (448 / 19) * (Y + (3 / 32) * X - 1083 / 448) ^ 2 +
      (3483 / 16) * (X + 2137 / 2322) ^ 2 +
      131797 / 5418 := by
  unfold coefficientTwo
  ring

/-- Exact strict positivity of the old B₂ coefficient. -/
theorem coefficientTwo_pos (X Y : ℝ) : 0 < coefficientTwo X Y := by
  rw [coefficientTwo_sos]
  positivity

/-- The manuscript's quartic B₃, in rational (X,Y) coordinates. -/
def coefficientThree (X Y : ℝ) : ℝ :=
  168 + 72 * X - 168 * Y + 54 * X ^ 2 + 46 * Y ^ 2 - 84 * X * Y +
    (20 * X - 24 * Y) * (X ^ 2 + Y ^ 2 / 3) +
    6 * (X ^ 2 + Y ^ 2 / 3) ^ 2

private theorem coefficientThree_add_sos (X Y : ℝ) :
    coefficientThree X Y + 252 =
      6 * (X ^ 2 + Y ^ 2 / 3 + (5 / 3) * X - 2 * Y - 1 / 2) ^ 2 +
      24 * (Y - (11 / 12) * X - 15 / 4) ^ 2 +
      (139 / 6) * (X - 249 / 139) ^ 2 +
      1851 / 278 := by
  unfold coefficientThree
  ring

/-- Exact strict positivity of B₃ + 252. -/
theorem coefficientThree_add_pos (X Y : ℝ) :
    0 < coefficientThree X Y + 252 := by
  rw [coefficientThree_add_sos]
  positivity

/-! ## The coupled Sigma certificate -/

/-- The old coefficient B₄, again in rational (X,Y) coordinates. -/
def coefficientFour (X Y : ℝ) : ℝ :=
  60 + 24 * X - 24 * Y + 14 * (X ^ 2 + Y ^ 2 / 3)

/-- The coupled polynomial which controls the negative-B₃ case. -/
def coupledSigma (X Y : ℝ) : ℝ :=
  4 * coefficientTwo X Y * coefficientFour X Y +
    252 * coefficientThree X Y

private def sigmaRemainderQ : Matrix (Fin 6) (Fin 6) ℚ := !![
  8739057600, -4231634400, 478800000, 6265576800, -1795500000, 47880000;
  -4231634400, 2519799114, -385003080, -2526627600, 807975000, 239400000;
  478800000, -385003080, 79782560, 281630160, -81252000, -35910000;
  6265576800, -2526627600, 281630160, 10931106942, -2359670040, 2303554680;
  -1795500000, 807975000, -81252000, -2359670040, 685371360, -243756000;
  47880000, 239400000, -35910000, 2303554680, -243756000, 1122611040]

private def sigmaRemainderLQ : Matrix (Fin 6) (Fin 6) ℚ := !![
  1, 0, 0, 0, 0, 0;
  (-491 / 1014), 1, 0, 0, 0, 0;
  (250 / 4563), (-32435740 / 99695867), 1, 0, 0, 0;
  (727 / 1014), (107434800 / 99695867),
    (386554179222477 / 13908710622512), 1, 0, 0;
  (-625 / 3042), (-13012500 / 99695867),
    (-2682176146725 / 3477177655628),
    (-672773442101882740 / 2192229913808106817), 1, 0;
  (25 / 4563), (55610000 / 99695867),
    (175331786181125 / 13908710622512),
    (495915200689391455 / 2192229913808106817),
    (22159801298530914084895 / 10547120712337618624667), 1]

private def sigmaRemainderDQ : Fin 6 → ℚ := ![
  8739057600,
  (79557301866 / 169),
  (1112696849800960 / 299087601),
  (2624099206828303859949 / 869294413907),
  (2531308970961028469920080 / 115380521779374043),
  (1406694633431943161674826341030 / 10547120712337618624667)
]

set_option maxHeartbeats 2000000 in
private theorem sigmaRemainder_ldl :
    sigmaRemainderQ = sigmaRemainderLQ * diagonal sigmaRemainderDQ *
      sigmaRemainderLQ.transpose := by
  native_decide

private theorem sigmaRemainder_lower :
    sigmaRemainderLQ.BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  fin_cases i <;> fin_cases j <;>
    norm_num [sigmaRemainderLQ] at hij ⊢

private theorem sigmaRemainder_det : sigmaRemainderLQ.det = 1 := by
  rw [Matrix.det_of_lowerTriangular sigmaRemainderLQ sigmaRemainder_lower]
  native_decide

private theorem sigmaRemainder_d_pos (i : Fin 6) :
    0 < (sigmaRemainderDQ i : ℝ) := by
  fin_cases i <;> norm_num [sigmaRemainderDQ]

private theorem sigmaRemainder_posDef :
    (realMatrix sigmaRemainderQ).PosDef :=
  realMatrix_posDef_of_ldl sigmaRemainderQ sigmaRemainderLQ sigmaRemainderDQ
    sigmaRemainder_ldl sigmaRemainder_det sigmaRemainder_d_pos

/-- Monomials for the quartic remainder after removing the radial square. -/
private def sigmaRemainderMonomial (X Y : ℝ) : Fin 6 → ℝ :=
  ![1, Y, Y ^ 2, X, X * Y, X ^ 2]

set_option maxHeartbeats 4000000 in
private theorem coupledSigma_split (X Y : ℝ) :
    coupledSigma X Y =
      2128 * (X ^ 2 + Y ^ 2 / 3) *
        (X ^ 2 + Y ^ 2 / 3 + (387 / 133) * X -
          (261 / 133) * Y + 77 / 20) ^ 2 +
      (1 / 59850 : ℝ) *
        (sigmaRemainderMonomial X Y ⬝ᵥ
          (realMatrix sigmaRemainderQ).mulVec (sigmaRemainderMonomial X Y)) := by
  simp [coupledSigma, coefficientTwo, coefficientThree, coefficientFour,
    sigmaRemainderMonomial, realMatrix, sigmaRemainderQ, dotProduct, Matrix.mulVec,
    Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- Exact strict positivity of the coupled old Gram polynomial Sigma. -/
theorem coupledSigma_pos (X Y : ℝ) : 0 < coupledSigma X Y := by
  have hm : sigmaRemainderMonomial X Y ≠ 0 := by
    intro h
    have hfirst := congrFun h (0 : Fin 6)
    change (1 : ℝ) = 0 at hfirst
    norm_num at hfirst
  have hq := sigmaRemainder_posDef.2 (sigmaRemainderMonomial X Y) hm
  have hq' : 0 <
      sigmaRemainderMonomial X Y ⬝ᵥ
        (realMatrix sigmaRemainderQ).mulVec (sigmaRemainderMonomial X Y) := by
    simpa using hq
  rw [coupledSigma_split]
  have hradial :
      0 ≤ 2128 * (X ^ 2 + Y ^ 2 / 3) *
        (X ^ 2 + Y ^ 2 / 3 + (387 / 133) * X -
          (261 / 133) * Y + 77 / 20) ^ 2 := by
    positivity
  have hremainder : 0 < (1 / 59850 : ℝ) *
      (sigmaRemainderMonomial X Y ⬝ᵥ
        (realMatrix sigmaRemainderQ).mulVec (sigmaRemainderMonomial X Y)) := by
    positivity
  linarith

/-- The difficult discriminant is positive on the only region where it is
needed.  This exposes the old constant `252` as the parameter of a
one-multiplier conditional SOS certificate, not as part of the target
inequality. -/
private theorem middleDiscriminant_pos_of_negative
    (X Y : ℝ) (hnegative : coefficientThree X Y < 0) :
    0 < 4 * coefficientTwo X Y * coefficientFour X Y -
      coefficientThree X Y ^ 2 := by
  apply discriminant_pos_of_shift_certificate (C := 252)
  · simpa [coupledSigma] using coupledSigma_pos X Y
  · exact coefficientThree_add_pos X Y
  · exact hnegative

/-! ## Assembly of the old N₁ coefficient -/

/-- The old B₁ coefficient in rational (X,Y) coordinates. -/
def coefficientOne (X Y : ℝ) : ℝ :=
  (X ^ 2 + Y ^ 2 / 3) *
    (240 + 168 * X - 72 * Y + 54 * (X ^ 2 + Y ^ 2 / 3))

theorem coefficientOne_lower (X Y : ℝ) :
    (112 / 3 : ℝ) * (X ^ 2 + Y ^ 2 / 3) ≤ coefficientOne X Y := by
  have hnu : 0 ≤ X ^ 2 + Y ^ 2 / 3 := by positivity
  have hsquareX := sq_nonneg (9 * X + 14)
  have hsquareY := sq_nonneg (Y - 2)
  have hbracket :
      (112 / 3 : ℝ) ≤
        240 + 168 * X - 72 * Y + 54 * (X ^ 2 + Y ^ 2 / 3) := by
    nlinarith
  simpa [coefficientOne, mul_comm] using
    (mul_le_mul_of_nonneg_left hbracket hnu)

theorem coefficientOne_nonneg (X Y : ℝ) :
    0 ≤ coefficientOne X Y := by
  have hnu : 0 ≤ X ^ 2 + Y ^ 2 / 3 := by positivity
  have hlower := coefficientOne_lower X Y
  nlinarith

theorem coefficientFour_lower (X Y : ℝ) :
    (132 / 7 : ℝ) ≤ coefficientFour X Y := by
  have hsquareX := sq_nonneg (7 * X + 6)
  have hsquareY := sq_nonneg (7 * Y - 18)
  dsimp [coefficientFour]
  nlinarith

theorem coefficientFour_pos (X Y : ℝ) :
    0 < coefficientFour X Y := by
  have hlower := coefficientFour_lower X Y
  norm_num at hlower ⊢
  linarith

/-- Positivity of the three middle coefficients after regrouping.  The
negative-middle-coefficient branch is discharged by the conditional SOS
certificate above. -/
theorem middleCombination_pos {a : ℝ} (ha : 0 < a) (X Y : ℝ) :
    0 < coefficientTwo X Y +
      a * coefficientThree X Y + a ^ 2 * coefficientFour X Y := by
  have h2 := coefficientTwo_pos X Y
  have h4 := coefficientFour_pos X Y
  by_cases h3 : 0 ≤ coefficientThree X Y
  · have ha3 : 0 ≤ a * coefficientThree X Y :=
      mul_nonneg ha.le h3
    have ha24 : 0 < a ^ 2 * coefficientFour X Y :=
      mul_pos (sq_pos_of_pos ha) h4
    linarith
  · have h3neg : coefficientThree X Y < 0 := lt_of_not_ge h3
    have hdisc := middleDiscriminant_pos_of_negative X Y h3neg
    have hid :
        4 * coefficientFour X Y *
            (coefficientTwo X Y + a * coefficientThree X Y +
              a ^ 2 * coefficientFour X Y) =
          (2 * coefficientFour X Y * a + coefficientThree X Y) ^ 2 +
            (4 * coefficientTwo X Y * coefficientFour X Y -
              coefficientThree X Y ^ 2) := by ring
    have hscaled :
        0 < 4 * coefficientFour X Y *
          (coefficientTwo X Y + a * coefficientThree X Y +
            a ^ 2 * coefficientFour X Y) := by
      rw [hid]
      positivity
    nlinarith

/-- The full coefficient N₁ of the old minimum-numerator expansion. -/
def minimumLinearCoeff (a X Y : ℝ) : ℝ :=
  36 * (X ^ 2 + Y ^ 2 / 3) ^ 2 +
    a * coefficientOne X Y +
    a ^ 2 * coefficientTwo X Y +
    a ^ 3 * coefficientThree X Y +
    a ^ 4 * coefficientFour X Y +
    6 * a ^ 5

theorem minimumLinearCoeff_pos {a : ℝ} (ha : 0 < a) (X Y : ℝ) :
    0 < minimumLinearCoeff a X Y := by
  have hnu : 0 ≤ 36 * (X ^ 2 + Y ^ 2 / 3) ^ 2 := by positivity
  have h1 : 0 ≤ a * coefficientOne X Y :=
    mul_nonneg ha.le (coefficientOne_nonneg X Y)
  have hmiddle := middleCombination_pos ha X Y
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hmiddleScaled :
      0 < a ^ 2 *
        (coefficientTwo X Y + a * coefficientThree X Y +
          a ^ 2 * coefficientFour X Y) :=
    mul_pos ha2 hmiddle
  have h5 : 0 < 6 * a ^ 5 := by positivity
  dsimp [minimumLinearCoeff]
  nlinarith

end PermanentalDominance.N4.A4GeometricGram
