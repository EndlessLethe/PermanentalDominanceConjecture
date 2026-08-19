import PermanentalDominance.N4.A4Registry
import PermanentalDominance.N4.RegisteredCompleteness

/-!
# Realization and completeness of the `A₄` character table

The two primitive-root rows are realized by homomorphisms through the
quotient `A₄/V₄ ≅ C₃`.  The last row is the standard three-dimensional
summand of the permutation representation on four letters.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace PermanentalDominance.N4

local instance : Fintype (representative .a4) := Fintype.ofFinite _

open PermutationEnumeration

/-! ## The two non-real linear characters -/

private def a4CharacterIndex (sigma : S4) : Fin 3 :=
  if sigma ∈ representativeCarrier .v4Normal then 0
  else if sigma ∈ A4Gap.a4PositiveClass then 1 else 2

private def a4AddIndex : Fin 3 → Fin 3 → Fin 3
  | 0, j => j
  | 1, 0 => 1
  | 1, 1 => 2
  | 1, 2 => 0
  | 2, 0 => 2
  | 2, 1 => 0
  | 2, 2 => 1

private theorem a4CharacterIndex_one : a4CharacterIndex 1 = 0 := by
  native_decide

private theorem a4CharacterIndex_mul_raw :
    ∀ sigma ∈ representativeCarrier .a4,
      ∀ tau ∈ representativeCarrier .a4,
        a4CharacterIndex (sigma * tau) =
          a4AddIndex (a4CharacterIndex sigma) (a4CharacterIndex tau) := by
  native_decide

private def a4OmegaUnit : ℂˣ where
  val := A4Certificate.omega
  inv := A4Certificate.omega ^ 2
  val_inv := by
    simpa only [pow_two, pow_three, mul_assoc] using A4Certificate.omega_cube
  inv_val := by
    simpa only [pow_two, pow_three, mul_assoc, mul_comm] using
      A4Certificate.omega_cube

private def a4OmegaUnitByIndex : Fin 3 → ℂˣ
  | 0 => 1
  | 1 => a4OmegaUnit
  | 2 => a4OmegaUnit ^ 2

private theorem a4OmegaUnitByIndex_mul (i j : Fin 3) :
    a4OmegaUnitByIndex (a4AddIndex i j) =
      a4OmegaUnitByIndex i * a4OmegaUnitByIndex j := by
  apply Units.ext
  fin_cases i <;> fin_cases j <;>
    simp [a4AddIndex, a4OmegaUnitByIndex, a4OmegaUnit,
      pow_succ] <;> ring
  all_goals first
    | exact A4Certificate.omega_cube.symm
    | exact A4Certificate.omega_pow_four.symm

/-- The primitive-root character of `A₄/V₄`. -/
def a4OmegaUnitCharacter : representative .a4 →* ℂˣ where
  toFun sigma := a4OmegaUnitByIndex (a4CharacterIndex sigma.1)
  map_one' := by
    rw [show (1 : representative .a4).1 = 1 by rfl,
      a4CharacterIndex_one]
    rfl
  map_mul' sigma tau := by
    rw [show (sigma * tau).1 = sigma.1 * tau.1 by rfl,
      a4CharacterIndex_mul_raw sigma.1 sigma.2 tau.1 tau.2]
    exact a4OmegaUnitByIndex_mul _ _

@[simp] theorem a4OmegaUnitCharacter_apply (sigma : representative .a4) :
    (a4OmegaUnitCharacter sigma : ℂ) = A4Gap.omegaCharacter sigma := by
  by_cases hv : sigma.1 ∈ representativeCarrier .v4Normal
  · simp [a4OmegaUnitCharacter, a4OmegaUnitByIndex,
      a4CharacterIndex, A4Gap.omegaCharacter, a4OmegaUnit, hv]
  · by_cases hp : sigma.1 ∈ A4Gap.a4PositiveClass
    · simp [a4OmegaUnitCharacter, a4OmegaUnitByIndex,
        a4CharacterIndex, A4Gap.omegaCharacter, a4OmegaUnit, hv, hp]
    · simp [a4OmegaUnitCharacter, a4OmegaUnitByIndex,
        a4CharacterIndex, A4Gap.omegaCharacter, a4OmegaUnit, hv, hp]

/-- Pointwise complex conjugation gives the other primitive-root character. -/
def a4OmegaConjugateUnitCharacter : representative .a4 →* ℂˣ :=
  (Units.map (starRingEnd ℂ)).comp a4OmegaUnitCharacter

@[simp] theorem a4OmegaConjugateUnitCharacter_apply
    (sigma : representative .a4) :
    (a4OmegaConjugateUnitCharacter sigma : ℂ) =
      A4Gap.omegaConjugateCharacter sigma := by
  simp [a4OmegaConjugateUnitCharacter, A4Gap.omegaConjugateCharacter]

theorem a4_rowOne_degree : (rowOfIndex .a4 ⟨1, by decide⟩).degree = 1 := by
  have h13 : (⟨1, by decide⟩ : Fin 4) ≠ 3 := by decide
  simp [rowOfIndex, a4Row, mkRow, h13]

theorem a4_rowTwo_degree : (rowOfIndex .a4 ⟨2, by decide⟩).degree = 1 := by
  have h23 : (⟨2, by decide⟩ : Fin 4) ≠ 3 := by decide
  simp [rowOfIndex, a4Row, mkRow, h23]

theorem a4_rowOne_character :
    (rowOfIndex .a4 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep a4OmegaUnitCharacter).character := by
  funext sigma
  rw [oneDimensionalFDRep_character, a4OmegaUnitCharacter_apply]
  have h := A4Registry.registered_omega_normalizedCoeff sigma
  change (rowOfIndex .a4 ⟨1, by decide⟩).coeff sigma /
    (rowOfIndex .a4 ⟨1, by decide⟩).degree = A4Gap.omegaCharacter sigma at h
  rw [a4_rowOne_degree] at h
  simpa using h

theorem a4_rowTwo_character :
    (rowOfIndex .a4 ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep a4OmegaConjugateUnitCharacter).character := by
  funext sigma
  rw [oneDimensionalFDRep_character, a4OmegaConjugateUnitCharacter_apply]
  have h := A4Registry.registered_omegaConjugate_normalizedCoeff sigma
  change (rowOfIndex .a4 ⟨2, by decide⟩).coeff sigma /
    (rowOfIndex .a4 ⟨2, by decide⟩).degree =
      A4Gap.omegaConjugateCharacter sigma at h
  rw [a4_rowTwo_degree] at h
  simpa using h

instance a4_rowOne_simple :
    Simple (oneDimensionalFDRep a4OmegaUnitCharacter) :=
  oneDimensionalFDRep_simple _

instance a4_rowTwo_simple :
    Simple (oneDimensionalFDRep a4OmegaConjugateUnitCharacter) :=
  oneDimensionalFDRep_simple _

/-! ## The standard three-dimensional representation -/

private def a4Raw : Fin 12 → S4
  | 0 => p0123 | 1 => p0231 | 2 => p0312 | 3 => p1032
  | 4 => p1203 | 5 => p1320 | 6 => p2013 | 7 => p2130
  | 8 => p2301 | 9 => p3021 | 10 => p3102 | 11 => p3210

private def a4Index (sigma : S4) : Fin 12 :=
  if sigma = p0123 then 0 else if sigma = p0231 then 1
  else if sigma = p0312 then 2 else if sigma = p1032 then 3
  else if sigma = p1203 then 4 else if sigma = p1320 then 5
  else if sigma = p2013 then 6 else if sigma = p2130 then 7
  else if sigma = p2301 then 8 else if sigma = p3021 then 9
  else if sigma = p3102 then 10 else 11

private def a4MulIndex : Fin 12 → Fin 12 → Fin 12
  | 0, j => j
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => 6
  | 1, 4 => 8 | 1, 5 => 7 | 1, 6 => 9 | 1, 7 => 11
  | 1, 8 => 10 | 1, 9 => 3 | 1, 10 => 4 | 1, 11 => 5
  | 2, 0 => 2 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 9
  | 2, 4 => 10 | 2, 5 => 11 | 2, 6 => 3 | 2, 7 => 5
  | 2, 8 => 4 | 2, 9 => 6 | 2, 10 => 8 | 2, 11 => 7
  | 3, 0 => 3 | 3, 1 => 5 | 3, 2 => 4 | 3, 3 => 0
  | 3, 4 => 2 | 3, 5 => 1 | 3, 6 => 10 | 3, 7 => 9
  | 3, 8 => 11 | 3, 9 => 7 | 3, 10 => 6 | 3, 11 => 8
  | 4, 0 => 4 | 4, 1 => 3 | 4, 2 => 5 | 4, 3 => 7
  | 4, 4 => 6 | 4, 5 => 8 | 4, 6 => 0 | 4, 7 => 1
  | 4, 8 => 2 | 4, 9 => 10 | 4, 10 => 11 | 4, 11 => 9
  | 5, 0 => 5 | 5, 1 => 4 | 5, 2 => 3 | 5, 3 => 10
  | 5, 4 => 11 | 5, 5 => 9 | 5, 6 => 7 | 5, 7 => 8
  | 5, 8 => 6 | 5, 9 => 0 | 5, 10 => 2 | 5, 11 => 1
  | 6, 0 => 6 | 6, 1 => 7 | 6, 2 => 8 | 6, 3 => 1
  | 6, 4 => 0 | 6, 5 => 2 | 6, 6 => 4 | 6, 7 => 3
  | 6, 8 => 5 | 6, 9 => 11 | 6, 10 => 9 | 6, 11 => 10
  | 7, 0 => 7 | 7, 1 => 8 | 7, 2 => 6 | 7, 3 => 4
  | 7, 4 => 5 | 7, 5 => 3 | 7, 6 => 11 | 7, 7 => 10
  | 7, 8 => 9 | 7, 9 => 1 | 7, 10 => 0 | 7, 11 => 2
  | 8, 0 => 8 | 8, 1 => 6 | 8, 2 => 7 | 8, 3 => 11
  | 8, 4 => 9 | 8, 5 => 10 | 8, 6 => 1 | 8, 7 => 2
  | 8, 8 => 0 | 8, 9 => 4 | 8, 10 => 5 | 8, 11 => 3
  | 9, 0 => 9 | 9, 1 => 11 | 9, 2 => 10 | 9, 3 => 2
  | 9, 4 => 1 | 9, 5 => 0 | 9, 6 => 8 | 9, 7 => 6
  | 9, 8 => 7 | 9, 9 => 5 | 9, 10 => 3 | 9, 11 => 4
  | 10, 0 => 10 | 10, 1 => 9 | 10, 2 => 11 | 10, 3 => 5
  | 10, 4 => 3 | 10, 5 => 4 | 10, 6 => 2 | 10, 7 => 0
  | 10, 8 => 1 | 10, 9 => 8 | 10, 10 => 7 | 10, 11 => 6
  | 11, 0 => 11 | 11, 1 => 10 | 11, 2 => 9 | 11, 3 => 8
  | 11, 4 => 7 | 11, 5 => 6 | 11, 6 => 5 | 11, 7 => 4
  | 11, 8 => 3 | 11, 9 => 2 | 11, 10 => 1 | 11, 11 => 0

private theorem a4_index_one : a4Index 1 = 0 := by native_decide

private theorem a4_index_mul_on_carrier :
    ∀ sigma ∈ representativeCarrier .a4,
      ∀ tau ∈ representativeCarrier .a4,
        a4Index (sigma * tau) = a4MulIndex (a4Index sigma) (a4Index tau) := by
  native_decide

private def a4IntMat : Fin 12 → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 0, 0; -1, -1, -1; 0, 1, 0]
  | 2 => !![1, 0, 0; 0, 0, 1; -1, -1, -1]
  | 3 => !![0, 1, 0; 1, 0, 0; -1, -1, -1]
  | 4 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  | 5 => !![-1, -1, -1; 1, 0, 0; 0, 0, 1]
  | 6 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | 7 => !![-1, -1, -1; 0, 1, 0; 1, 0, 0]
  | 8 => !![0, 0, 1; -1, -1, -1; 1, 0, 0]
  | 9 => !![0, 1, 0; -1, -1, -1; 0, 0, 1]
  | 10 => !![0, 0, 1; 0, 1, 0; -1, -1, -1]
  | 11 => !![-1, -1, -1; 0, 0, 1; 0, 1, 0]

private theorem a4IntMat_mul (i j : Fin 12) :
    a4IntMat (a4MulIndex i j) = a4IntMat i * a4IntMat j := by
  revert i j
  native_decide

private def a4Mat (i : Fin 12) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun r c => (a4IntMat i r c : ℂ)

private theorem a4Mat_mul (i j : Fin 12) :
    a4Mat (a4MulIndex i j) = a4Mat i * a4Mat j := by
  ext r c
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M r c)
    (a4IntMat_mul i j)
  simp only [a4Mat, Matrix.mul_apply, Fin.sum_univ_three] at h ⊢
  exact_mod_cast h

private theorem a4Mat_zero : a4Mat 0 = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [a4Mat, a4IntMat, Matrix.one_apply]

private def a4LinByIndex (i : Fin 12) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  Matrix.toLin' (a4Mat i)


private theorem a4LinByIndex_mul (i j : Fin 12) :
    a4LinByIndex (a4MulIndex i j) = a4LinByIndex i * a4LinByIndex j := by
  change Matrix.toLin' (a4Mat (a4MulIndex i j)) =
    (Matrix.toLin' (a4Mat i)).comp (Matrix.toLin' (a4Mat j))
  rw [a4Mat_mul, Matrix.toLin'_mul]

/-- The standard `A₄` action, in zero-sum coordinates for the permutation
representation on four letters. -/
def a4StandardRepresentation :
    Representation ℂ (representative .a4) (Fin 3 → ℂ) where
  toFun sigma := a4LinByIndex (a4Index sigma.1)
  map_one' := by
    rw [show (1 : representative .a4).1 = 1 by rfl, a4_index_one]
    rw [a4LinByIndex, a4Mat_zero, Matrix.toLin'_one]
    change LinearMap.id = LinearMap.id
    rfl
  map_mul' sigma tau := by
    change a4LinByIndex (a4Index (sigma.1 * tau.1)) =
      a4LinByIndex (a4Index sigma.1) * a4LinByIndex (a4Index tau.1)
    rw [a4_index_mul_on_carrier sigma.1 sigma.2 tau.1 tau.2]
    exact a4LinByIndex_mul _ _

def a4StandardFDRep : FDRep ℂ (representative .a4) :=
  FDRep.of a4StandardRepresentation

@[simp] theorem a4Standard_finrank : Module.finrank ℂ a4StandardFDRep = 3 := by
  simp [a4StandardFDRep, a4StandardRepresentation, FDRep.of]

private def a4TraceValue : Fin 12 → ℤ
  | 0 => 3 | 3 => -1 | 8 => -1 | 11 => -1 | _ => 0

private theorem a4LinByIndex_trace (i : Fin 12) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (a4LinByIndex i) =
      (a4TraceValue i : ℤ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 3))]
  change Matrix.trace (LinearMap.toMatrix' (Matrix.toLin' (a4Mat i))) = _
  rw [LinearMap.toMatrix'_toLin']
  fin_cases i <;>
    norm_num [Matrix.trace_fin_three, a4TraceValue, a4Mat, a4IntMat,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private def a4RegisteredStandardInt (sigma : S4) : ℤ :=
  if sigma = 1 then 3 else if sigma * sigma = 1 then -1 else 0

private theorem a4_trace_value_table :
    ∀ sigma ∈ representativeCarrier .a4,
      a4TraceValue (a4Index sigma) = a4RegisteredStandardInt sigma := by
  native_decide

set_option maxHeartbeats 3000000 in
theorem a4_standard_character :
    (rowOfIndex .a4 ⟨3, by decide⟩).coeff = a4StandardFDRep.character := by
  funext sigma
  change (if sigma.1 = 1 then 3 else if sigma.1 * sigma.1 = 1 then -1 else 0 : ℂ) =
    LinearMap.trace ℂ (Fin 3 → ℂ) (a4LinByIndex (a4Index sigma.1))
  rw [a4LinByIndex_trace]
  have hv := a4_trace_value_table sigma.1 sigma.2
  rw [hv]
  simp [a4RegisteredStandardInt]

theorem a4_standard_degree : (rowOfIndex .a4 ⟨3, by decide⟩).degree = 3 := by
  have h3 : (⟨3, by decide⟩ : Fin 4) = 3 := rfl
  simp [rowOfIndex, a4Row, mkRow, h3]

/-! ### Irreducibility of the standard representation -/

/-- The three-cycle operator used in the irreducibility calculation. -/
def a4R : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := a4LinByIndex 4

/-- The double-transposition operator used in the irreducibility calculation. -/
def a4D : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := a4LinByIndex 3

@[simp] theorem a4R_apply (v : Fin 3 → ℂ) :
    a4R v = ![v 2, v 0, v 1] := by
  ext k
  fin_cases k <;>
    simp [a4R, a4LinByIndex, a4Mat, a4IntMat, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem a4D_apply (v : Fin 3 → ℂ) :
    a4D v = ![v 1, v 0, -v 0 - v 1 - v 2] := by
  ext k
  fin_cases k <;>
    simp [a4D, a4LinByIndex, a4Mat, a4IntMat, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private def a4E0 : Fin 3 → ℂ := ![1, 0, 0]
private def a4E1 : Fin 3 → ℂ := ![0, 1, 0]
private def a4E2 : Fin 3 → ℂ := ![0, 0, 1]
private def a4E : Fin 3 → ℂ := ![1, 1, 1]
private def a4Q : Fin 3 → ℂ :=
  ![A4Certificate.omega ^ 2, A4Certificate.omega, 1]
private def a4Qbar : Fin 3 → ℂ :=
  ![A4Certificate.omega, A4Certificate.omega ^ 2, 1]

private theorem a4_top_of_e0
    (p : Submodule ℂ (Fin 3 → ℂ))
    (hR : ∀ v ∈ p, a4R v ∈ p) (he0 : a4E0 ∈ p) : p = ⊤ := by
  have he1 : a4E1 ∈ p := by
    have h := hR a4E0 he0
    simpa [a4E0, a4E1] using h
  have he2 : a4E2 ∈ p := by
    have h := hR a4E1 he1
    simpa [a4E1, a4E2] using h
  apply top_unique
  intro v _
  have hv := p.add_mem
    (p.add_mem (p.smul_mem (v 0) he0) (p.smul_mem (v 1) he1))
    (p.smul_mem (v 2) he2)
  convert hv using 1
  ext k
  fin_cases k <;> simp [a4E0, a4E1, a4E2, Pi.smul_apply]

private theorem a4_top_of_e
    (p : Submodule ℂ (Fin 3 → ℂ))
    (hR : ∀ v ∈ p, a4R v ∈ p)
    (hD : ∀ v ∈ p, a4D v ∈ p) (he : a4E ∈ p) : p = ⊤ := by
  have hu : a4D a4E ∈ p := hD a4E he
  have hru : a4R (a4D a4E) ∈ p := hR _ hu
  have hr2u : a4R (a4R (a4D a4E)) ∈ p := hR _ hru
  have he0 : a4E0 ∈ p := by
    have h := p.add_mem
      (p.add_mem (p.smul_mem (-(1 : ℂ) / 4) hu)
        (p.smul_mem (-(1 : ℂ) / 2) hru))
      (p.smul_mem (-(1 : ℂ) / 4) hr2u)
    convert h using 1
    ext k
    fin_cases k <;>
      simp [a4E, a4E0, Pi.smul_apply] <;> ring
  exact a4_top_of_e0 p hR he0

private theorem a4_top_of_q
    (p : Submodule ℂ (Fin 3 → ℂ))
    (hR : ∀ v ∈ p, a4R v ∈ p)
    (hD : ∀ v ∈ p, a4D v ∈ p) (hq : a4Q ∈ p) : p = ⊤ := by
  have how2 : A4Certificate.omega ^ 2 = -A4Certificate.omega - 1 := by
    linear_combination A4Certificate.omega_sq_add_omega_add_one
  have hu : a4D a4Q ∈ p := hD a4Q hq
  have hru : a4R (a4D a4Q) ∈ p := hR _ hu
  have hr2u : a4R (a4R (a4D a4Q)) ∈ p := hR _ hru
  have he0 : a4E0 ∈ p := by
    have h := p.add_mem
      (p.add_mem
        (p.smul_mem (A4Certificate.omega ^ 2 / 2) hu)
        (p.smul_mem (-(1 : ℂ) / 2) hru))
      (p.smul_mem (A4Certificate.omega / 2) hr2u)
    convert h using 1
    ext k
    fin_cases k <;>
      simp [a4Q, a4E0, Pi.smul_apply] <;>
      ring_nf <;>
      simp only [A4Certificate.omega_cube, A4Certificate.omega_pow_four,
        one_mul] <;>
      rw [how2] <;> ring
  exact a4_top_of_e0 p hR he0

private theorem a4_top_of_qbar
    (p : Submodule ℂ (Fin 3 → ℂ))
    (hR : ∀ v ∈ p, a4R v ∈ p)
    (hD : ∀ v ∈ p, a4D v ∈ p) (hq : a4Qbar ∈ p) : p = ⊤ := by
  have how2 : A4Certificate.omega ^ 2 = -A4Certificate.omega - 1 := by
    linear_combination A4Certificate.omega_sq_add_omega_add_one
  have hu : a4D a4Qbar ∈ p := hD a4Qbar hq
  have hru : a4R (a4D a4Qbar) ∈ p := hR _ hu
  have hr2u : a4R (a4R (a4D a4Qbar)) ∈ p := hR _ hru
  have he0 : a4E0 ∈ p := by
    have h := p.add_mem
      (p.add_mem
        (p.smul_mem (A4Certificate.omega / 2) hu)
        (p.smul_mem (-(1 : ℂ) / 2) hru))
      (p.smul_mem (A4Certificate.omega ^ 2 / 2) hr2u)
    convert h using 1
    ext k
    fin_cases k <;>
      simp [a4Qbar, a4E0, Pi.smul_apply] <;>
      ring_nf <;>
      simp only [A4Certificate.omega_cube, A4Certificate.omega_pow_four,
        one_mul] <;>
      rw [how2] <;> ring
  exact a4_top_of_e0 p hR he0

/-- A nonzero subspace stable under the displayed three-cycle and double
transposition is the whole standard three-space. -/
theorem a4_stable_under_R_D_eq_top
    (p : Submodule ℂ (Fin 3 → ℂ))
    (hR : ∀ v ∈ p, a4R v ∈ p)
    (hD : ∀ v ∈ p, a4D v ∈ p) (hne : p ≠ ⊥) : p = ⊤ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff p).mp hne
  let rv := a4R v
  let r2v := a4R rv
  have hrv : rv ∈ p := by
    exact hR v hv
  have hr2v : r2v ∈ p := by
    exact hR rv hrv
  let z0 := v + rv + r2v
  let z1 := v + A4Certificate.omega ^ 2 • rv + A4Certificate.omega • r2v
  let z2 := v + A4Certificate.omega • rv + A4Certificate.omega ^ 2 • r2v
  have hz0 : z0 ∈ p := p.add_mem (p.add_mem hv hrv) hr2v
  have hz1 : z1 ∈ p := p.add_mem
    (p.add_mem hv (p.smul_mem _ hrv)) (p.smul_mem _ hr2v)
  have hz2 : z2 ∈ p := p.add_mem
    (p.add_mem hv (p.smul_mem _ hrv)) (p.smul_mem _ hr2v)
  let c0 : ℂ := v 0 + v 1 + v 2
  let c1 : ℂ := v 2 + A4Certificate.omega ^ 2 * v 1 +
    A4Certificate.omega * v 0
  let c2 : ℂ := v 2 + A4Certificate.omega * v 1 +
    A4Certificate.omega ^ 2 * v 0
  have how2 : A4Certificate.omega ^ 2 = -A4Certificate.omega - 1 := by
    linear_combination A4Certificate.omega_sq_add_omega_add_one
  have hform0 : z0 = c0 • a4E := by
    ext k
    fin_cases k <;>
      simp [z0, rv, r2v, c0, a4E, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  have hform1 : z1 = c1 • a4Q := by
    ext k
    fin_cases k <;>
      simp [z1, rv, r2v, c1, a4Q, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail] <;>
      ring_nf <;>
      try simp only [A4Certificate.omega_cube, A4Certificate.omega_pow_four,
        one_mul] <;>
      rw [how2] <;> ring
  have hform2 : z2 = c2 • a4Qbar := by
    ext k
    fin_cases k <;>
      simp [z2, rv, r2v, c2, a4Qbar, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail] <;>
      ring_nf <;>
      try simp only [A4Certificate.omega_cube, A4Certificate.omega_pow_four,
        one_mul] <;>
      rw [how2] <;> ring
  have hsum : z0 + z1 + z2 = (3 : ℂ) • v := by
    ext k
    fin_cases k <;>
      simp [z0, z1, z2, rv, r2v, Pi.smul_apply,
        Matrix.vecHead, Matrix.vecTail] <;>
      rw [how2] <;> ring
  have recover (z q : Fin 3 → ℂ) (c : ℂ) (hz : z ∈ p)
      (hform : z = c • q) (hn : z ≠ 0) : q ∈ p := by
    have hc : c ≠ 0 := by
      intro hc
      apply hn
      rw [hform, hc, zero_smul]
    rw [hform] at hz
    have h := p.smul_mem c⁻¹ hz
    simpa [hc] using h
  by_cases hzero0 : z0 = 0
  · by_cases hzero1 : z1 = 0
    · have hne2 : z2 ≠ 0 := by
        intro hzero2
        have hthree : (3 : ℂ) • v = 0 := by
          rw [← hsum, hzero0, hzero1, hzero2]
          simp
        have hvz : v = 0 :=
          (smul_eq_zero.mp hthree).resolve_left (by norm_num)
        exact hv0 hvz
      exact a4_top_of_qbar p hR hD
        (recover z2 a4Qbar c2 hz2 hform2 hne2)
    · exact a4_top_of_q p hR hD
        (recover z1 a4Q c1 hz1 hform1 hzero1)
  · exact a4_top_of_e p hR hD
      (recover z0 a4E c0 hz0 hform0 hzero0)

private def a4rElt : representative .a4 := A4Gap.q1203
private def a4dElt : representative .a4 := A4Gap.q1032

private theorem a4Standard_rho_r (v : Fin 3 → ℂ) :
    a4StandardFDRep.ρ a4rElt v = a4R v := by
  change a4LinByIndex (a4Index p1203) v = a4LinByIndex 4 v
  rw [show a4Index p1203 = 4 by native_decide]

private theorem a4Standard_rho_d (v : Fin 3 → ℂ) :
    a4StandardFDRep.ρ a4dElt v = a4D v := by
  change a4LinByIndex (a4Index p1032) v = a4LinByIndex 3 v
  rw [show a4Index p1032 = 3 by native_decide]

instance a4_standard_simple : Simple a4StandardFDRep where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) (representative .a4)
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 a4StandardFDRep : a4StandardFDRep ⟶ a4StandardFDRep) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      have heval := congrArg
        (fun q : a4StandardFDRep ⟶ a4StandardFDRep => q.hom.hom a4E0) hid
      have h0 := congr_fun heval 0
      change (1 : ℂ) = 0 at h0
      exact one_ne_zero h0
    · intro hnonzero
      have hlin : f.hom.hom ≠ 0 := by
        intro hzero
        apply hnonzero
        apply Action.Hom.ext
        exact ModuleCat.hom_ext hzero
      let p : Submodule ℂ (Fin 3 → ℂ) := LinearMap.range f.hom.hom
      have hstable (h : representative .a4) (v : Fin 3 → ℂ) (hv : v ∈ p) :
          a4StandardFDRep.ρ h v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ h y, ?_⟩
        have hc := congrArg (fun q : Y.V ⟶ a4StandardFDRep.V => q.hom y) (f.comm h)
        simpa using hc
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := a4_stable_under_R_D_eq_top p
        (fun v hv => by simpa [a4Standard_rho_r] using hstable a4rElt v hv)
        (fun v hv => by simpa [a4Standard_rho_d] using hstable a4dElt v hv)
        hpne
      have hsurj : Function.Surjective f.hom.hom := LinearMap.range_eq_top.mp hp
      let U := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
      haveI : Mono (U.map f.hom) := by infer_instance
      have hinj : Function.Injective f.hom.hom :=
        (ModuleCat.mono_iff_injective (U.map f.hom)).1 inferInstance
      haveI : IsIso (U.map f.hom) :=
        (ConcreteCategory.isIso_iff_bijective (U.map f.hom)).2 ⟨hinj, hsurj⟩
      haveI : IsIso f.hom := isIso_of_reflects_iso f.hom U
      infer_instance

/-! ## Exhaustion of the irreducibles -/

/-- The four concrete irreducible `A₄` representations, in character-table
order: the trivial character, the two cubic characters, and the standard
three-dimensional representation. -/
def a4RegisteredIrrep (i : Fin 4) : FDRep ℂ (representative .a4) :=
  if i = 0 then oneDimensionalFDRep (trivialUnitCharacter (representative .a4))
  else if i = 1 then oneDimensionalFDRep a4OmegaUnitCharacter
  else if i = 2 then oneDimensionalFDRep a4OmegaConjugateUnitCharacter
  else a4StandardFDRep

instance a4RegisteredIrrep_simple (i : Fin 4) : Simple (a4RegisteredIrrep i) := by
  fin_cases i <;> simp [a4RegisteredIrrep] <;> infer_instance

/-- Each registered representation has the character in the corresponding
row of the concrete `A₄` table. -/
theorem a4RegisteredIrrep_character (i : Fin 4) :
    (rowOfIndex .a4 i).coeff = (a4RegisteredIrrep i).character := by
  fin_cases i
  · simpa [a4RegisteredIrrep] using rowZero_character .a4
  · simpa [a4RegisteredIrrep] using a4_rowOne_character
  · simpa [a4RegisteredIrrep] using a4_rowTwo_character
  · simpa [a4RegisteredIrrep] using a4_standard_character

/-- Each registered representation has the degree in the corresponding row
of the concrete `A₄` table. -/
theorem a4RegisteredIrrep_degree (i : Fin 4) :
    (rowOfIndex .a4 i).degree =
      (Module.finrank ℂ (a4RegisteredIrrep i) : ℂ) := by
  fin_cases i
  · simpa [a4RegisteredIrrep] using rowZero_degree .a4
  · simpa [a4RegisteredIrrep] using a4_rowOne_degree
  · simpa [a4RegisteredIrrep] using a4_rowTwo_degree
  · simpa [a4RegisteredIrrep] using a4_standard_degree

private theorem a4_card : Fintype.card (representative .a4) = 12 := by
  let e : representative .a4 ≃ {x // x ∈ representativeCarrier .a4} := {
    toFun x := ⟨x.1, (mem_representative_iff .a4 x.1).mp x.2⟩
    invFun x := ⟨x.1, (mem_representative_iff .a4 x.1).mpr x.2⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  calc
    Fintype.card (representative .a4) =
        Fintype.card {x // x ∈ representativeCarrier .a4} := Fintype.card_congr e
    _ = (representativeCarrier .a4).card := Fintype.card_coe _
    _ = 12 := by native_decide

private theorem a4_registered_regular_identity (h : representative .a4) :
    (rowOfIndex .a4 ⟨0, by decide⟩).coeff h +
      (rowOfIndex .a4 ⟨1, by decide⟩).coeff h +
      (rowOfIndex .a4 ⟨2, by decide⟩).coeff h +
      3 * (rowOfIndex .a4 ⟨3, by decide⟩).coeff h =
        if h = 1 then 12 else 0 := by
  change (1 : ℂ) +
      (if h.1 = 1 ∨ h.1 * h.1 = 1 then 1
        else if inA4PositiveClass h.1 then A4Certificate.omega
        else A4Certificate.omega ^ 2) +
      (if h.1 = 1 ∨ h.1 * h.1 = 1 then 1
        else if inA4PositiveClass h.1 then A4Certificate.omega ^ 2
        else A4Certificate.omega) +
      3 * (if h.1 = 1 then 3 else if h.1 * h.1 = 1 then -1 else 0) =
        if h = 1 then 12 else 0
  by_cases hid : h = 1
  · have hval : h.1 = 1 := congrArg Subtype.val hid
    simp [hid, hval]
    norm_num
  · have hval : h.1 ≠ 1 := by
      intro hh
      exact hid (Subtype.ext hh)
    by_cases hsquare : h.1 * h.1 = 1
    · simp [hid, hval, hsquare]
      norm_num
    · by_cases hpositive : inA4PositiveClass h.1
      · simp [hid, hval, hsquare, hpositive]
        linear_combination A4Certificate.omega_sq_add_omega_add_one
      · simp [hid, hval, hsquare, hpositive]
        linear_combination A4Certificate.omega_sq_add_omega_add_one

/-- The degree-weighted sum of the four registered characters is the regular
character of the concrete `A₄` representative. -/
theorem a4RegisteredIrrep_regular_identity (h : representative .a4) :
    ∑ i : Fin 4, (Module.finrank ℂ (a4RegisteredIrrep i) : ℂ) *
        (a4RegisteredIrrep i).character h =
      if h = 1 then (Fintype.card (representative .a4) : ℂ) else 0 := by
  rw [Fin.sum_univ_four]
  change
    (Module.finrank ℂ (oneDimensionalFDRep
      (trivialUnitCharacter (representative .a4))) : ℂ) *
        (oneDimensionalFDRep
          (trivialUnitCharacter (representative .a4))).character h +
    (Module.finrank ℂ (oneDimensionalFDRep a4OmegaUnitCharacter) : ℂ) *
        (oneDimensionalFDRep a4OmegaUnitCharacter).character h +
    (Module.finrank ℂ
      (oneDimensionalFDRep a4OmegaConjugateUnitCharacter) : ℂ) *
        (oneDimensionalFDRep a4OmegaConjugateUnitCharacter).character h +
    (Module.finrank ℂ a4StandardFDRep : ℂ) * a4StandardFDRep.character h = _
  rw [oneDimensionalFDRep_finrank, oneDimensionalFDRep_finrank,
    oneDimensionalFDRep_finrank, a4Standard_finrank]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  rw [← rowZero_character .a4, ← a4_rowOne_character,
    ← a4_rowTwo_character, ← a4_standard_character, a4_card]
  exact a4_registered_regular_identity h

/-- Every simple complex representation of the concrete `A₄` representative
is isomorphic to exactly one of the four registered candidates (existence is
all that is needed by the table-completeness registry). -/
theorem a4_simple_complete (V : FDRep ℂ (representative .a4)) [Simple V] :
    ∃ i : Fin 4, Nonempty (V ≅ a4RegisteredIrrep i) :=
  simple_complete_of_regular_character_identity a4RegisteredIrrep
    a4RegisteredIrrep_regular_identity V

end PermanentalDominance.N4
