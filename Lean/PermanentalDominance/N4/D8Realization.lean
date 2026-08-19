import PermanentalDominance.N4.NonabelianRealization

/-!
# The five irreducible representations of the concrete dihedral subgroup

The finite multiplication table is separated from the matrix calculations.  Thus all group
equalities are discharged by a small native certificate, while all representation identities are
eight-by-eight calculations with two explicit matrices.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

local instance : Fintype (representative .d8) := Fintype.ofFinite _

private def d8g : S4 := ConcretePerm.cycle0123
private def d8s : S4 := ConcretePerm.t02

private def d8ExplicitCarrier : Finset S4 :=
  {1, d8g, d8g ^ 2, d8g ^ 3, d8s, d8s * d8g, d8s * d8g ^ 2, d8s * d8g ^ 3}

private theorem d8_carrier_eq_explicit : representativeCarrier .d8 = d8ExplicitCarrier := by
  native_decide

private def d8e (x : S4) (hx : x ∈ d8ExplicitCarrier) : representative .d8 :=
  ⟨x, by simpa [d8_carrier_eq_explicit] using hx⟩

private def d8Raw : Fin 8 → S4
  | 0 => 1 | 1 => d8g | 2 => d8g ^ 2 | 3 => d8g ^ 3
  | 4 => d8s | 5 => d8s * d8g | 6 => d8s * d8g ^ 2 | 7 => d8s * d8g ^ 3

private def d8Index (x : S4) : Fin 8 :=
  if x = 1 then 0 else if x = d8g then 1 else if x = d8g ^ 2 then 2
  else if x = d8g ^ 3 then 3 else if x = d8s then 4 else if x = d8s * d8g then 5
  else if x = d8s * d8g ^ 2 then 6 else 7

private def d8MulIndex : Fin 8 → Fin 8 → Fin 8
  | 0, j => j
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 3 | 1, 3 => 0
  | 1, 4 => 7 | 1, 5 => 4 | 1, 6 => 5 | 1, 7 => 6
  | 2, 0 => 2 | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1
  | 2, 4 => 6 | 2, 5 => 7 | 2, 6 => 4 | 2, 7 => 5
  | 3, 0 => 3 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 2
  | 3, 4 => 5 | 3, 5 => 6 | 3, 6 => 7 | 3, 7 => 4
  | 4, 0 => 4 | 4, 1 => 5 | 4, 2 => 6 | 4, 3 => 7
  | 4, 4 => 0 | 4, 5 => 1 | 4, 6 => 2 | 4, 7 => 3
  | 5, 0 => 5 | 5, 1 => 6 | 5, 2 => 7 | 5, 3 => 4
  | 5, 4 => 3 | 5, 5 => 0 | 5, 6 => 1 | 5, 7 => 2
  | 6, 0 => 6 | 6, 1 => 7 | 6, 2 => 4 | 6, 3 => 5
  | 6, 4 => 2 | 6, 5 => 3 | 6, 6 => 0 | 6, 7 => 1
  | 7, 0 => 7 | 7, 1 => 4 | 7, 2 => 5 | 7, 3 => 6
  | 7, 4 => 1 | 7, 5 => 2 | 7, 6 => 3 | 7, 7 => 0

private theorem d8_index_one : d8Index 1 = 0 := by native_decide

private theorem d8_index_mul_on_carrier :
    ∀ a ∈ representativeCarrier .d8, ∀ b ∈ representativeCarrier .d8,
      d8Index (a * b) = d8MulIndex (d8Index a) (d8Index b) := by
  native_decide

private def complexSignUnit (b : Bool) : ℂˣ := if b then -1 else 1

private def d8LinearBit (eg es : Bool) : Fin 8 → Bool
  | 0 => false | 1 => eg | 2 => false | 3 => eg
  | 4 => es | 5 => Bool.xor eg es | 6 => es | 7 => Bool.xor eg es

private def d8UnitByIndex (eg es : Bool) (i : Fin 8) : ℂˣ :=
  complexSignUnit (d8LinearBit eg es i)

private theorem d8UnitByIndex_mul (eg es : Bool) (i j : Fin 8) :
    d8UnitByIndex eg es (d8MulIndex i j) =
      d8UnitByIndex eg es i * d8UnitByIndex eg es j := by
  cases eg <;> cases es <;> fin_cases i <;> fin_cases j <;>
    norm_num [d8UnitByIndex, d8LinearBit, d8MulIndex, complexSignUnit]

/-- A one-dimensional dihedral character, with `eg` and `es` recording the signs of the
rotation and reflection generators. -/
def d8LinearUnitCharacter (eg es : Bool) : representative .d8 →* ℂˣ where
  toFun h := d8UnitByIndex eg es (d8Index h.1)
  map_one' := by
    change d8UnitByIndex eg es (d8Index (1 : S4)) = 1
    rw [d8_index_one]
    rfl
  map_mul' h k := by
    change d8UnitByIndex eg es (d8Index (h.1 * k.1)) =
      d8UnitByIndex eg es (d8Index h.1) * d8UnitByIndex eg es (d8Index k.1)
    rw [d8_index_mul_on_carrier h.1 h.2 k.1 k.2]
    exact d8UnitByIndex_mul _ _ _ _

private def d8SignInt (b : Bool) : ℤ := if b then -1 else 1

private def d8LinearIntValue (g s σ : S4) (eg es : Bool) : ℤ :=
  if σ = 1 then 1
  else if σ = g then d8SignInt eg
  else if σ = g ^ 2 then 1
  else if σ = g ^ 3 then d8SignInt eg
  else if σ = s then d8SignInt es
  else if σ = s * g then d8SignInt (Bool.xor eg es)
  else if σ = s * g ^ 2 then d8SignInt es
  else d8SignInt (Bool.xor eg es)

private theorem complexSignUnit_coe (b : Bool) :
    (complexSignUnit b : ℂ) = (d8SignInt b : ℤ) := by
  cases b <;> norm_num [complexSignUnit, d8SignInt]

private theorem d8LinearValue_eq_intCast (g s σ : S4) (eg es : Bool) :
    d8LinearValue g s σ eg es = (d8LinearIntValue g s σ eg es : ℤ) := by
  simp [d8LinearValue, d8LinearIntValue, d8SignInt]

private theorem d8_linear_index_table (eg es : Bool) :
    ∀ σ ∈ representativeCarrier .d8,
      d8SignInt (d8LinearBit eg es (d8Index σ)) =
        d8LinearIntValue d8g d8s σ eg es := by
  cases eg <;> cases es <;> native_decide

@[simp] theorem d8LinearUnitCharacter_apply (eg es : Bool) (h : representative .d8) :
    (d8LinearUnitCharacter eg es h : ℂ) = d8LinearValue d8g d8s h.1 eg es := by
  change (d8UnitByIndex eg es (d8Index h.1) : ℂ) = _
  rw [show (d8UnitByIndex eg es (d8Index h.1) : ℂ) =
      (d8SignInt (d8LinearBit eg es (d8Index h.1)) : ℤ) by
        exact complexSignUnit_coe _]
  rw [d8_linear_index_table eg es h.1 h.2]
  exact (d8LinearValue_eq_intCast d8g d8s h.1 eg es).symm

theorem d8_linear1_character :
    (rowOfIndex .d8 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep (d8LinearUnitCharacter true false)).character := by
  funext h
  simp [rowOfIndex, d8Row, mkRow, d8g, d8s, oneDimensionalFDRep_character]

theorem d8_linear2_character :
    (rowOfIndex .d8 ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep (d8LinearUnitCharacter false true)).character := by
  have h20 : (⟨2, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h21 : (⟨2, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h22 : (⟨2, by decide⟩ : Fin 5) = 2 := by decide
  funext h
  simp [rowOfIndex, d8Row, mkRow, d8g, d8s, h20, h21, h22,
    oneDimensionalFDRep_character]

theorem d8_linear3_character :
    (rowOfIndex .d8 ⟨3, by decide⟩).coeff =
      (oneDimensionalFDRep (d8LinearUnitCharacter true true)).character := by
  have h30 : (⟨3, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h31 : (⟨3, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h32 : (⟨3, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h33 : (⟨3, by decide⟩ : Fin 5) = 3 := by decide
  funext h
  simp [rowOfIndex, d8Row, mkRow, d8g, d8s, h30, h31, h32, h33,
    oneDimensionalFDRep_character]

theorem d8_linear1_degree : (rowOfIndex .d8 ⟨1, by decide⟩).degree = 1 := by
  simp [rowOfIndex, d8Row, mkRow]

theorem d8_linear2_degree : (rowOfIndex .d8 ⟨2, by decide⟩).degree = 1 := by
  have h20 : (⟨2, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h21 : (⟨2, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h22 : (⟨2, by decide⟩ : Fin 5) = 2 := by decide
  simp [rowOfIndex, d8Row, mkRow, h20, h21, h22]

theorem d8_linear3_degree : (rowOfIndex .d8 ⟨3, by decide⟩).degree = 1 := by
  have h30 : (⟨3, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h31 : (⟨3, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h32 : (⟨3, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h33 : (⟨3, by decide⟩ : Fin 5) = 3 := by decide
  simp [rowOfIndex, d8Row, mkRow, h30, h31, h32, h33]

instance d8_linear_simple (eg es : Bool) :
    Simple (oneDimensionalFDRep (d8LinearUnitCharacter eg es)) :=
  oneDimensionalFDRep_simple _

/-! ## The two-dimensional reflection representation -/

private def d8R : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![-v 1, v 0]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

private def d8S : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, v 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

private def d8LinByIndex : Fin 8 → (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)
  | 0 => LinearMap.id | 1 => d8R | 2 => d8R * d8R | 3 => d8R * (d8R * d8R)
  | 4 => d8S | 5 => d8S * d8R | 6 => d8S * (d8R * d8R)
  | 7 => d8S * (d8R * (d8R * d8R))

private def d8VecByIndex : Fin 8 → (Fin 2 → ℂ) → (Fin 2 → ℂ)
  | 0, v => ![v 0, v 1]
  | 1, v => ![-v 1, v 0]
  | 2, v => ![-v 0, -v 1]
  | 3, v => ![v 1, -v 0]
  | 4, v => ![v 1, v 0]
  | 5, v => ![v 0, -v 1]
  | 6, v => ![-v 1, -v 0]
  | 7, v => ![-v 0, v 1]

private theorem d8LinByIndex_apply (i : Fin 8) (v : Fin 2 → ℂ) :
    d8LinByIndex i v = d8VecByIndex i v := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [d8LinByIndex, d8VecByIndex, d8R, d8S, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem d8VecByIndex_mul (i j : Fin 8) (v : Fin 2 → ℂ) :
    d8VecByIndex (d8MulIndex i j) v = d8VecByIndex i (d8VecByIndex j v) := by
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [d8MulIndex, d8VecByIndex, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem d8LinByIndex_mul (i j : Fin 8) :
    d8LinByIndex (d8MulIndex i j) = d8LinByIndex i * d8LinByIndex j := by
  apply LinearMap.ext
  intro v
  change d8LinByIndex (d8MulIndex i j) v = d8LinByIndex i (d8LinByIndex j v)
  rw [d8LinByIndex_apply, d8LinByIndex_apply, d8LinByIndex_apply]
  exact d8VecByIndex_mul i j v

def d8StandardRepresentation : Representation ℂ (representative .d8) (Fin 2 → ℂ) where
  toFun h := d8LinByIndex (d8Index h.1)
  map_one' := by
    change d8LinByIndex (d8Index (1 : S4)) = 1
    rw [d8_index_one]
    rfl
  map_mul' h k := by
    change d8LinByIndex (d8Index (h.1 * k.1)) =
      d8LinByIndex (d8Index h.1) * d8LinByIndex (d8Index k.1)
    rw [d8_index_mul_on_carrier h.1 h.2 k.1 k.2]
    exact d8LinByIndex_mul _ _

def d8StandardFDRep : FDRep ℂ (representative .d8) := FDRep.of d8StandardRepresentation

@[simp] theorem d8Standard_finrank : Module.finrank ℂ d8StandardFDRep = 2 := by
  simp [d8StandardFDRep, d8StandardRepresentation, FDRep.of]

private def d8TraceValue : Fin 8 → ℤ
  | 0 => 2 | 2 => -2 | _ => 0

private theorem d8LinByIndex_trace (i : Fin 8) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (d8LinByIndex i) = (d8TraceValue i : ℤ) := by
  fin_cases i <;>
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2)), Matrix.trace_fin_two] <;>
    norm_num [d8TraceValue, d8LinByIndex, d8R, d8S, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

private def d8RegisteredStandardInt (σ : S4) : ℤ :=
  if σ = 1 then 2 else if σ = d8g ^ 2 then -2 else 0

private theorem d8_trace_table :
    ∀ σ ∈ representativeCarrier .d8,
      d8TraceValue (d8Index σ) = d8RegisteredStandardInt σ := by
  native_decide

theorem d8_standard_character :
    (rowOfIndex .d8 ⟨4, by decide⟩).coeff = d8StandardFDRep.character := by
  funext h
  change (if h.1 = 1 then 2 else if h.1 = d8g ^ 2 then -2 else 0 : ℂ) =
    LinearMap.trace ℂ (Fin 2 → ℂ) (d8LinByIndex (d8Index h.1))
  rw [d8LinByIndex_trace]
  have hv := d8_trace_table h.1 h.2
  rw [hv]
  simp [d8RegisteredStandardInt]

theorem d8_standard_degree : (rowOfIndex .d8 ⟨4, by decide⟩).degree = 2 := by
  have h4 : (⟨4, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h41 : (⟨4, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h42 : (⟨4, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h43 : (⟨4, by decide⟩ : Fin 5) ≠ 3 := by decide
  simp [rowOfIndex, d8Row, mkRow, h4, h41, h42, h43]

/-! ## Irreducibility of the reflection representation -/

private def d8gElt : representative .d8 := d8e d8g (by native_decide)
private def d8sElt : representative .d8 := d8e d8s (by native_decide)

private theorem d8Standard_rho_g (v : Fin 2 → ℂ) :
    d8StandardFDRep.ρ d8gElt v = d8R v := by
  change d8LinByIndex (d8Index d8g) v = d8R v
  rw [show d8Index d8g = 1 by native_decide]
  rfl

private theorem d8Standard_rho_s (v : Fin 2 → ℂ) :
    d8StandardFDRep.ρ d8sElt v = d8S v := by
  change d8LinByIndex (d8Index d8s) v = d8S v
  rw [show d8Index d8s = 4 by native_decide]
  rfl

private def d8E0 : Fin 2 → ℂ := ![1, 0]
private def d8E1 : Fin 2 → ℂ := ![0, 1]

private theorem d8_stable_range_eq_top
    (p : Submodule ℂ (Fin 2 → ℂ))
    (hR : ∀ v ∈ p, d8R v ∈ p)
    (hS : ∀ v ∈ p, d8S v ∈ p)
    (hne : p ≠ ⊥) : p = ⊤ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff p).mp hne
  have hSv : d8S v ∈ p := hS v hv
  have he0 : d8E0 ∈ p := by
    by_cases ha : v 0 + v 1 = 0
    · have hy : v 1 = -v 0 := by linear_combination ha
      have hx : v 0 ≠ 0 := by
        intro hx
        apply hv0
        funext i
        fin_cases i
        · exact hx
        · simpa [hy, hx]
      have hRv : d8R v ∈ p := hR v hv
      have hc : v + d8R v ∈ p := p.add_mem hv hRv
      have hden : 2 * v 0 ≠ 0 := mul_ne_zero (by norm_num) hx
      have hs := p.smul_mem (2 * v 0)⁻¹ hc
      convert hs using 1
      ext i
      fin_cases i
      · simp [d8E0, d8R, hy, Matrix.vecHead, Matrix.vecTail]
        field_simp [hden]
        ring
      · simp [d8E0, d8R, hy, Matrix.vecHead, Matrix.vecTail]
    · have hsum : v + d8S v ∈ p := p.add_mem hv hSv
      have hRsum : d8R (v + d8S v) ∈ p := hR _ hsum
      have hc : (v + d8S v) - d8R (v + d8S v) ∈ p := p.sub_mem hsum hRsum
      have hden : 2 * (v 0 + v 1) ≠ 0 := mul_ne_zero (by norm_num) ha
      have hs := p.smul_mem (2 * (v 0 + v 1))⁻¹ hc
      convert hs using 1
      ext i
      fin_cases i
      · simp [d8E0, d8R, d8S, Matrix.vecHead, Matrix.vecTail]
        field_simp [hden]
        ring
      · simp [d8E0, d8R, d8S, Matrix.vecHead, Matrix.vecTail]
        exact Or.inr (by ring)
  have he1 : d8E1 ∈ p := by
    have := hS d8E0 he0
    simpa [d8E0, d8E1, d8S, Matrix.vecHead, Matrix.vecTail] using this
  apply top_unique
  intro z hz
  have hz' := p.add_mem (p.smul_mem (z 0) he0) (p.smul_mem (z 1) he1)
  convert hz' using 1
  ext i
  fin_cases i <;> simp [d8E0, d8E1, Pi.smul_apply, Matrix.vecHead, Matrix.vecTail]

instance d8_standard_simple : Simple d8StandardFDRep where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) (representative .d8)
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 d8StandardFDRep : d8StandardFDRep ⟶ d8StandardFDRep) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      have heval := congrArg
        (fun q : d8StandardFDRep ⟶ d8StandardFDRep => q.hom.hom d8E0) hid
      have h0 := congr_fun heval 0
      change (1 : ℂ) = 0 at h0
      exact one_ne_zero h0
    · intro hnonzero
      have hlin : f.hom.hom ≠ 0 := by
        intro hzero
        apply hnonzero
        apply Action.Hom.ext
        exact ModuleCat.hom_ext hzero
      let p : Submodule ℂ (Fin 2 → ℂ) := LinearMap.range f.hom.hom
      have hstable (h : representative .d8) (v : Fin 2 → ℂ) (hv : v ∈ p) :
          d8StandardFDRep.ρ h v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ h y, ?_⟩
        have hc := congrArg (fun q : Y.V ⟶ d8StandardFDRep.V => q.hom y) (f.comm h)
        simpa using hc
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := d8_stable_range_eq_top p
        (fun v hv => by simpa [d8Standard_rho_g] using hstable d8gElt v hv)
        (fun v hv => by simpa [d8Standard_rho_s] using hstable d8sElt v hv) hpne
      have hsurj : Function.Surjective f.hom.hom := LinearMap.range_eq_top.mp hp
      let U := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
      haveI : Mono (U.map f.hom) := by infer_instance
      have hinj : Function.Injective f.hom.hom :=
        (ModuleCat.mono_iff_injective (U.map f.hom)).1 inferInstance
      haveI : IsIso (U.map f.hom) :=
        (ConcreteCategory.isIso_iff_bijective (U.map f.hom)).2 ⟨hinj, hsurj⟩
      haveI : IsIso f.hom := isIso_of_reflects_iso f.hom U
      infer_instance

/-! ## Registered family and completeness -/

def d8RegisteredIrrep (i : Fin 5) : FDRep ℂ (representative .d8) :=
  if i = 0 then oneDimensionalFDRep (trivialUnitCharacter (representative .d8))
  else if i = 1 then oneDimensionalFDRep (d8LinearUnitCharacter true false)
  else if i = 2 then oneDimensionalFDRep (d8LinearUnitCharacter false true)
  else if i = 3 then oneDimensionalFDRep (d8LinearUnitCharacter true true)
  else d8StandardFDRep

instance d8RegisteredIrrep_simple (i : Fin 5) : Simple (d8RegisteredIrrep i) := by
  fin_cases i <;> simp [d8RegisteredIrrep] <;> infer_instance

private theorem d8_card : Fintype.card (representative .d8) = 8 := by
  let e : representative .d8 ≃ {x // x ∈ representativeCarrier .d8} := {
    toFun x := ⟨x.1, (mem_representative_iff .d8 x.1).mp x.2⟩
    invFun x := ⟨x.1, (mem_representative_iff .d8 x.1).mpr x.2⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  calc
    Fintype.card (representative .d8) =
        Fintype.card {x // x ∈ representativeCarrier .d8} := Fintype.card_congr e
    _ = (representativeCarrier .d8).card := Fintype.card_coe _
    _ = 8 := by native_decide

private theorem d8_regular_integer_table :
    ∀ σ ∈ representativeCarrier .d8,
      (1 : ℤ) + d8LinearIntValue d8g d8s σ true false +
          d8LinearIntValue d8g d8s σ false true +
          d8LinearIntValue d8g d8s σ true true +
          2 * d8RegisteredStandardInt σ = if σ = 1 then 8 else 0 := by
  native_decide

private theorem d8_value_regular_identity (h : representative .d8) :
    (1 : ℂ) + d8LinearValue d8g d8s h.1 true false +
        d8LinearValue d8g d8s h.1 false true +
        d8LinearValue d8g d8s h.1 true true +
        2 * (if h.1 = 1 then 2 else if h.1 = d8g ^ 2 then -2 else 0) =
      if h = 1 then 8 else 0 := by
  rw [d8LinearValue_eq_intCast, d8LinearValue_eq_intCast, d8LinearValue_eq_intCast]
  have hv := d8_regular_integer_table h.1 h.2
  have heq : (h = 1) ↔ (h.1 = 1) := by
    constructor
    · exact fun hh => congrArg Subtype.val hh
    · exact fun hh => Subtype.ext hh
  simp only [heq]
  rw [show (if h.1 = 1 then 2 else if h.1 = d8g ^ 2 then -2 else 0 : ℂ) =
      (d8RegisteredStandardInt h.1 : ℤ) by simp [d8RegisteredStandardInt]]
  exact_mod_cast hv

theorem d8RegisteredIrrep_regular_identity (h : representative .d8) :
    ∑ i : Fin 5, (Module.finrank ℂ (d8RegisteredIrrep i) : ℂ) *
        (d8RegisteredIrrep i).character h =
      if h = 1 then (Fintype.card (representative .d8) : ℂ) else 0 := by
  rw [Fin.sum_univ_five]
  change
    (Module.finrank ℂ (oneDimensionalFDRep
      (trivialUnitCharacter (representative .d8))) : ℂ) *
        (oneDimensionalFDRep (trivialUnitCharacter (representative .d8))).character h +
    (Module.finrank ℂ (oneDimensionalFDRep
      (d8LinearUnitCharacter true false)) : ℂ) *
        (oneDimensionalFDRep (d8LinearUnitCharacter true false)).character h +
    (Module.finrank ℂ (oneDimensionalFDRep
      (d8LinearUnitCharacter false true)) : ℂ) *
        (oneDimensionalFDRep (d8LinearUnitCharacter false true)).character h +
    (Module.finrank ℂ (oneDimensionalFDRep
      (d8LinearUnitCharacter true true)) : ℂ) *
        (oneDimensionalFDRep (d8LinearUnitCharacter true true)).character h +
    (Module.finrank ℂ d8StandardFDRep : ℂ) * d8StandardFDRep.character h = _
  rw [oneDimensionalFDRep_finrank, oneDimensionalFDRep_finrank,
    oneDimensionalFDRep_finrank, oneDimensionalFDRep_finrank, d8Standard_finrank]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  rw [oneDimensionalFDRep_character, oneDimensionalFDRep_character,
    oneDimensionalFDRep_character, oneDimensionalFDRep_character,
    d8LinearUnitCharacter_apply, d8LinearUnitCharacter_apply,
    d8LinearUnitCharacter_apply, ← d8_standard_character, d8_card]
  change (1 : ℂ) + d8LinearValue d8g d8s h.1 true false +
      d8LinearValue d8g d8s h.1 false true +
      d8LinearValue d8g d8s h.1 true true +
      2 * (if h.1 = 1 then 2 else if h.1 = d8g ^ 2 then -2 else 0) = _
  exact d8_value_regular_identity h

theorem d8_simple_complete (V : FDRep ℂ (representative .d8)) [Simple V] :
    ∃ i : Fin 5, Nonempty (V ≅ d8RegisteredIrrep i) :=
  simple_complete_of_regular_character_identity d8RegisteredIrrep
    d8RegisteredIrrep_regular_identity V

end PermanentalDominance.N4
