import PermanentalDominance.N4.AbelianCompleteness
import PermanentalDominance.N4.RegisteredCompleteness

/-!
# Concrete irreducibles for the nonabelian representatives

This module begins the nonabelian realization layer with the canonical sign representations.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

local instance (k : SubgroupKind) : Fintype (representative k) := Fintype.ofFinite _

/-- Cast an integral unit (`1` or `-1`) to a complex unit. -/
def intUnitToComplexUnit : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ)

/-- Restriction of the permutation sign to a concrete subgroup. -/
def permutationSignUnitCharacter (H : Subgroup S4) : H →* ℂˣ :=
  intUnitToComplexUnit.comp (Equiv.Perm.sign.comp H.subtype)

@[simp] theorem permutationSignUnitCharacter_apply (H : Subgroup S4) (h : H) :
    (permutationSignUnitCharacter H h : ℂ) = (Equiv.Perm.sign h.1 : ℤ) := by
  rfl

private theorem s3_sign_table :
    ∀ σ ∈ representativeCarrier .s3,
      Equiv.Perm.sign σ = if s3Class σ = 1 then -1 else 1 := by
  native_decide

theorem s3_sign_character :
    (rowOfIndex .s3 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep (permutationSignUnitCharacter (representative .s3))).character := by
  funext h
  rw [oneDimensionalFDRep_character, permutationSignUnitCharacter_apply]
  have hs := s3_sign_table h.1 h.2
  change (if s3Class h.1 = 1 then -1 else 1 : ℂ) = (Equiv.Perm.sign h.1 : ℤ)
  rw [hs]
  split <;> norm_num

theorem s3_sign_degree : (rowOfIndex .s3 ⟨1, by decide⟩).degree = 1 := by
  have hne : (⟨1, by decide⟩ : Fin 3) ≠ 2 := by decide
  simp [rowOfIndex, s3Row, mkRow, hne]

instance s3_sign_simple :
    Simple (oneDimensionalFDRep (permutationSignUnitCharacter (representative .s3))) :=
  oneDimensionalFDRep_simple _

private theorem s4_sign_table :
    ∀ σ ∈ representativeCarrier .s4,
      Equiv.Perm.sign σ = if s4Class σ = 1 ∨ s4Class σ = 4 then -1 else 1 := by
  native_decide

theorem s4_sign_character :
    (rowOfIndex .s4 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep (permutationSignUnitCharacter (representative .s4))).character := by
  funext h
  rw [oneDimensionalFDRep_character, permutationSignUnitCharacter_apply]
  have hs := s4_sign_table h.1 h.2
  change (if s4Class h.1 = 1 ∨ s4Class h.1 = 4 then -1 else 1 : ℂ) =
    (Equiv.Perm.sign h.1 : ℤ)
  rw [hs]
  split <;> norm_num

theorem s4_sign_degree : (rowOfIndex .s4 ⟨1, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, s4Row, mkRow]

instance s4_sign_simple :
    Simple (oneDimensionalFDRep (permutationSignUnitCharacter (representative .s4))) :=
  oneDimensionalFDRep_simple _

/-! ## The two-dimensional standard representation of `S₃` -/

private def s3r : S4 := ConcretePerm.cycle012
private def s3s : S4 := ConcretePerm.t01

private def s3ExplicitCarrier : Finset S4 :=
  {1, s3r, s3r ^ 2, s3s, s3s * s3r, s3s * s3r ^ 2}

private theorem s3_carrier_eq_explicit : representativeCarrier .s3 = s3ExplicitCarrier := by
  native_decide

private def s3e (x : S4) (hx : x ∈ s3ExplicitCarrier) : representative .s3 :=
  ⟨x, by simpa [s3_carrier_eq_explicit] using hx⟩

private def s3R : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![-v 1, v 0 - v 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

private def s3S : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, v 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

private def s3Raw : Fin 6 → S4
  | 0 => 1
  | 1 => s3r
  | 2 => s3r ^ 2
  | 3 => s3s
  | 4 => s3s * s3r
  | 5 => s3s * s3r ^ 2

private def s3Index (x : S4) : Fin 6 :=
  if x = 1 then 0 else if x = s3r then 1 else if x = s3r ^ 2 then 2
  else if x = s3s then 3 else if x = s3s * s3r then 4 else 5

private def s3MulIndex : Fin 6 → Fin 6 → Fin 6
  | 0, j => j
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => 5 | 1, 4 => 3 | 1, 5 => 4
  | 2, 0 => 2 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 4 | 2, 4 => 5 | 2, 5 => 3
  | 3, 0 => 3 | 3, 1 => 4 | 3, 2 => 5 | 3, 3 => 0 | 3, 4 => 1 | 3, 5 => 2
  | 4, 0 => 4 | 4, 1 => 5 | 4, 2 => 3 | 4, 3 => 2 | 4, 4 => 0 | 4, 5 => 1
  | 5, 0 => 5 | 5, 1 => 3 | 5, 2 => 4 | 5, 3 => 1 | 5, 4 => 2 | 5, 5 => 0

private def s3LinByIndex : Fin 6 → (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)
  | 0 => LinearMap.id
  | 1 => s3R
  | 2 => s3R * s3R
  | 3 => s3S
  | 4 => s3S * s3R
  | 5 => s3S * (s3R * s3R)

private theorem s3_index_one : s3Index 1 = 0 := by native_decide

private theorem s3_index_mul_on_carrier :
    ∀ a ∈ representativeCarrier .s3, ∀ b ∈ representativeCarrier .s3,
      s3Index (a * b) = s3MulIndex (s3Index a) (s3Index b) := by
  native_decide

private theorem s3LinByIndex_mul (i j : Fin 6) :
    s3LinByIndex (s3MulIndex i j) = s3LinByIndex i * s3LinByIndex j := by
  fin_cases i <;> fin_cases j <;>
    ext v k <;> fin_cases k <;> norm_num [s3MulIndex, s3LinByIndex, s3R, s3S] <;> ring

private theorem s3_exhaust_subtype (h : representative .s3) :
    h = s3e 1 (by native_decide) ∨
    h = s3e s3r (by native_decide) ∨
    h = s3e (s3r ^ 2) (by native_decide) ∨
    h = s3e s3s (by native_decide) ∨
    h = s3e (s3s * s3r) (by native_decide) ∨
    h = s3e (s3s * s3r ^ 2) (by native_decide) := by
  have hh : h.1 ∈ s3ExplicitCarrier := by
    rw [← s3_carrier_eq_explicit]
    exact h.2
  simp only [s3ExplicitCarrier, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh | hh | hh | hh
  all_goals
    first
    | exact Or.inl (Subtype.ext hh)
    | exact Or.inr (Or.inl (Subtype.ext hh))
    | exact Or.inr (Or.inr (Or.inl (Subtype.ext hh)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext hh))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext hh)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext hh)))))

def s3StandardRepresentation : Representation ℂ (representative .s3) (Fin 2 → ℂ) where
  toFun h := s3LinByIndex (s3Index h.1)
  map_one' := by
    change s3LinByIndex (s3Index (1 : S4)) = 1
    rw [s3_index_one]
    rfl
  map_mul' h k := by
    change s3LinByIndex (s3Index (h.1 * k.1)) =
      s3LinByIndex (s3Index h.1) * s3LinByIndex (s3Index k.1)
    rw [s3_index_mul_on_carrier h.1 h.2 k.1 k.2]
    exact s3LinByIndex_mul _ _

def s3StandardFDRep : FDRep ℂ (representative .s3) :=
  FDRep.of s3StandardRepresentation

@[simp] theorem s3Standard_finrank : Module.finrank ℂ s3StandardFDRep = 2 := by
  simp [s3StandardFDRep, s3StandardRepresentation, FDRep.of]

private def s3TraceValue : Fin 6 → ℤ
  | 0 => 2 | 1 => -1 | 2 => -1 | 3 => 0 | 4 => 0 | 5 => 0

private theorem s3LinByIndex_trace (i : Fin 6) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (s3LinByIndex i) = (s3TraceValue i : ℂ) := by
  fin_cases i <;>
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2))] <;>
    rw [Matrix.trace_fin_two] <;>
    norm_num [s3TraceValue, s3LinByIndex, s3R, s3S, LinearMap.toMatrix_apply,
      Pi.basisFun_apply] <;> ring

private def s3RegisteredStandardValue (x : S4) : ℤ :=
  if s3Class x = 0 then 2 else if s3Class x = 2 then -1 else 0

private theorem s3_trace_value_table :
    ∀ x ∈ representativeCarrier .s3,
      s3TraceValue (s3Index x) = s3RegisteredStandardValue x := by
  native_decide

theorem s3_standard_character :
    (rowOfIndex .s3 ⟨2, by decide⟩).coeff = s3StandardFDRep.character := by
  funext h
  change (if s3Class h.1 = 0 then 2 else if s3Class h.1 = 2 then -1 else 0 : ℂ) =
    LinearMap.trace ℂ (Fin 2 → ℂ) (s3LinByIndex (s3Index h.1))
  rw [s3LinByIndex_trace]
  have hv := s3_trace_value_table h.1 h.2
  rw [hv]
  simp [s3RegisteredStandardValue]

theorem s3_standard_degree : (rowOfIndex .s3 ⟨2, by decide⟩).degree = 2 := by
  have heq : (⟨2, by decide⟩ : Fin 3) = 2 := by decide
  simp [rowOfIndex, s3Row, mkRow, heq]

/-! ### Irreducibility and completeness for `S₃` -/

private def s3rElt : representative .s3 := s3e s3r (by native_decide)
private def s3sElt : representative .s3 := s3e s3s (by native_decide)

private theorem s3Standard_rho_r (v : Fin 2 → ℂ) :
    s3StandardFDRep.ρ s3rElt v = s3R v := by
  change s3LinByIndex (s3Index s3r) v = s3R v
  rw [show s3Index s3r = 1 by native_decide]
  rfl

private theorem s3Standard_rho_s (v : Fin 2 → ℂ) :
    s3StandardFDRep.ρ s3sElt v = s3S v := by
  change s3LinByIndex (s3Index s3s) v = s3S v
  rw [show s3Index s3s = 3 by native_decide]
  rfl

private def s3E0 : Fin 2 → ℂ := ![1, 0]
private def s3E1 : Fin 2 → ℂ := ![0, 1]

/-- A nonzero subspace of the standard plane which is stable under the two standard
generators is the whole plane.  This is the concrete irreducibility calculation used below. -/
private theorem s3_stable_range_eq_top
    (p : Submodule ℂ (Fin 2 → ℂ))
    (hR : ∀ v ∈ p, s3R v ∈ p)
    (hS : ∀ v ∈ p, s3S v ∈ p)
    (hne : p ≠ ⊥) : p = ⊤ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff p).mp hne
  have hSv : s3S v ∈ p := hS v hv
  by_cases ha : v 0 + v 1 = 0
  · have hy : v 1 = -v 0 := by linear_combination ha
    have hx : v 0 ≠ 0 := by
      intro hx
      apply hv0
      funext i
      fin_cases i
      · exact hx
      · simpa [hy, hx]
    have hRv : s3R v ∈ p := hR v hv
    have hd : s3R v - v ∈ p := p.sub_mem hRv hv
    have he1 : s3E1 ∈ p := by
      have hs := p.smul_mem ((3 * v 0)⁻¹) hd
      convert hs using 1
      ext i
      fin_cases i <;>
        simp [s3E1, s3R, hy, hx, Pi.smul_apply, Matrix.vecHead, Matrix.vecTail] <;>
        try (field_simp [hx] <;> ring)
    have he0 : s3E0 ∈ p := by
      have := hS s3E1 he1
      simpa [s3E0, s3E1, s3S] using this
    apply top_unique
    intro z hz
    have hz' := p.add_mem (p.smul_mem (z 0) he0) (p.smul_mem (z 1) he1)
    convert hz' using 1
    ext i
    fin_cases i <;> simp [s3E0, s3E1, Pi.smul_apply]
  · have hsum : v + s3S v ∈ p := p.add_mem hv hSv
    have hRsum : s3R (v + s3S v) ∈ p := hR _ hsum
    have hden : -v 0 - v 1 ≠ 0 := by
      intro hz
      apply ha
      linear_combination -hz
    have he0 : s3E0 ∈ p := by
      have hs := p.smul_mem (-(v 0 + v 1))⁻¹ hRsum
      convert hs using 1
      ext i
      fin_cases i
      · simp [s3E0, s3R, s3S, Pi.smul_apply, ha, Matrix.vecHead, Matrix.vecTail]
        have hcomm₁ : -v 1 + -v 0 = -v 0 - v 1 := by ring
        have hcomm₂ : -v 0 + -v 1 = -v 0 - v 1 := by ring
        rw [hcomm₁, hcomm₂]
        exact (inv_mul_cancel₀ hden).symm
      · simp [s3E0, s3R, s3S, Pi.smul_apply, ha, hden, Matrix.vecHead,
          Matrix.vecTail]
        exact Or.inr (by ring)
    have he1 : s3E1 ∈ p := by
      have := hS s3E0 he0
      simpa [s3E0, s3E1, s3S] using this
    apply top_unique
    intro z hz
    have hz' := p.add_mem (p.smul_mem (z 0) he0) (p.smul_mem (z 1) he1)
    convert hz' using 1
    ext i
    fin_cases i <;> simp [s3E0, s3E1, Pi.smul_apply]

instance s3_standard_simple : Simple s3StandardFDRep where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) (representative .s3)
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 s3StandardFDRep : s3StandardFDRep ⟶ s3StandardFDRep) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      have heval := congrArg
        (fun q : s3StandardFDRep ⟶ s3StandardFDRep => q.hom.hom s3E0) hid
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
      have hstable (h : representative .s3) (v : Fin 2 → ℂ) (hv : v ∈ p) :
          s3StandardFDRep.ρ h v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ h y, ?_⟩
        have hc := congrArg (fun q : Y.V ⟶ s3StandardFDRep.V => q.hom y) (f.comm h)
        simpa using hc
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := s3_stable_range_eq_top p
        (fun v hv => by simpa [s3Standard_rho_r] using hstable s3rElt v hv)
        (fun v hv => by simpa [s3Standard_rho_s] using hstable s3sElt v hv) hpne
      have hsurj : Function.Surjective f.hom.hom := LinearMap.range_eq_top.mp hp
      let U := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
      haveI : Mono (U.map f.hom) := by infer_instance
      have hinj : Function.Injective f.hom.hom :=
        (ModuleCat.mono_iff_injective (U.map f.hom)).1 inferInstance
      haveI : IsIso (U.map f.hom) :=
        (ConcreteCategory.isIso_iff_bijective (U.map f.hom)).2 ⟨hinj, hsurj⟩
      haveI : IsIso f.hom := isIso_of_reflects_iso f.hom U
      infer_instance

/-! ### Exhaustion of the irreducibles of `S₃` -/

/-- The three concrete irreducible representations indexed in table order. -/
def s3RegisteredIrrep (i : Fin 3) : FDRep ℂ (representative .s3) :=
  if i = 0 then oneDimensionalFDRep (trivialUnitCharacter (representative .s3))
  else if i = 1 then
    oneDimensionalFDRep (permutationSignUnitCharacter (representative .s3))
  else s3StandardFDRep

instance s3RegisteredIrrep_simple (i : Fin 3) : Simple (s3RegisteredIrrep i) := by
  fin_cases i <;> simp [s3RegisteredIrrep] <;> infer_instance

private theorem s3_card : Fintype.card (representative .s3) = 6 := by
  let e : representative .s3 ≃ {x // x ∈ representativeCarrier .s3} := {
    toFun x := ⟨x.1, (mem_representative_iff .s3 x.1).mp x.2⟩
    invFun x := ⟨x.1, (mem_representative_iff .s3 x.1).mpr x.2⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  calc
    Fintype.card (representative .s3) =
        Fintype.card {x // x ∈ representativeCarrier .s3} := Fintype.card_congr e
    _ = (representativeCarrier .s3).card := Fintype.card_coe _
    _ = 6 := by native_decide

private theorem s3_regular_integer_table :
    ∀ σ ∈ representativeCarrier .s3,
      (1 : ℤ) + (if s3Class σ = 1 then -1 else 1) +
          2 * (if s3Class σ = 0 then 2 else if s3Class σ = 2 then -1 else 0) =
        if σ = 1 then 6 else 0 := by
  native_decide

private theorem s3_registered_regular_identity (h : representative .s3) :
    (rowOfIndex .s3 ⟨0, by decide⟩).coeff h +
      (rowOfIndex .s3 ⟨1, by decide⟩).coeff h +
      2 * (rowOfIndex .s3 ⟨2, by decide⟩).coeff h =
        if h = 1 then 6 else 0 := by
  change (1 : ℂ) + (if s3Class h.1 = 1 then -1 else 1) +
      2 * (if s3Class h.1 = 0 then 2 else if s3Class h.1 = 2 then -1 else 0) =
    if h = 1 then 6 else 0
  have hv := s3_regular_integer_table h.1 h.2
  have heq : (h = 1) ↔ (h.1 = 1) := by
    constructor
    · exact fun hh => congrArg Subtype.val hh
    · exact fun hh => Subtype.ext hh
  simp only [heq]
  exact_mod_cast hv

theorem s3RegisteredIrrep_regular_identity (h : representative .s3) :
    ∑ i : Fin 3, (Module.finrank ℂ (s3RegisteredIrrep i) : ℂ) *
        (s3RegisteredIrrep i).character h =
      if h = 1 then (Fintype.card (representative .s3) : ℂ) else 0 := by
  rw [Fin.sum_univ_three]
  change
    (Module.finrank ℂ (oneDimensionalFDRep
        (trivialUnitCharacter (representative .s3))) : ℂ) *
        (oneDimensionalFDRep
          (trivialUnitCharacter (representative .s3))).character h +
      (Module.finrank ℂ (oneDimensionalFDRep
        (permutationSignUnitCharacter (representative .s3))) : ℂ) *
        (oneDimensionalFDRep
          (permutationSignUnitCharacter (representative .s3))).character h +
      (Module.finrank ℂ s3StandardFDRep : ℂ) * s3StandardFDRep.character h = _
  rw [oneDimensionalFDRep_finrank, oneDimensionalFDRep_finrank, s3Standard_finrank]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  rw [← rowZero_character .s3, ← s3_sign_character, ← s3_standard_character, s3_card]
  exact s3_registered_regular_identity h

/-- Every simple complex representation of the concrete `S₃` representative is one of the
three registered representations. -/
theorem s3_simple_complete (V : FDRep ℂ (representative .s3)) [Simple V] :
    ∃ i : Fin 3, Nonempty (V ≅ s3RegisteredIrrep i) :=
  simple_complete_of_regular_character_identity s3RegisteredIrrep
    s3RegisteredIrrep_regular_identity V

end PermanentalDominance.N4
