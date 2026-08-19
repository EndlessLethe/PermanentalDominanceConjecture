import PermanentalDominance.N4.D8Realization
import PermanentalDominance.N4.A4Realization

/-!
# Concrete irreducible representations of `S₄`

The two-dimensional row is pulled back from the already verified standard representation of
`S₃` along the action of `S₄` on the three nonidentity elements of its normal Klein four group.
The quotient map is certified on the finite permutation group itself.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

local instance : Fintype (representative .s4) := Fintype.ofFinite _
local instance : Fintype (representative .s3) := Fintype.ofFinite _

private def s4d0 : S4 := ConcretePerm.double01_23
private def s4d1 : S4 := ConcretePerm.double02_13

private def s4PairImage (σ d : S4) : Fin 3 :=
  let x := σ * d * σ⁻¹
  if x = s4d0 then 0 else if x = s4d1 then 1 else 2

/-- The permutation of the three double transpositions, written in the chosen concrete copy of
`S₃` (the permutations fixing `3`). -/
private def s4ToS3Raw (σ : S4) : S4 :=
  let a := s4PairImage σ s4d0
  let b := s4PairImage σ s4d1
  if a = 0 ∧ b = 1 then 1
  else if a = 1 ∧ b = 2 then ConcretePerm.cycle012
  else if a = 2 ∧ b = 0 then ConcretePerm.cycle012 ^ 2
  else if a = 1 ∧ b = 0 then ConcretePerm.t01
  else if a = 0 ∧ b = 2 then ConcretePerm.t01 * ConcretePerm.cycle012
  else ConcretePerm.t01 * ConcretePerm.cycle012 ^ 2

private theorem s4ToS3Raw_mem (σ : S4) :
    s4ToS3Raw σ ∈ representativeCarrier .s3 := by
  native_decide +revert

private theorem s4ToS3Raw_one : s4ToS3Raw 1 = 1 := by
  native_decide

private theorem s4ToS3Raw_mul :
    ∀ σ τ : S4, s4ToS3Raw (σ * τ) = s4ToS3Raw σ * s4ToS3Raw τ := by
  native_decide

/-- The quotient homomorphism `S₄ → S₃` with kernel the normal Klein four subgroup. -/
def s4ToS3 : representative .s4 →* representative .s3 where
  toFun σ := ⟨s4ToS3Raw σ.1, by
    rw [mem_representative_iff]
    exact s4ToS3Raw_mem σ.1⟩
  map_one' := Subtype.ext s4ToS3Raw_one
  map_mul' σ τ := Subtype.ext (s4ToS3Raw_mul σ.1 τ.1)

private theorem s4ToS3Raw_range :
    ∀ y ∈ representativeCarrier .s3, ∃ x : S4, s4ToS3Raw x = y := by
  native_decide

theorem s4ToS3_surjective : Function.Surjective s4ToS3 := by
  intro y
  obtain ⟨x, hx⟩ := s4ToS3Raw_range y.1 ((mem_representative_iff .s3 y.1).mp y.2)
  have hxmem : x ∈ representative .s4 := by
    rw [mem_representative_iff]
    change x ∈ (Finset.univ : Finset S4)
    simp
  exact ⟨⟨x, hxmem⟩, Subtype.ext hx⟩

/-- Pull back an `H`-representation along a group homomorphism `G → H`. -/
def pullbackFDRep {G H : Type} [Group G] [Group H] (q : G →* H) (X : FDRep ℂ H) :
    FDRep ℂ G :=
  FDRep.of (X.ρ.comp q)

@[simp] theorem pullbackFDRep_rho {G H : Type} [Group G] [Group H]
    (q : G →* H) (X : FDRep ℂ H) (g : G) :
    (pullbackFDRep q X).ρ g = X.ρ (q g) := rfl

@[simp] theorem pullbackFDRep_finrank {G H : Type} [Group G] [Group H]
    (q : G →* H) (X : FDRep ℂ H) :
    Module.finrank ℂ (pullbackFDRep q X) = Module.finrank ℂ X := rfl

@[simp] theorem pullbackFDRep_character {G H : Type} [Group G] [Group H]
    (q : G →* H) (X : FDRep ℂ H) (g : G) :
    (pullbackFDRep q X).character g = X.character (q g) := rfl

/-! ## Simplicity under a surjective pullback -/

private def invariantSubRepresentation {H : Type} [Group H] (X : FDRep ℂ H)
    (p : Submodule ℂ X) (hp : ∀ h : H, ∀ x ∈ p, X.ρ h x ∈ p) :
    Representation ℂ H p where
    toFun := fun h => {
      toFun := fun x : p => ⟨X.ρ h x.1, hp h x.1 x.2⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp }
    map_one' := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change X.ρ 1 x.1 = x.1
      simp
    map_mul' := fun h k => by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change X.ρ (h * k) x.1 = X.ρ h (X.ρ k x.1)
      rw [map_mul]
      rfl

private def invariantSubFDRep {H : Type} [Group H] (X : FDRep ℂ H)
    (p : Submodule ℂ X) (hp : ∀ h : H, ∀ x ∈ p, X.ρ h x ∈ p) : FDRep ℂ H :=
  FDRep.of (invariantSubRepresentation X p hp)

private def invariantSubFDRepι {H : Type} [Group H] (X : FDRep ℂ H)
    (p : Submodule ℂ X) (hp : ∀ h : H, ∀ x ∈ p, X.ρ h x ∈ p) :
    invariantSubFDRep X p hp ⟶ X where
  hom := ModuleCat.ofHom (p.subtype : p →ₗ[ℂ] X)
  comm h := by
    ext x
    rfl

private theorem invariant_submodule_eq_top_of_simple {H : Type} [Group H]
    (X : FDRep ℂ H) [Simple X]
    (p : Submodule ℂ X) (hp : ∀ h : H, ∀ x ∈ p, X.ρ h x ∈ p)
    (hne : p ≠ ⊥) : p = ⊤ := by
  let P := invariantSubFDRep X p hp
  let ι : P ⟶ X := invariantSubFDRepι X p hp
  haveI : Mono ι := ConcreteCategory.mono_of_injective ι (by
    intro x y hxy
    exact Subtype.ext hxy)
  have hi : ι ≠ 0 := by
    intro hi0
    apply hne
    apply bot_unique
    intro x hx
    let xp : p := ⟨x, hx⟩
    have he := congrArg (fun f : P ⟶ X => f.hom.hom xp) hi0
    change x = 0 at he
    simpa using he
  haveI : IsIso ι := (Simple.mono_isIso_iff_nonzero ι).2 hi
  have hsurj : Function.Surjective ι :=
    (ConcreteCategory.bijective_of_isIso ι).2
  apply top_unique
  intro x hx
  obtain ⟨y, hy⟩ := hsurj x
  change p at y
  change (y : X) = x at hy
  rw [← hy]
  exact y.property

/-- Pullback along a surjective group homomorphism preserves irreducibility. -/
theorem pullbackFDRep_simple_of_surjective {G H : Type} [Group G] [Group H]
    (q : G →* H) (hq : Function.Surjective q) (X : FDRep ℂ H) [Simple X] :
    Simple (pullbackFDRep q X) where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) G
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 (pullbackFDRep q X) :
          pullbackFDRep q X ⟶ pullbackFDRep q X) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      haveI : Nontrivial X := not_subsingleton_iff_nontrivial.mp (by
        intro hsub
        apply CategoryTheory.id_nonzero X
        apply Action.Hom.ext
        ext x
        exact @Subsingleton.elim X hsub x 0)
      obtain ⟨x, hx⟩ := exists_ne (0 : X)
      have heval := congrArg
        (fun a : pullbackFDRep q X ⟶ pullbackFDRep q X => a.hom.hom x) hid
      have : x = 0 := by simpa using heval
      exact hx this
    · intro hnonzero
      have hlin : f.hom.hom ≠ 0 := by
        intro hzero
        apply hnonzero
        apply Action.Hom.ext
        exact ModuleCat.hom_ext hzero
      let p : Submodule ℂ X := LinearMap.range f.hom.hom
      have hstableG (g : G) (v : X) (hv : v ∈ p) : X.ρ (q g) v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ g y, ?_⟩
        have hc := congrArg
          (fun a : Y.V ⟶ (pullbackFDRep q X).V => a.hom y) (f.comm g)
        simpa using hc
      have hstableH (h : H) (v : X) (hv : v ∈ p) : X.ρ h v ∈ p := by
        obtain ⟨g, rfl⟩ := hq h
        exact hstableG g v hv
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := invariant_submodule_eq_top_of_simple X p hstableH hpne
      have hsurj : Function.Surjective f.hom.hom := LinearMap.range_eq_top.mp hp
      let U := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
      haveI : Mono (U.map f.hom) := by infer_instance
      have hinj : Function.Injective f.hom.hom :=
        (ModuleCat.mono_iff_injective (U.map f.hom)).1 inferInstance
      haveI : IsIso (U.map f.hom) :=
        (ConcreteCategory.isIso_iff_bijective (U.map f.hom)).2 ⟨hinj, hsurj⟩
      haveI : IsIso f.hom := isIso_of_reflects_iso f.hom U
      infer_instance

/-- The two-dimensional irreducible representation of `S₄`, inflated from `S₄/V₄ ≅ S₃`. -/
def s4TwoDimensionalFDRep : FDRep ℂ (representative .s4) :=
  pullbackFDRep s4ToS3 s3StandardFDRep

@[simp] theorem s4TwoDimensional_finrank : Module.finrank ℂ s4TwoDimensionalFDRep = 2 := by
  simp [s4TwoDimensionalFDRep]

instance s4_twoDimensional_simple : Simple s4TwoDimensionalFDRep :=
  pullbackFDRep_simple_of_surjective s4ToS3 s4ToS3_surjective s3StandardFDRep

private def s4TwoDimensionalIntValue (σ : S4) : ℤ :=
  if s4Class σ = 0 then 2 else if s4Class σ = 2 then 2
  else if s4Class σ = 3 then -1 else 0

private def s3StandardIntValue (σ : S4) : ℤ :=
  if s3Class σ = 0 then 2 else if s3Class σ = 2 then -1 else 0

private theorem s4_quotient_character_table :
    ∀ σ ∈ representativeCarrier .s4,
      s4TwoDimensionalIntValue σ = s3StandardIntValue (s4ToS3Raw σ) := by
  native_decide

theorem s4_twoDimensional_character :
    (rowOfIndex .s4 ⟨4, by decide⟩).coeff = s4TwoDimensionalFDRep.character := by
  funext h
  have h42 : (⟨4, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h43 : (⟨4, by decide⟩ : Fin 5) ≠ 3 := by decide
  have hs4 : (rowOfIndex .s4 ⟨4, by decide⟩).coeff h =
      (s4TwoDimensionalIntValue h.1 : ℂ) := by
    by_cases h0 : s4Class h.1 = 0 <;>
      by_cases h1 : s4Class h.1 = 1 <;>
      by_cases h2 : s4Class h.1 = 2 <;>
      by_cases h3 : s4Class h.1 = 3 <;>
      simp [rowOfIndex, s4Row, mkRow, s4TwoDimensionalIntValue,
        h42, h43, h0, h1, h2, h3]
  rw [hs4]
  unfold s4TwoDimensionalFDRep
  rw [pullbackFDRep_character]
  rw [← congrFun s3_standard_character (s4ToS3 h)]
  have hs3 : (rowOfIndex .s3 ⟨2, by decide⟩).coeff (s4ToS3 h) =
      (s3StandardIntValue (s4ToS3Raw h.1) : ℂ) := by
    simp [rowOfIndex, s3Row, mkRow, s3StandardIntValue, s4ToS3]
  rw [hs3]
  exact_mod_cast s4_quotient_character_table h.1 h.2

theorem s4_twoDimensional_degree : (rowOfIndex .s4 ⟨4, by decide⟩).degree = 2 := by
  have h4 : (⟨4, by decide⟩ : Fin 5) = 4 := by decide
  simp [rowOfIndex, s4Row, mkRow, h4]

/-! ## The three-dimensional standard representation -/

/-- Embed three coordinates into the four-dimensional sum-zero hyperplane. -/
def s4StandardEmbed (v : Fin 3 → ℂ) : Fin 4 → ℂ :=
  ![v 0, v 1, v 2, -(v 0 + v 1 + v 2)]

@[simp] theorem s4StandardEmbed_castSucc (v : Fin 3 → ℂ) (i : Fin 3) :
    s4StandardEmbed v i.castSucc = v i := by
  fin_cases i <;> rfl

@[simp] theorem s4StandardEmbed_last (v : Fin 3 → ℂ) :
    s4StandardEmbed v (Fin.last 3) = -∑ i, v i := by
  simp [s4StandardEmbed, Fin.sum_univ_three]

private theorem s4StandardEmbed_sum (v : Fin 3 → ℂ) :
    ∑ i : Fin 4, s4StandardEmbed v i = 0 := by
  simp [s4StandardEmbed, Fin.sum_univ_four]
  ring

private theorem s4StandardEmbed_add (x y : Fin 3 → ℂ) (j : Fin 4) :
    s4StandardEmbed (x + y) j = s4StandardEmbed x j + s4StandardEmbed y j := by
  fin_cases j <;> simp [s4StandardEmbed] <;> ring

private theorem s4StandardEmbed_smul (c : ℂ) (x : Fin 3 → ℂ) (j : Fin 4) :
    s4StandardEmbed (c • x) j = c * s4StandardEmbed x j := by
  fin_cases j <;> simp [s4StandardEmbed] <;> ring

/-- The standard action in zero-sum coordinates. -/
def s4StandardAct (σ : S4) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => s4StandardEmbed v (σ⁻¹ i.castSucc)

private theorem s4StandardEmbed_act (σ : S4) (v : Fin 3 → ℂ) (j : Fin 4) :
    s4StandardEmbed (s4StandardAct σ v) j = s4StandardEmbed v (σ⁻¹ j) := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · change -(s4StandardEmbed v (σ⁻¹ (0 : Fin 4)) +
        s4StandardEmbed v (σ⁻¹ (1 : Fin 4)) +
        s4StandardEmbed v (σ⁻¹ (2 : Fin 4))) =
      s4StandardEmbed v (σ⁻¹ (3 : Fin 4))
    have hsum : (∑ i : Fin 4, s4StandardEmbed v (σ⁻¹ i)) = 0 := by
      rw [Equiv.sum_comp (σ⁻¹) (fun i => s4StandardEmbed v i)]
      exact s4StandardEmbed_sum v
    rw [Fin.sum_univ_four] at hsum
    linear_combination - hsum

def s4StandardLin (σ : S4) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun := s4StandardAct σ
  map_add' x y := by
    ext i
    exact s4StandardEmbed_add x y _
  map_smul' c x := by
    ext i
    exact s4StandardEmbed_smul c x _

def s4StandardRepresentation : Representation ℂ (representative .s4) (Fin 3 → ℂ) where
  toFun σ := s4StandardLin σ.1
  map_one' := by
    apply LinearMap.ext
    intro v
    ext i
    simp [s4StandardLin, s4StandardAct]
  map_mul' σ τ := by
    apply LinearMap.ext
    intro v
    ext i
    change s4StandardEmbed v ((σ.1 * τ.1)⁻¹ i.castSucc) =
      s4StandardEmbed (s4StandardAct τ.1 v) (σ.1⁻¹ i.castSucc)
    rw [s4StandardEmbed_act]
    simp [mul_inv_rev]

def s4StandardFDRep : FDRep ℂ (representative .s4) := FDRep.of s4StandardRepresentation

@[simp] theorem s4Standard_finrank : Module.finrank ℂ s4StandardFDRep = 3 := by
  simp [s4StandardFDRep, s4StandardRepresentation, FDRep.of]

private def s4StandardDiagInt (σ : S4) (i : Fin 3) : ℤ :=
  if σ⁻¹ i.castSucc = Fin.last 3 then -1
  else if σ⁻¹ i.castSucc = i.castSucc then 1 else 0

private def s4StandardTraceInt (σ : S4) : ℤ :=
  ∑ i : Fin 3, s4StandardDiagInt σ i

private theorem s4StandardEmbed_basis (i : Fin 3) (j : Fin 4) :
    s4StandardEmbed (Pi.single i (1 : ℂ)) j =
      (if j = Fin.last 3 then (-1 : ℤ) else if j = i.castSucc then 1 else 0 : ℤ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [s4StandardEmbed, Pi.single_apply,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.last]
  all_goals decide

private theorem s4Standard_diagonal (σ : S4) (i : Fin 3) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Fin 3)) (Pi.basisFun ℂ (Fin 3))
      (s4StandardLin σ) i i = (s4StandardDiagInt σ i : ℤ) := by
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    s4StandardLin, s4StandardAct]
  change s4StandardAct σ (Pi.single i 1) i = _
  change s4StandardEmbed (Pi.single i 1) (σ⁻¹ i.castSucc) = _
  rw [s4StandardEmbed_basis]
  rfl

private theorem s4Standard_trace (σ : S4) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (s4StandardLin σ) =
      (s4StandardTraceInt σ : ℤ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 3)), Matrix.trace_fin_three]
  rw [s4Standard_diagonal, s4Standard_diagonal, s4Standard_diagonal]
  simp [s4StandardTraceInt, Fin.sum_univ_three]

private def s4RegisteredStandardInt (σ : S4) : ℤ :=
  if s4Class σ = 0 then 3 else if s4Class σ = 1 then 1
  else if s4Class σ = 2 then -1 else if s4Class σ = 3 then 0 else -1

private theorem s4_standard_trace_table :
    ∀ σ ∈ representativeCarrier .s4,
      s4StandardTraceInt σ = s4RegisteredStandardInt σ := by
  native_decide

theorem s4_standard_character :
    (rowOfIndex .s4 ⟨2, by decide⟩).coeff = s4StandardFDRep.character := by
  funext h
  have h20 : (⟨2, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h21 : (⟨2, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h22 : (⟨2, by decide⟩ : Fin 5) = 2 := rfl
  have h23 : (⟨2, by decide⟩ : Fin 5) ≠ 3 := by decide
  have h24 : (⟨2, by decide⟩ : Fin 5) ≠ 4 := by decide
  have hrow : (rowOfIndex .s4 ⟨2, by decide⟩).coeff h =
      (s4RegisteredStandardInt h.1 : ℂ) := by
    by_cases h0 : s4Class h.1 = 0 <;>
      by_cases h1 : s4Class h.1 = 1 <;>
      by_cases h2 : s4Class h.1 = 2 <;>
      by_cases h3 : s4Class h.1 = 3 <;>
      simp [rowOfIndex, s4Row, mkRow, s4RegisteredStandardInt,
        h20, h21, h22, h23, h24, h0, h1, h2, h3]
  rw [hrow]
  change (s4RegisteredStandardInt h.1 : ℂ) =
    LinearMap.trace ℂ (Fin 3 → ℂ) (s4StandardLin h.1)
  rw [s4Standard_trace]
  exact_mod_cast (s4_standard_trace_table h.1 h.2).symm

theorem s4_standard_degree : (rowOfIndex .s4 ⟨2, by decide⟩).degree = 3 := by
  have h20 : (⟨2, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h21 : (⟨2, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h24 : (⟨2, by decide⟩ : Fin 5) ≠ 4 := by decide
  simp [rowOfIndex, s4Row, mkRow, h20, h21, h24]

/-! ### Irreducibility of the standard representation -/

private theorem s4_every_perm_mem (σ : S4) : σ ∈ representative .s4 := by
  rw [mem_representative_iff]
  change σ ∈ (Finset.univ : Finset S4)
  simp

private def s4rElt : representative .s4 :=
  ⟨ConcretePerm.cycle012, s4_every_perm_mem ConcretePerm.cycle012⟩

private def s4dElt : representative .s4 :=
  ⟨ConcretePerm.double01_23, s4_every_perm_mem ConcretePerm.double01_23⟩

private theorem s4Standard_rho_r (v : Fin 3 → ℂ) :
    s4StandardFDRep.ρ s4rElt v = a4R v := by
  change s4StandardAct ConcretePerm.cycle012 v = a4R v
  rw [a4R_apply]
  ext i
  fin_cases i
  · change s4StandardEmbed v (ConcretePerm.cycle012⁻¹ (0 : Fin 4)) = v 2
    rw [show ConcretePerm.cycle012⁻¹ (0 : Fin 4) = 2 by native_decide]
    rfl
  · change s4StandardEmbed v (ConcretePerm.cycle012⁻¹ (1 : Fin 4)) = v 0
    rw [show ConcretePerm.cycle012⁻¹ (1 : Fin 4) = 0 by native_decide]
    rfl
  · change s4StandardEmbed v (ConcretePerm.cycle012⁻¹ (2 : Fin 4)) = v 1
    rw [show ConcretePerm.cycle012⁻¹ (2 : Fin 4) = 1 by native_decide]
    rfl

private theorem s4Standard_rho_d (v : Fin 3 → ℂ) :
    s4StandardFDRep.ρ s4dElt v = a4D v := by
  change s4StandardAct ConcretePerm.double01_23 v = a4D v
  rw [a4D_apply]
  ext i
  fin_cases i
  · change s4StandardEmbed v (ConcretePerm.double01_23⁻¹ (0 : Fin 4)) = v 1
    rw [show ConcretePerm.double01_23⁻¹ (0 : Fin 4) = 1 by native_decide]
    rfl
  · change s4StandardEmbed v (ConcretePerm.double01_23⁻¹ (1 : Fin 4)) = v 0
    rw [show ConcretePerm.double01_23⁻¹ (1 : Fin 4) = 0 by native_decide]
    rfl
  · change s4StandardEmbed v (ConcretePerm.double01_23⁻¹ (2 : Fin 4)) =
        -v 0 - v 1 - v 2
    rw [show ConcretePerm.double01_23⁻¹ (2 : Fin 4) = 3 by native_decide]
    simp [s4StandardEmbed]
    ring

private def s4E0 : Fin 3 → ℂ := ![1, 0, 0]

instance s4_standard_simple : Simple s4StandardFDRep where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) (representative .s4)
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 s4StandardFDRep : s4StandardFDRep ⟶ s4StandardFDRep) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      have heval := congrArg
        (fun q : s4StandardFDRep ⟶ s4StandardFDRep => q.hom.hom s4E0) hid
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
      have hstable (h : representative .s4) (v : Fin 3 → ℂ) (hv : v ∈ p) :
          s4StandardFDRep.ρ h v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ h y, ?_⟩
        have hc := congrArg (fun q : Y.V ⟶ s4StandardFDRep.V => q.hom y) (f.comm h)
        simpa using hc
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := a4_stable_under_R_D_eq_top p
        (fun v hv => by simpa [s4Standard_rho_r] using hstable s4rElt v hv)
        (fun v hv => by simpa [s4Standard_rho_d] using hstable s4dElt v hv)
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

/-! ## The sign twist of the standard representation -/

/-- The standard representation tensored with the permutation sign. -/
def s4SignTwistedLin (h : representative .s4) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  (permutationSignUnitCharacter (representative .s4) h : ℂ) • s4StandardLin h.1

def s4SignTwistedRepresentation :
    Representation ℂ (representative .s4) (Fin 3 → ℂ) where
  toFun := s4SignTwistedLin
  map_one' := by
    apply LinearMap.ext
    intro v
    simp only [s4SignTwistedLin, map_one, Units.val_one, one_smul]
    change s4StandardLin (1 : S4) v = v
    exact LinearMap.congr_fun s4StandardRepresentation.map_one v
  map_mul' h k := by
    apply LinearMap.ext
    intro v
    have hstd : s4StandardLin (h.1 * k.1) v =
        s4StandardLin h.1 (s4StandardLin k.1 v) := by
      have hx := congrArg (fun L : Module.End ℂ (Fin 3 → ℂ) => L v)
        (s4StandardRepresentation.map_mul h k)
      exact hx
    change
      (permutationSignUnitCharacter (representative .s4) (h * k) : ℂ) •
          s4StandardLin (h.1 * k.1) v =
        (permutationSignUnitCharacter (representative .s4) h : ℂ) •
          s4StandardLin h.1
            ((permutationSignUnitCharacter (representative .s4) k : ℂ) •
              s4StandardLin k.1 v)
    rw [hstd]
    simp [mul_smul, mul_comm]

def s4SignTwistedFDRep : FDRep ℂ (representative .s4) :=
  FDRep.of s4SignTwistedRepresentation

@[simp] theorem s4SignTwisted_finrank : Module.finrank ℂ s4SignTwistedFDRep = 3 := by
  simp [s4SignTwistedFDRep, s4SignTwistedRepresentation, FDRep.of]

private def s4RegisteredTwistedInt (σ : S4) : ℤ :=
  Equiv.Perm.sign σ * s4RegisteredStandardInt σ

private theorem s4_twisted_row_table :
    ∀ σ ∈ representativeCarrier .s4,
      (if s4Class σ = 0 then 3 else if s4Class σ = 1 then -1
        else if s4Class σ = 2 then -1 else if s4Class σ = 3 then 0 else 1) =
        s4RegisteredTwistedInt σ := by
  native_decide

private theorem s4SignTwisted_trace (h : representative .s4) :
    s4SignTwistedFDRep.character h = (s4RegisteredTwistedInt h.1 : ℤ) := by
  change LinearMap.trace ℂ (Fin 3 → ℂ)
      ((permutationSignUnitCharacter (representative .s4) h : ℂ) •
        s4StandardLin h.1) = _
  rw [map_smul, s4Standard_trace,
    s4_standard_trace_table h.1 h.2, permutationSignUnitCharacter_apply]
  simp [s4RegisteredTwistedInt]

theorem s4_signTwisted_character :
    (rowOfIndex .s4 ⟨3, by decide⟩).coeff = s4SignTwistedFDRep.character := by
  funext h
  have h30 : (⟨3, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h31 : (⟨3, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h32 : (⟨3, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h33 : (⟨3, by decide⟩ : Fin 5) = 3 := rfl
  have h34 : (⟨3, by decide⟩ : Fin 5) ≠ 4 := by decide
  have hrow : (rowOfIndex .s4 ⟨3, by decide⟩).coeff h =
      ((if s4Class h.1 = 0 then 3 else if s4Class h.1 = 1 then -1
        else if s4Class h.1 = 2 then -1 else if s4Class h.1 = 3 then 0 else 1 : ℤ) : ℂ) := by
    by_cases h0 : s4Class h.1 = 0 <;>
      by_cases h1 : s4Class h.1 = 1 <;>
      by_cases h2 : s4Class h.1 = 2 <;>
      by_cases h3 : s4Class h.1 = 3 <;>
      simp [rowOfIndex, s4Row, mkRow, h30, h31, h32, h33, h34, h0, h1, h2, h3]
  rw [hrow, s4SignTwisted_trace]
  exact_mod_cast s4_twisted_row_table h.1 h.2

theorem s4_signTwisted_degree :
    (rowOfIndex .s4 ⟨3, by decide⟩).degree = 3 := by
  have h30 : (⟨3, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h31 : (⟨3, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h32 : (⟨3, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h33 : (⟨3, by decide⟩ : Fin 5) = 3 := rfl
  have h34 : (⟨3, by decide⟩ : Fin 5) ≠ 4 := by decide
  simp [rowOfIndex, s4Row, mkRow, h30, h31, h32, h33, h34]

private theorem s4SignTwisted_rho_r (v : Fin 3 → ℂ) :
    s4SignTwistedFDRep.ρ s4rElt v = a4R v := by
  change (permutationSignUnitCharacter (representative .s4) s4rElt : ℂ) •
      s4StandardLin ConcretePerm.cycle012 v = a4R v
  have hs : Equiv.Perm.sign ConcretePerm.cycle012 = 1 := by native_decide
  have hs' : Equiv.Perm.sign s4rElt.1 = 1 := by simpa [s4rElt] using hs
  rw [permutationSignUnitCharacter_apply, hs']
  norm_num
  change s4StandardAct ConcretePerm.cycle012 v = ![v 2, v 0, v 1]
  rw [← a4R_apply]
  have hr := s4Standard_rho_r v
  change s4StandardAct ConcretePerm.cycle012 v = a4R v at hr
  exact hr

private theorem s4SignTwisted_rho_d (v : Fin 3 → ℂ) :
    s4SignTwistedFDRep.ρ s4dElt v = a4D v := by
  change (permutationSignUnitCharacter (representative .s4) s4dElt : ℂ) •
      s4StandardLin ConcretePerm.double01_23 v = a4D v
  have hs : Equiv.Perm.sign ConcretePerm.double01_23 = 1 := by native_decide
  have hs' : Equiv.Perm.sign s4dElt.1 = 1 := by simpa [s4dElt] using hs
  rw [permutationSignUnitCharacter_apply, hs']
  norm_num
  change s4StandardAct ConcretePerm.double01_23 v =
    ![v 1, v 0, -v 0 - v 1 - v 2]
  rw [← a4D_apply]
  have hd := s4Standard_rho_d v
  change s4StandardAct ConcretePerm.double01_23 v = a4D v at hd
  exact hd

instance s4_signTwisted_simple : Simple s4SignTwistedFDRep where
  mono_isIso_iff_nonzero := by
    classical
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) (representative .s4)
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : Epi f := by infer_instance
      intro hzero
      have hid : (𝟙 s4SignTwistedFDRep :
          s4SignTwistedFDRep ⟶ s4SignTwistedFDRep) = 0 := by
        apply (cancel_epi f).1
        simp [hzero]
      have heval := congrArg
        (fun q : s4SignTwistedFDRep ⟶ s4SignTwistedFDRep => q.hom.hom s4E0) hid
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
      have hstable (h : representative .s4) (v : Fin 3 → ℂ) (hv : v ∈ p) :
          s4SignTwistedFDRep.ρ h v ∈ p := by
        rcases hv with ⟨y, rfl⟩
        refine ⟨Y.ρ h y, ?_⟩
        have hc := congrArg
          (fun q : Y.V ⟶ s4SignTwistedFDRep.V => q.hom y) (f.comm h)
        simpa using hc
      have hpne : p ≠ ⊥ := by
        intro hp
        apply hlin
        ext y
        have hm : f.hom.hom y ∈ p := ⟨y, rfl⟩
        rw [hp] at hm
        simpa using hm
      have hp : p = ⊤ := a4_stable_under_R_D_eq_top p
        (fun v hv => by simpa [s4SignTwisted_rho_r] using hstable s4rElt v hv)
        (fun v hv => by simpa [s4SignTwisted_rho_d] using hstable s4dElt v hv)
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

/-! ## Registered family and exhaustion -/

/-- The five concrete irreducible `S₄` representations, in character-table order. -/
def s4RegisteredIrrep (i : Fin 5) : FDRep ℂ (representative .s4) :=
  if i = 0 then oneDimensionalFDRep (trivialUnitCharacter (representative .s4))
  else if i = 1 then
    oneDimensionalFDRep (permutationSignUnitCharacter (representative .s4))
  else if i = 2 then s4StandardFDRep
  else if i = 3 then s4SignTwistedFDRep
  else s4TwoDimensionalFDRep

instance s4RegisteredIrrep_simple (i : Fin 5) : Simple (s4RegisteredIrrep i) := by
  fin_cases i <;> simp [s4RegisteredIrrep] <;> infer_instance

theorem s4RegisteredIrrep_character (i : Fin 5) :
    (rowOfIndex .s4 i).coeff = (s4RegisteredIrrep i).character := by
  fin_cases i
  · simpa [s4RegisteredIrrep] using rowZero_character .s4
  · simpa [s4RegisteredIrrep] using s4_sign_character
  · simpa [s4RegisteredIrrep] using s4_standard_character
  · simpa [s4RegisteredIrrep] using s4_signTwisted_character
  · simpa [s4RegisteredIrrep] using s4_twoDimensional_character

theorem s4RegisteredIrrep_degree (i : Fin 5) :
    (rowOfIndex .s4 i).degree =
      (Module.finrank ℂ (s4RegisteredIrrep i) : ℂ) := by
  fin_cases i
  · simpa [s4RegisteredIrrep] using rowZero_degree .s4
  · simpa [s4RegisteredIrrep] using s4_sign_degree
  · simpa [s4RegisteredIrrep] using s4_standard_degree
  · simpa [s4RegisteredIrrep] using s4_signTwisted_degree
  · simpa [s4RegisteredIrrep] using s4_twoDimensional_degree

private theorem s4_card : Fintype.card (representative .s4) = 24 := by
  let e : representative .s4 ≃ {x // x ∈ representativeCarrier .s4} := {
    toFun x := ⟨x.1, (mem_representative_iff .s4 x.1).mp x.2⟩
    invFun x := ⟨x.1, (mem_representative_iff .s4 x.1).mpr x.2⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  calc
    Fintype.card (representative .s4) =
        Fintype.card {x // x ∈ representativeCarrier .s4} := Fintype.card_congr e
    _ = (representativeCarrier .s4).card := Fintype.card_coe _
    _ = 24 := by native_decide

private theorem s4_regular_integer_table :
    ∀ σ ∈ representativeCarrier .s4,
      (1 : ℤ) + (if s4Class σ = 1 ∨ s4Class σ = 4 then -1 else 1) +
        3 * (if s4Class σ = 0 then 3 else if s4Class σ = 1 then 1
          else if s4Class σ = 2 then -1 else if s4Class σ = 3 then 0 else -1) +
        3 * (if s4Class σ = 0 then 3 else if s4Class σ = 1 then -1
          else if s4Class σ = 2 then -1 else if s4Class σ = 3 then 0 else 1) +
        2 * (if s4Class σ = 0 then 2 else if s4Class σ = 1 then 0
          else if s4Class σ = 2 then 2 else if s4Class σ = 3 then -1 else 0) =
        if σ = 1 then 24 else 0 := by
  native_decide

private theorem s4_registered_regular_identity (h : representative .s4) :
    (rowOfIndex .s4 ⟨0, by decide⟩).coeff h +
      (rowOfIndex .s4 ⟨1, by decide⟩).coeff h +
      3 * (rowOfIndex .s4 ⟨2, by decide⟩).coeff h +
      3 * (rowOfIndex .s4 ⟨3, by decide⟩).coeff h +
      2 * (rowOfIndex .s4 ⟨4, by decide⟩).coeff h =
        if h = 1 then 24 else 0 := by
  have h00 : (⟨0, by decide⟩ : Fin 5) = 0 := rfl
  have h10 : (⟨1, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h11 : (⟨1, by decide⟩ : Fin 5) = 1 := rfl
  have h20 : (⟨2, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h21 : (⟨2, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h22 : (⟨2, by decide⟩ : Fin 5) = 2 := rfl
  have h30 : (⟨3, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h31 : (⟨3, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h32 : (⟨3, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h33 : (⟨3, by decide⟩ : Fin 5) = 3 := rfl
  have h40 : (⟨4, by decide⟩ : Fin 5) ≠ 0 := by decide
  have h41 : (⟨4, by decide⟩ : Fin 5) ≠ 1 := by decide
  have h42 : (⟨4, by decide⟩ : Fin 5) ≠ 2 := by decide
  have h43 : (⟨4, by decide⟩ : Fin 5) ≠ 3 := by decide
  simp only [rowOfIndex, s4Row, mkRow, h00, h10, h11, h20, h21, h22,
    h30, h31, h32, h33, h40, h41, h42, h43, if_pos, if_neg]
  have n10 : (1 : Fin 5) ≠ 0 := by decide
  have n20 : (2 : Fin 5) ≠ 0 := by decide
  have n21 : (2 : Fin 5) ≠ 1 := by decide
  have n30 : (3 : Fin 5) ≠ 0 := by decide
  have n31 : (3 : Fin 5) ≠ 1 := by decide
  have n32 : (3 : Fin 5) ≠ 2 := by decide
  simp only [n10, n20, n21, n30, n31, n32, if_neg, if_false]
  change (1 : ℂ) + (if s4Class h.1 = 1 ∨ s4Class h.1 = 4 then -1 else 1) +
      3 * (if s4Class h.1 = 0 then 3 else if s4Class h.1 = 1 then 1
        else if s4Class h.1 = 2 then -1 else if s4Class h.1 = 3 then 0 else -1) +
      3 * (if s4Class h.1 = 0 then 3 else if s4Class h.1 = 1 then -1
        else if s4Class h.1 = 2 then -1 else if s4Class h.1 = 3 then 0 else 1) +
      2 * (if s4Class h.1 = 0 then 2 else if s4Class h.1 = 1 then 0
        else if s4Class h.1 = 2 then 2 else if s4Class h.1 = 3 then -1 else 0) =
      if h = 1 then 24 else 0
  have hv := s4_regular_integer_table h.1 h.2
  have heq : (h = 1) ↔ (h.1 = 1) := by
    constructor
    · exact fun hh => congrArg Subtype.val hh
    · exact fun hh => Subtype.ext hh
  simp only [heq]
  exact_mod_cast hv

theorem s4RegisteredIrrep_regular_identity (h : representative .s4) :
    ∑ i : Fin 5, (Module.finrank ℂ (s4RegisteredIrrep i) : ℂ) *
        (s4RegisteredIrrep i).character h =
      if h = 1 then (Fintype.card (representative .s4) : ℂ) else 0 := by
  rw [Fin.sum_univ_five]
  change
    (Module.finrank ℂ (oneDimensionalFDRep
      (trivialUnitCharacter (representative .s4))) : ℂ) *
        (oneDimensionalFDRep
          (trivialUnitCharacter (representative .s4))).character h +
    (Module.finrank ℂ (oneDimensionalFDRep
      (permutationSignUnitCharacter (representative .s4))) : ℂ) *
        (oneDimensionalFDRep
          (permutationSignUnitCharacter (representative .s4))).character h +
    (Module.finrank ℂ s4StandardFDRep : ℂ) * s4StandardFDRep.character h +
    (Module.finrank ℂ s4SignTwistedFDRep : ℂ) * s4SignTwistedFDRep.character h +
    (Module.finrank ℂ s4TwoDimensionalFDRep : ℂ) *
      s4TwoDimensionalFDRep.character h = _
  rw [oneDimensionalFDRep_finrank, oneDimensionalFDRep_finrank,
    s4Standard_finrank, s4SignTwisted_finrank, s4TwoDimensional_finrank]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  rw [← rowZero_character .s4, ← s4_sign_character, ← s4_standard_character,
    ← s4_signTwisted_character, ← s4_twoDimensional_character, s4_card]
  exact s4_registered_regular_identity h

/-- Every simple complex representation of the concrete `S₄` representative occurs in the
five-row registered family. -/
theorem s4_simple_complete (V : FDRep ℂ (representative .s4)) [Simple V] :
    ∃ i : Fin 5, Nonempty (V ≅ s4RegisteredIrrep i) :=
  simple_complete_of_regular_character_identity s4RegisteredIrrep
    s4RegisteredIrrep_regular_identity V

end PermanentalDominance.N4
