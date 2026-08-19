import PermanentalDominance.N4.CharacterTables
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Realization of the registered rows by finite-dimensional representations

This module starts with the common construction used by every one-dimensional row.  The remaining
nonabelian standard representations and the completeness argument are developed on top of this
interface; no analytic inequality is imported here.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

/-- The one-dimensional representation associated with a multiplicative complex coefficient. -/
def oneDimensionalRepresentation {H : Type} [Group H] (chiUnit : H →* ℂˣ) :
    Representation ℂ H ℂ where
  toFun h := (chiUnit h : ℂ) • LinearMap.id
  map_one' := by
    ext z
    simp
  map_mul' h k := by
    ext z
    simp [mul_smul, mul_comm]

/-- The bundled finite-dimensional version of `oneDimensionalRepresentation`. -/
def oneDimensionalFDRep {H : Type} [Group H] (chiUnit : H →* ℂˣ) : FDRep ℂ H :=
  FDRep.of (oneDimensionalRepresentation chiUnit)

@[simp] theorem oneDimensionalFDRep_finrank {H : Type} [Group H] (chiUnit : H →* ℂˣ) :
    Module.finrank ℂ (oneDimensionalFDRep chiUnit) = 1 := by
  change Module.finrank ℂ ℂ = 1
  simp

@[simp] theorem oneDimensionalFDRep_character {H : Type} [Group H] (chiUnit : H →* ℂˣ)
    (h : H) :
    (oneDimensionalFDRep chiUnit).character h = (chiUnit h : ℂ) := by
  simp [FDRep.character, oneDimensionalFDRep, oneDimensionalRepresentation]

/-- A finitely generated module is simple when its underlying `ModuleCat` object is simple. -/
theorem simpleFG_of_simpleUnderlying (M : FGModuleCat ℂ) [Simple M.obj] : Simple M := by
  constructor
  intro N f hf
  let F := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
  haveI : Simple (F.obj M) := show Simple M.obj from inferInstance
  haveI : Mono (F.map f) := by infer_instance
  constructor
  · intro hIso
    haveI : IsIso f := hIso
    haveI : IsIso (F.map f) := by infer_instance
    have hmap : F.map f ≠ 0 :=
      (Simple.mono_isIso_iff_nonzero (F.map f)).1 inferInstance
    intro hzero
    apply hmap
    simp [hzero]
  · intro hnonzero
    have hmap : F.map f ≠ 0 := by
      intro h
      apply hnonzero
      apply F.map_injective
      simpa using h
    haveI : IsIso (F.map f) :=
      (Simple.mono_isIso_iff_nonzero (F.map f)).2 hmap
    exact isIso_of_reflects_iso f F

/-- An action on a simple underlying module is a simple object in the action category. -/
theorem simpleAction_of_simpleUnderlying {H : Type} [Group H] (X : FDRep ℂ H)
    [Simple X.V] : Simple X where
  mono_isIso_iff_nonzero := by
    intro Y f hf
    let F := Action.forget (FGModuleCat ℂ) H
    haveI : Mono f.hom := show Mono (F.map f) from inferInstance
    constructor
    · intro hIso
      haveI : IsIso f := hIso
      haveI : IsIso f.hom := show IsIso (F.map f) from inferInstance
      have hhom : f.hom ≠ 0 := (Simple.mono_isIso_iff_nonzero f.hom).1 inferInstance
      intro hzero
      apply hhom
      simpa [hzero]
    · intro hnonzero
      haveI : Mono f.hom := by infer_instance
      have hhom : f.hom ≠ 0 := by
        intro h
        apply hnonzero
        exact Action.Hom.ext h
      haveI : IsIso f.hom := (Simple.mono_isIso_iff_nonzero f.hom).2 hhom
      infer_instance

/-- Every one-dimensional complex representation is simple. -/
instance oneDimensionalFDRep_simple {H : Type} [Group H] (chiUnit : H →* ℂˣ) :
    Simple (oneDimensionalFDRep chiUnit) := by
  haveI : Simple (oneDimensionalFDRep chiUnit).V.obj :=
    simple_of_finrank_eq_one (oneDimensionalFDRep_finrank chiUnit)
  haveI : Simple (oneDimensionalFDRep chiUnit).V :=
    simpleFG_of_simpleUnderlying _
  exact simpleAction_of_simpleUnderlying _

/-! ## Irreducibles of finite abelian groups are one-dimensional -/

/-- In an abelian group action, the action of a group element is itself an equivariant
endomorphism. -/
def centralActionEnd {H : Type} [Group H] [IsMulCommutative H]
    (V : FDRep ℂ H) (h : H) : V ⟶ V where
  hom := Action.ρ V h
  comm g := by
    ext x
    change (V.ρ h * V.ρ g) x = (V.ρ g * V.ρ h) x
    rw [← V.ρ.map_mul, ← V.ρ.map_mul, mul_comm]

/-- Schur's lemma makes every group element act by a scalar in a simple abelian representation. -/
theorem abelian_rho_eq_smul_id {H : Type} [Group H] [IsMulCommutative H]
    (V : FDRep ℂ H) [Simple V] (h : H) :
    ∃ c : ℂ, V.ρ h = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (centralActionEnd V h)
  refine ⟨c, ?_⟩
  have hc' := congrArg (fun f : V ⟶ V => f.hom.hom) hc
  simpa [centralActionEnd] using hc'.symm

/-- Once all action operators are scalar, every underlying linear endomorphism is equivariant. -/
def linearEndAsActionEnd {H : Type} [Group H] [IsMulCommutative H]
    (V : FDRep ℂ H) [Simple V] (f : V →ₗ[ℂ] V) : V ⟶ V where
  hom := ModuleCat.ofHom f
  comm g := by
    obtain ⟨c, hc⟩ := abelian_rho_eq_smul_id V g
    ext x
    change f (V.ρ g x) = V.ρ g (f x)
    rw [hc]
    simp

/-- A simple finite-dimensional complex representation of an abelian group has finrank one. -/
theorem finite_abelian_simple_finrank_one {H : Type} [Group H] [IsMulCommutative H]
    (V : FDRep ℂ H) [Simple V] : Module.finrank ℂ V = 1 := by
  have hid : (LinearMap.id : V →ₗ[ℂ] V) ≠ 0 := by
    intro h
    apply CategoryTheory.id_nonzero V
    apply Action.Hom.ext
    ext x
    have hx := LinearMap.congr_fun h x
    simpa using hx
  have hend : Module.finrank ℂ (V →ₗ[ℂ] V) = 1 := by
    refine finrank_eq_one LinearMap.id hid ?_
    intro f
    obtain ⟨c, hc⟩ :=
      CategoryTheory.endomorphism_simple_eq_smul_id ℂ (linearEndAsActionEnd V f)
    refine ⟨c, ?_⟩
    have hc' := congrArg (fun q : V ⟶ V => q.hom.hom) hc
    simpa [linearEndAsActionEnd] using hc'
  rw [Module.finrank_linearMap] at hend
  nlinarith

/-- The invertible linear map underlying the action of a group element. -/
def actionLinearEquiv {H : Type} [Group H] (V : FDRep ℂ H) (h : H) : V ≃ₗ[ℂ] V where
  toLinearMap := V.ρ h
  invFun := V.ρ h⁻¹
  left_inv := FDRep.ρ_inv_self_apply h
  right_inv := FDRep.ρ_self_inv_apply h

/-- The action, bundled as a homomorphism into the general linear group. -/
def actionLinearEquivHom {H : Type} [Group H] (V : FDRep ℂ H) : H →* (V ≃ₗ[ℂ] V) where
  toFun := actionLinearEquiv V
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change V.ρ 1 x = x
    simp
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    change V.ρ (h * k) x = (V.ρ h * V.ρ k) x
    rw [map_mul]

/-- The determinant of a finite-dimensional representation, as a unit-valued character. -/
def determinantUnitCharacter {H : Type} [Group H] (V : FDRep ℂ H) : H →* ℂˣ :=
  LinearEquiv.det.comp (actionLinearEquivHom V)

/-- In an irreducible abelian representation, the character equals its determinant character. -/
theorem character_eq_determinantUnitCharacter {H : Type} [Group H] [IsMulCommutative H]
    (V : FDRep ℂ H) [Simple V] (h : H) :
    V.character h = (determinantUnitCharacter V h : ℂ) := by
  obtain ⟨c, hc⟩ := abelian_rho_eq_smul_id V h
  have hdim := finite_abelian_simple_finrank_one V
  have hcoe : (actionLinearEquiv V h : V →ₗ[ℂ] V) = c • LinearMap.id := hc
  have hrhs : (determinantUnitCharacter V h : ℂ) =
      LinearMap.det (actionLinearEquiv V h : V →ₗ[ℂ] V) := by
    simpa [determinantUnitCharacter, actionLinearEquivHom] using
      LinearEquiv.coe_det (actionLinearEquiv V h)
  rw [hrhs]
  change LinearMap.trace ℂ V (V.ρ h) =
    LinearMap.det (actionLinearEquiv V h : V →ₗ[ℂ] V)
  rw [hc]
  rw [hcoe, LinearMap.det_smul]
  simp [hdim]

/-- Over a finite group, equal irreducible characters come from isomorphic representations. -/
theorem nonempty_iso_of_character_eq {H : Type} [Group H] [Fintype H]
    (V W : FDRep ℂ H) [Simple V] [Simple W]
    (hchar : V.character = W.character) : Nonempty (V ≅ W) := by
  by_contra hnon
  have hVW := FDRep.char_orthonormal V W
  have hVV := FDRep.char_orthonormal V V
  rw [if_neg hnon] at hVW
  rw [if_pos ⟨Iso.refl V⟩] at hVV
  have hzeroone : (0 : ℂ) = 1 := by
    calc
      0 = ⅟ (Fintype.card H : ℂ) •
          ∑ g : H, V.character g * W.character g⁻¹ := hVW.symm
      _ = ⅟ (Fintype.card H : ℂ) •
          ∑ g : H, V.character g * V.character g⁻¹ := by rw [← hchar]
      _ = 1 := hVV
  exact zero_ne_one hzeroone

/-! ## Trivial rows (the first row of every table) -/

/-- The trivial unit-valued character. -/
def trivialUnitCharacter (H : Type) [Group H] : H →* ℂˣ := 1

@[simp] theorem trivialUnitCharacter_apply (H : Type) [Group H] (h : H) :
    (trivialUnitCharacter H h : ℂ) = 1 := by
  rfl

/-- The first registered row of every representative is realized by the trivial representation. -/
theorem rowZero_character (k : SubgroupKind) :
    (rowOfIndex k ⟨0, by cases k <;> decide⟩).coeff =
      (oneDimensionalFDRep (trivialUnitCharacter (representative k))).character := by
  funext h
  cases k <;>
    simp [rowOfIndex, trivialRow, mkRow, c4Row, v4Row, s3Row, d8Row, a4Row, s4Row,
      oneDimensionalFDRep_character]

theorem rowZero_degree (k : SubgroupKind) :
    (rowOfIndex k ⟨0, by cases k <;> decide⟩).degree = 1 := by
  cases k <;>
    simp [rowOfIndex, trivialRow, mkRow, c4Row, v4Row, s3Row, d8Row, a4Row, s4Row]

/-- The representation realizing row zero is irreducible. -/
instance rowZero_simple (k : SubgroupKind) :
    Simple (oneDimensionalFDRep (trivialUnitCharacter (representative k))) :=
  oneDimensionalFDRep_simple _

/-! ## The two cyclic groups of order two -/

/-- The unique nontrivial unit-valued character of a specified two-element subgroup. -/
def orderTwoUnitCharacter (H : Subgroup S4) (g : S4)
    (hexhaust : ∀ h : H, h.1 = 1 ∨ h.1 = g) (hg : g * g = 1) (hg1 : g ≠ 1) : H →* ℂˣ where
  toFun h := if h.1 = 1 then 1 else -1
  map_one' := by simp
  map_mul' h k := by
    rcases hexhaust h with hh | hh <;> rcases hexhaust k with hk | hk
    · apply Units.ext
      simp [hh, hk]
    · apply Units.ext
      simp [hh, hk]
    · apply Units.ext
      simp [hh, hk]
    · apply Units.ext
      simp [hh, hk, hg, hg1]

theorem c2Transposition_exhaust (h : representative .c2Transposition) :
    h.1 = 1 ∨ h.1 = ConcretePerm.t01 := by
  have hh := h.property
  change h.1 ∈ ({1, ConcretePerm.t01} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  · exact Or.inr (Finset.mem_singleton.mp hh)

theorem c2DoubleTransposition_exhaust (h : representative .c2DoubleTransposition) :
    h.1 = 1 ∨ h.1 = ConcretePerm.double01_23 := by
  have hh := h.property
  change h.1 ∈ ({1, ConcretePerm.double01_23} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  · exact Or.inr (Finset.mem_singleton.mp hh)

theorem t01_sq : ConcretePerm.t01 * ConcretePerm.t01 = 1 := by
  native_decide

theorem t01_ne_one : ConcretePerm.t01 ≠ 1 := by
  native_decide

theorem double01_23_sq :
    ConcretePerm.double01_23 * ConcretePerm.double01_23 = 1 := by
  native_decide

theorem double01_23_ne_one : ConcretePerm.double01_23 ≠ 1 := by
  native_decide

def c2TranspositionUnitCharacter : representative .c2Transposition →* ℂˣ :=
  orderTwoUnitCharacter _ ConcretePerm.t01 c2Transposition_exhaust t01_sq t01_ne_one

def c2DoubleTranspositionUnitCharacter : representative .c2DoubleTransposition →* ℂˣ :=
  orderTwoUnitCharacter _ ConcretePerm.double01_23 c2DoubleTransposition_exhaust
    double01_23_sq double01_23_ne_one

@[simp] theorem c2TranspositionUnitCharacter_apply
    (h : representative .c2Transposition) :
    (c2TranspositionUnitCharacter h : ℂ) = if h.1 = 1 then 1 else -1 := by
  by_cases hh : h = 1 <;>
    simp [c2TranspositionUnitCharacter, orderTwoUnitCharacter, hh]

@[simp] theorem c2DoubleTranspositionUnitCharacter_apply
    (h : representative .c2DoubleTransposition) :
    (c2DoubleTranspositionUnitCharacter h : ℂ) = if h.1 = 1 then 1 else -1 := by
  by_cases hh : h = 1 <;>
    simp [c2DoubleTranspositionUnitCharacter, orderTwoUnitCharacter, hh]

theorem c2Transposition_rowOne_character :
    (rowOfIndex .c2Transposition ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep c2TranspositionUnitCharacter).character := by
  funext h
  simp [rowOfIndex, c2NontrivialRow, mkRow]

theorem c2DoubleTransposition_rowOne_character :
    (rowOfIndex .c2DoubleTransposition ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep c2DoubleTranspositionUnitCharacter).character := by
  funext h
  simp [rowOfIndex, c2NontrivialRow, mkRow]

theorem c2Transposition_rowOne_degree :
    (rowOfIndex .c2Transposition ⟨1, by decide⟩).degree = 1 := by
  simp [rowOfIndex, c2NontrivialRow, mkRow]

theorem c2DoubleTransposition_rowOne_degree :
    (rowOfIndex .c2DoubleTransposition ⟨1, by decide⟩).degree = 1 := by
  simp [rowOfIndex, c2NontrivialRow, mkRow]

instance c2Transposition_rowOne_simple :
    Simple (oneDimensionalFDRep c2TranspositionUnitCharacter) :=
  oneDimensionalFDRep_simple _

instance c2DoubleTransposition_rowOne_simple :
    Simple (oneDimensionalFDRep c2DoubleTranspositionUnitCharacter) :=
  oneDimensionalFDRep_simple _

/-! ## The cyclic group of order three -/

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have hq := omega_quadratic
  rw [h] at hq
  norm_num at hq

theorem omega_cube : omega ^ 3 = 1 := by
  have hfactor : omega ^ 3 - 1 = (omega - 1) * (omega ^ 2 + omega + 1) := by
    ring
  apply sub_eq_zero.mp
  rw [hfactor, omega_quadratic]
  ring

/-- The chosen primitive cube root, bundled as a complex unit. -/
def omegaUnit : ℂˣ := Units.mk0 omega omega_ne_zero

@[simp] theorem omegaUnit_val : (omegaUnit : ℂ) = omega := rfl

@[simp] theorem omegaUnit_cube : omegaUnit ^ 3 = 1 := by
  apply Units.ext
  simpa using omega_cube

@[simp] theorem omegaUnit_four : omegaUnit ^ 4 = omegaUnit := by
  rw [show 4 = 3 + 1 by norm_num, pow_add, omegaUnit_cube, one_mul, pow_one]

theorem omega_four : omega ^ 4 = omega := by
  rw [show 4 = 3 + 1 by norm_num, pow_add, omega_cube, one_mul, pow_one]

theorem omega_sq_sq : (omega ^ 2) ^ 2 = omega := by
  rw [← pow_mul, show 2 * 2 = 4 by norm_num, omega_four]

theorem omega_mul_self : omega * omega = omega ^ 2 := by ring

theorem omega_mul_sq : omega * omega ^ 2 = 1 := by
  calc
    omega * omega ^ 2 = omega ^ 3 := by ring
    _ = 1 := omega_cube

theorem omega_sq_mul : omega ^ 2 * omega = 1 := by
  rw [mul_comm, omega_mul_sq]

theorem omega_sq_mul_sq : omega ^ 2 * omega ^ 2 = omega := by
  calc
    omega ^ 2 * omega ^ 2 = (omega ^ 2) ^ 2 := by ring
    _ = omega := omega_sq_sq

theorem c3_exhaust (h : representative .c3) :
    h.1 = 1 ∨ h.1 = ConcretePerm.cycle012 ∨ h.1 = ConcretePerm.cycle012 ^ 2 := by
  have hh := h.property
  change h.1 ∈
    ({1, ConcretePerm.cycle012, ConcretePerm.cycle012 ^ 2} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (Finset.mem_singleton.mp hh))

theorem cycle012_ne_one : ConcretePerm.cycle012 ≠ 1 := by native_decide
theorem cycle012_sq_ne_one : ConcretePerm.cycle012 ^ 2 ≠ 1 := by native_decide
theorem cycle012_sq_ne_self :
    ConcretePerm.cycle012 ^ 2 ≠ ConcretePerm.cycle012 := by native_decide
theorem cycle012_mul_self :
    ConcretePerm.cycle012 * ConcretePerm.cycle012 =
      ConcretePerm.cycle012 ^ 2 := by native_decide
theorem cycle012_mul_sq :
    ConcretePerm.cycle012 * ConcretePerm.cycle012 ^ 2 = 1 := by native_decide
theorem cycle012_sq_mul :
    ConcretePerm.cycle012 ^ 2 * ConcretePerm.cycle012 = 1 := by native_decide
theorem cycle012_sq_mul_sq :
    ConcretePerm.cycle012 ^ 2 * ConcretePerm.cycle012 ^ 2 =
      ConcretePerm.cycle012 := by native_decide

set_option maxRecDepth 10000 in
/-- The character sending the chosen three-cycle to `omega`. -/
def c3OmegaUnitCharacter : representative .c3 →* ℂˣ where
  toFun h := if h.1 = 1 then 1
    else if h.1 = ConcretePerm.cycle012 then omegaUnit else omegaUnit ^ 2
  map_one' := by simp
  map_mul' h k := by
    rcases c3_exhaust h with hh | hh | hh <;>
      rcases c3_exhaust k with hk | hk | hk
    all_goals
      apply Units.ext
      simp [hh, hk, cycle012_ne_one, cycle012_sq_ne_one, cycle012_sq_ne_self,
        cycle012_mul_self, cycle012_mul_sq, cycle012_sq_mul, cycle012_sq_mul_sq,
        omegaUnit, omegaUnit_cube, omegaUnit_four, omega_mul_self, omega_mul_sq,
        omega_sq_mul, omega_sq_mul_sq]

/-- The conjugate character sending the chosen three-cycle to `omega ^ 2`. -/
def c3OmegaSqUnitCharacter : representative .c3 →* ℂˣ :=
  c3OmegaUnitCharacter ^ 2

@[simp] theorem c3OmegaUnitCharacter_apply (h : representative .c3) :
    (c3OmegaUnitCharacter h : ℂ) =
      if h.1 = 1 then 1
      else if h.1 = ConcretePerm.cycle012 then omega else omega ^ 2 := by
  by_cases h1 : h = 1
  · simp [c3OmegaUnitCharacter, h1]
  by_cases hg : h.1 = ConcretePerm.cycle012
  · simp [c3OmegaUnitCharacter, h1, hg, cycle012_ne_one]
  · simp [c3OmegaUnitCharacter, h1, hg]

@[simp] theorem c3OmegaSqUnitCharacter_apply (h : representative .c3) :
    (c3OmegaSqUnitCharacter h : ℂ) =
      if h.1 = 1 then 1
      else if h.1 = ConcretePerm.cycle012 then omega ^ 2 else omega := by
  rcases c3_exhaust h with hh | hh | hh <;>
    simp [c3OmegaSqUnitCharacter, hh, cycle012_ne_one, cycle012_sq_ne_one,
      cycle012_sq_ne_self, omega_cube, omega_four, omega_sq_sq]

theorem c3_rowOne_character :
    (rowOfIndex .c3 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep c3OmegaUnitCharacter).character := by
  funext h
  simp [rowOfIndex, c3Row, mkRow]

theorem c3_rowTwo_character :
    (rowOfIndex .c3 ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep c3OmegaSqUnitCharacter).character := by
  funext h
  simp [rowOfIndex, c3Row, mkRow]

theorem c3_rowOne_degree : (rowOfIndex .c3 ⟨1, by decide⟩).degree = 1 := by
  simp [rowOfIndex, c3Row, mkRow]

theorem c3_rowTwo_degree : (rowOfIndex .c3 ⟨2, by decide⟩).degree = 1 := by
  simp [rowOfIndex, c3Row, mkRow]

instance c3_rowOne_simple : Simple (oneDimensionalFDRep c3OmegaUnitCharacter) :=
  oneDimensionalFDRep_simple _

instance c3_rowTwo_simple : Simple (oneDimensionalFDRep c3OmegaSqUnitCharacter) :=
  oneDimensionalFDRep_simple _

/-! ## The cyclic group of order four -/

/-- The imaginary unit bundled as a complex unit. -/
def complexIUnit : ℂˣ := Units.mk0 Complex.I (by norm_num)

@[simp] theorem complexIUnit_val : (complexIUnit : ℂ) = Complex.I := rfl
@[simp] theorem complexIUnit_sq : complexIUnit ^ 2 = -1 := by
  apply Units.ext
  norm_num [complexIUnit, pow_two]
@[simp] theorem complexIUnit_cube : complexIUnit ^ 3 = -complexIUnit := by
  apply Units.ext
  norm_num [complexIUnit, pow_succ]
@[simp] theorem complexIUnit_four : complexIUnit ^ 4 = 1 := by
  apply Units.ext
  norm_num [complexIUnit, pow_succ]

theorem c4_exhaust (h : representative .c4) :
    h.1 = 1 ∨ h.1 = ConcretePerm.cycle0123 ∨
      h.1 = ConcretePerm.cycle0123 ^ 2 ∨ h.1 = ConcretePerm.cycle0123 ^ 3 := by
  have hh := h.property
  change h.1 ∈ ({1, ConcretePerm.cycle0123, ConcretePerm.cycle0123 ^ 2,
    ConcretePerm.cycle0123 ^ 3} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inl hh)
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inr (Or.inl hh))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hh)))

theorem cycle0123_ne_one : ConcretePerm.cycle0123 ≠ 1 := by native_decide
theorem cycle0123_sq_ne_one : ConcretePerm.cycle0123 ^ 2 ≠ 1 := by native_decide
theorem cycle0123_cube_ne_one : ConcretePerm.cycle0123 ^ 3 ≠ 1 := by native_decide
theorem cycle0123_sq_ne_self :
    ConcretePerm.cycle0123 ^ 2 ≠ ConcretePerm.cycle0123 := by native_decide
theorem cycle0123_ne_sq :
    ConcretePerm.cycle0123 ≠ ConcretePerm.cycle0123 ^ 2 := by native_decide
theorem cycle0123_cube_ne_self :
    ConcretePerm.cycle0123 ^ 3 ≠ ConcretePerm.cycle0123 := by native_decide
theorem cycle0123_ne_cube :
    ConcretePerm.cycle0123 ≠ ConcretePerm.cycle0123 ^ 3 := by native_decide
theorem cycle0123_cube_ne_sq :
    ConcretePerm.cycle0123 ^ 3 ≠ ConcretePerm.cycle0123 ^ 2 := by native_decide
theorem cycle0123_sq_ne_cube :
    ConcretePerm.cycle0123 ^ 2 ≠ ConcretePerm.cycle0123 ^ 3 := by native_decide
theorem cycle0123_mul_self :
    ConcretePerm.cycle0123 * ConcretePerm.cycle0123 = ConcretePerm.cycle0123 ^ 2 := by
  native_decide
theorem cycle0123_mul_sq :
    ConcretePerm.cycle0123 * ConcretePerm.cycle0123 ^ 2 =
      ConcretePerm.cycle0123 ^ 3 := by native_decide
theorem cycle0123_mul_cube :
    ConcretePerm.cycle0123 * ConcretePerm.cycle0123 ^ 3 = 1 := by native_decide
theorem cycle0123_sq_mul :
    ConcretePerm.cycle0123 ^ 2 * ConcretePerm.cycle0123 =
      ConcretePerm.cycle0123 ^ 3 := by native_decide
theorem cycle0123_sq_mul_sq :
    ConcretePerm.cycle0123 ^ 2 * ConcretePerm.cycle0123 ^ 2 = 1 := by native_decide
theorem cycle0123_sq_mul_cube :
    ConcretePerm.cycle0123 ^ 2 * ConcretePerm.cycle0123 ^ 3 =
      ConcretePerm.cycle0123 := by native_decide
theorem cycle0123_cube_mul :
    ConcretePerm.cycle0123 ^ 3 * ConcretePerm.cycle0123 = 1 := by native_decide
theorem cycle0123_cube_mul_sq :
    ConcretePerm.cycle0123 ^ 3 * ConcretePerm.cycle0123 ^ 2 =
      ConcretePerm.cycle0123 := by native_decide
theorem cycle0123_cube_mul_cube :
    ConcretePerm.cycle0123 ^ 3 * ConcretePerm.cycle0123 ^ 3 =
      ConcretePerm.cycle0123 ^ 2 := by native_decide

set_option maxRecDepth 10000 in
/-- The character sending the chosen four-cycle to `I`. -/
def c4IUnitCharacter : representative .c4 →* ℂˣ where
  toFun h := if h.1 = 1 then 1 else if h.1 = ConcretePerm.cycle0123 then complexIUnit
    else if h.1 = ConcretePerm.cycle0123 ^ 2 then complexIUnit ^ 2 else complexIUnit ^ 3
  map_one' := by simp
  map_mul' h k := by
    rcases c4_exhaust h with hh | hh | hh | hh <;>
      rcases c4_exhaust k with hk | hk | hk | hk
    all_goals
      apply Units.ext
      simp [hh, hk, cycle0123_ne_one, cycle0123_sq_ne_one, cycle0123_cube_ne_one,
        cycle0123_sq_ne_self, cycle0123_cube_ne_self, cycle0123_cube_ne_sq,
        cycle0123_mul_self, cycle0123_mul_sq, cycle0123_mul_cube, cycle0123_sq_mul,
        cycle0123_sq_mul_sq, cycle0123_sq_mul_cube, cycle0123_cube_mul,
        cycle0123_cube_mul_sq, cycle0123_cube_mul_cube, complexIUnit,
        complexIUnit_sq, complexIUnit_cube, complexIUnit_four] <;> norm_num

def c4MinusOneUnitCharacter : representative .c4 →* ℂˣ := c4IUnitCharacter ^ 2
def c4MinusIUnitCharacter : representative .c4 →* ℂˣ := c4IUnitCharacter ^ 3

@[simp] theorem c4IUnitCharacter_apply (h : representative .c4) :
    (c4IUnitCharacter h : ℂ) =
      if h.1 = 1 then 1 else if h.1 = ConcretePerm.cycle0123 then Complex.I
      else if h.1 = ConcretePerm.cycle0123 ^ 2 then -1 else -Complex.I := by
  by_cases h1 : h = 1
  · subst h
    simp
  have hv1 : h.1 ≠ 1 := by
    intro hv
    exact h1 (Subtype.ext hv)
  by_cases hg : h.1 = ConcretePerm.cycle0123
  · simp [c4IUnitCharacter, h1, hv1, hg, cycle0123_ne_one, complexIUnit]
  by_cases hg2 : h.1 = ConcretePerm.cycle0123 ^ 2
  · simp [c4IUnitCharacter, h1, hv1, hg, hg2, cycle0123_sq_ne_one,
      cycle0123_sq_ne_self, complexIUnit]
  · simp [c4IUnitCharacter, h1, hv1, hg, hg2, complexIUnit]

@[simp] theorem c4MinusOneUnitCharacter_apply (h : representative .c4) :
    (c4MinusOneUnitCharacter h : ℂ) =
      if h.1 = 1 ∨ h.1 = ConcretePerm.cycle0123 ^ 2 then 1 else -1 := by
  rcases c4_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    simp [c4MinusOneUnitCharacter, hh, cycle0123_ne_one, cycle0123_sq_ne_one,
      cycle0123_cube_ne_one, cycle0123_sq_ne_self, cycle0123_ne_sq,
      cycle0123_cube_ne_self, cycle0123_ne_cube, cycle0123_cube_ne_sq,
      cycle0123_sq_ne_cube, complexIUnit] <;> norm_num [pow_succ]

@[simp] theorem c4MinusIUnitCharacter_apply (h : representative .c4) :
    (c4MinusIUnitCharacter h : ℂ) =
      if h.1 = 1 then 1 else if h.1 = ConcretePerm.cycle0123 then -Complex.I
      else if h.1 = ConcretePerm.cycle0123 ^ 2 then -1 else Complex.I := by
  rcases c4_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    simp [c4MinusIUnitCharacter, hh, cycle0123_ne_one, cycle0123_sq_ne_one,
      cycle0123_cube_ne_one, cycle0123_sq_ne_self, cycle0123_ne_sq,
      cycle0123_cube_ne_self, cycle0123_ne_cube, cycle0123_cube_ne_sq,
      cycle0123_sq_ne_cube, complexIUnit] <;> norm_num [pow_succ]

theorem c4_rowOne_character :
    (rowOfIndex .c4 ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep c4IUnitCharacter).character := by
  funext h
  norm_num [rowOfIndex, c4Row, mkRow]

theorem c4_rowTwo_character :
    (rowOfIndex .c4 ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep c4MinusOneUnitCharacter).character := by
  funext h
  change (if h.1 = 1 ∨ h.1 = ConcretePerm.cycle0123 ^ 2 then 1 else -1) =
    (oneDimensionalFDRep c4MinusOneUnitCharacter).character h
  simp

theorem c4_rowThree_character :
    (rowOfIndex .c4 ⟨3, by decide⟩).coeff =
      (oneDimensionalFDRep c4MinusIUnitCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.cycle0123 then -Complex.I
    else if h.1 = ConcretePerm.cycle0123 ^ 2 then -1 else Complex.I) =
      (oneDimensionalFDRep c4MinusIUnitCharacter).character h
  simp

theorem c4_rowOne_degree : (rowOfIndex .c4 ⟨1, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, c4Row, mkRow]
theorem c4_rowTwo_degree : (rowOfIndex .c4 ⟨2, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, c4Row, mkRow]
theorem c4_rowThree_degree : (rowOfIndex .c4 ⟨3, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, c4Row, mkRow]

instance c4_rowOne_simple : Simple (oneDimensionalFDRep c4IUnitCharacter) :=
  oneDimensionalFDRep_simple _
instance c4_rowTwo_simple : Simple (oneDimensionalFDRep c4MinusOneUnitCharacter) :=
  oneDimensionalFDRep_simple _
instance c4_rowThree_simple : Simple (oneDimensionalFDRep c4MinusIUnitCharacter) :=
  oneDimensionalFDRep_simple _

/-! ## The two Klein four groups -/

theorem subgroupElement_ne_one_of_val_ne_one {H : Subgroup S4} {h : H}
    (hv : h.1 ≠ 1) : h ≠ 1 := by
  intro he
  apply hv
  simpa using congrArg Subtype.val he

set_option maxRecDepth 10000 in
/-- The unit-valued character of a Klein group determined by its values on two generators. -/
def kleinUnitCharacter (H : Subgroup S4) (a b : S4)
    (hexhaust : ∀ h : H, h.1 = 1 ∨ h.1 = a ∨ h.1 = b ∨ h.1 = a * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : a * b ≠ 1)
    (hba : b * a = a * b) (haa : a * a = 1) (hbb : b * b = 1)
    (hac : a * (a * b) = b) (hca : (a * b) * a = b)
    (hbc : b * (a * b) = a) (hcb : (a * b) * b = a)
    (hcc : (a * b) * (a * b) = 1)
    (hab : a ≠ b) (hacne : a ≠ a * b) (hbcne : b ≠ a * b)
    (sa sb : Bool) : H →* ℂˣ where
  toFun h :=
    let ua : ℂˣ := if sa then -1 else 1
    let ub : ℂˣ := if sb then -1 else 1
    if h.1 = 1 then 1 else if h.1 = a then ua else if h.1 = b then ub else ua * ub
  map_one' := by simp
  map_mul' h k := by
    fin_cases sa <;> fin_cases sb <;>
      rcases hexhaust h with hh | hh | hh | hh <;>
      rcases hexhaust k with hk | hk | hk | hk
    all_goals
      apply Units.ext
      simp [hh, hk, ha1, hb1, hc1, hba, haa, hbb, hac, hca, hbc, hcb, hcc,
        hab, Ne.symm hab, hacne, Ne.symm hacne, hbcne, Ne.symm hbcne] <;> norm_num

theorem v4Normal_exhaust (h : representative .v4Normal) :
    h.1 = 1 ∨ h.1 = ConcretePerm.double01_23 ∨
      h.1 = ConcretePerm.double02_13 ∨
      h.1 = ConcretePerm.double01_23 * ConcretePerm.double02_13 := by
  have hh := h.property
  change h.1 ∈ ({1, ConcretePerm.double01_23, ConcretePerm.double02_13,
    ConcretePerm.double01_23 * ConcretePerm.double02_13} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inl hh)
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inr (Or.inl hh))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hh)))

theorem double02_13_ne_double01_23 :
    ConcretePerm.double02_13 ≠ ConcretePerm.double01_23 := by native_decide

private theorem v4Normal_facts :
    ConcretePerm.double01_23 ≠ 1 ∧
    ConcretePerm.double02_13 ≠ 1 ∧
    ConcretePerm.double01_23 * ConcretePerm.double02_13 ≠ 1 ∧
    ConcretePerm.double02_13 * ConcretePerm.double01_23 =
      ConcretePerm.double01_23 * ConcretePerm.double02_13 ∧
    ConcretePerm.double01_23 * ConcretePerm.double01_23 = 1 ∧
    ConcretePerm.double02_13 * ConcretePerm.double02_13 = 1 ∧
    ConcretePerm.double01_23 *
      (ConcretePerm.double01_23 * ConcretePerm.double02_13) = ConcretePerm.double02_13 ∧
    (ConcretePerm.double01_23 * ConcretePerm.double02_13) *
      ConcretePerm.double01_23 = ConcretePerm.double02_13 ∧
    ConcretePerm.double02_13 *
      (ConcretePerm.double01_23 * ConcretePerm.double02_13) = ConcretePerm.double01_23 ∧
    (ConcretePerm.double01_23 * ConcretePerm.double02_13) *
      ConcretePerm.double02_13 = ConcretePerm.double01_23 ∧
    (ConcretePerm.double01_23 * ConcretePerm.double02_13) *
      (ConcretePerm.double01_23 * ConcretePerm.double02_13) = 1 ∧
    ConcretePerm.double01_23 ≠ ConcretePerm.double02_13 ∧
    ConcretePerm.double01_23 ≠
      ConcretePerm.double01_23 * ConcretePerm.double02_13 ∧
    ConcretePerm.double02_13 ≠
      ConcretePerm.double01_23 * ConcretePerm.double02_13 := by
  native_decide

def v4NormalUnitCharacter (sa sb : Bool) : representative .v4Normal →* ℂˣ :=
  kleinUnitCharacter _ ConcretePerm.double01_23 ConcretePerm.double02_13
    v4Normal_exhaust (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) sa sb

def v4NormalRowOneCharacter := v4NormalUnitCharacter true false
def v4NormalRowTwoCharacter := v4NormalUnitCharacter false true
def v4NormalRowThreeCharacter := v4NormalUnitCharacter true true

theorem v4Normal_rowOne_character :
    (rowOfIndex .v4Normal ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep v4NormalRowOneCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.double01_23 then -1
    else if h.1 = ConcretePerm.double02_13 then 1 else -1) =
      (oneDimensionalFDRep v4NormalRowOneCharacter).character h
  rcases v4Normal_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Normal_facts])
    simp [v4NormalRowOneCharacter, v4NormalUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Normal_facts, double02_13_ne_double01_23] <;> norm_num

theorem v4Normal_rowTwo_character :
    (rowOfIndex .v4Normal ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep v4NormalRowTwoCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.double01_23 then 1
    else if h.1 = ConcretePerm.double02_13 then -1 else -1) =
      (oneDimensionalFDRep v4NormalRowTwoCharacter).character h
  rcases v4Normal_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Normal_facts])
    simp [v4NormalRowTwoCharacter, v4NormalUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Normal_facts, double02_13_ne_double01_23] <;> norm_num

theorem v4Normal_rowThree_character :
    (rowOfIndex .v4Normal ⟨3, by decide⟩).coeff =
      (oneDimensionalFDRep v4NormalRowThreeCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.double01_23 ∨
    h.1 = ConcretePerm.double02_13 then -1 else 1) =
      (oneDimensionalFDRep v4NormalRowThreeCharacter).character h
  rcases v4Normal_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Normal_facts])
    simp [v4NormalRowThreeCharacter, v4NormalUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Normal_facts, double02_13_ne_double01_23] <;> norm_num

theorem v4Normal_rowOne_degree : (rowOfIndex .v4Normal ⟨1, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]
theorem v4Normal_rowTwo_degree : (rowOfIndex .v4Normal ⟨2, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]
theorem v4Normal_rowThree_degree : (rowOfIndex .v4Normal ⟨3, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]

instance v4Normal_rowOne_simple : Simple (oneDimensionalFDRep v4NormalRowOneCharacter) :=
  oneDimensionalFDRep_simple _
instance v4Normal_rowTwo_simple : Simple (oneDimensionalFDRep v4NormalRowTwoCharacter) :=
  oneDimensionalFDRep_simple _
instance v4Normal_rowThree_simple : Simple (oneDimensionalFDRep v4NormalRowThreeCharacter) :=
  oneDimensionalFDRep_simple _

theorem v4Disjoint_exhaust (h : representative .v4Disjoint) :
    h.1 = 1 ∨ h.1 = ConcretePerm.t01 ∨ h.1 = ConcretePerm.t23 ∨
      h.1 = ConcretePerm.t01 * ConcretePerm.t23 := by
  have hh := h.property
  change h.1 ∈ ({1, ConcretePerm.t01, ConcretePerm.t23,
    ConcretePerm.t01 * ConcretePerm.t23} : Finset S4) at hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inl hh
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inl hh)
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact Or.inr (Or.inr (Or.inl hh))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hh)))

private theorem v4Disjoint_facts :
    ConcretePerm.t01 ≠ 1 ∧ ConcretePerm.t23 ≠ 1 ∧
    ConcretePerm.t01 * ConcretePerm.t23 ≠ 1 ∧
    ConcretePerm.t23 * ConcretePerm.t01 = ConcretePerm.t01 * ConcretePerm.t23 ∧
    ConcretePerm.t01 * ConcretePerm.t01 = 1 ∧
    ConcretePerm.t23 * ConcretePerm.t23 = 1 ∧
    ConcretePerm.t01 * (ConcretePerm.t01 * ConcretePerm.t23) = ConcretePerm.t23 ∧
    (ConcretePerm.t01 * ConcretePerm.t23) * ConcretePerm.t01 = ConcretePerm.t23 ∧
    ConcretePerm.t23 * (ConcretePerm.t01 * ConcretePerm.t23) = ConcretePerm.t01 ∧
    (ConcretePerm.t01 * ConcretePerm.t23) * ConcretePerm.t23 = ConcretePerm.t01 ∧
    (ConcretePerm.t01 * ConcretePerm.t23) *
      (ConcretePerm.t01 * ConcretePerm.t23) = 1 ∧
    ConcretePerm.t01 ≠ ConcretePerm.t23 ∧
    ConcretePerm.t01 ≠ ConcretePerm.t01 * ConcretePerm.t23 ∧
    ConcretePerm.t23 ≠ ConcretePerm.t01 * ConcretePerm.t23 := by
  native_decide

theorem t23_ne_t01 : ConcretePerm.t23 ≠ ConcretePerm.t01 := by native_decide

def v4DisjointUnitCharacter (sa sb : Bool) : representative .v4Disjoint →* ℂˣ :=
  kleinUnitCharacter _ ConcretePerm.t01 ConcretePerm.t23 v4Disjoint_exhaust
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) sa sb

def v4DisjointRowOneCharacter := v4DisjointUnitCharacter true false
def v4DisjointRowTwoCharacter := v4DisjointUnitCharacter false true
def v4DisjointRowThreeCharacter := v4DisjointUnitCharacter true true

theorem v4Disjoint_rowOne_character :
    (rowOfIndex .v4Disjoint ⟨1, by decide⟩).coeff =
      (oneDimensionalFDRep v4DisjointRowOneCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.t01 then -1
    else if h.1 = ConcretePerm.t23 then 1 else -1) =
      (oneDimensionalFDRep v4DisjointRowOneCharacter).character h
  rcases v4Disjoint_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Disjoint_facts])
    simp [v4DisjointRowOneCharacter, v4DisjointUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Disjoint_facts, t23_ne_t01] <;> norm_num

theorem v4Disjoint_rowTwo_character :
    (rowOfIndex .v4Disjoint ⟨2, by decide⟩).coeff =
      (oneDimensionalFDRep v4DisjointRowTwoCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.t01 then 1
    else if h.1 = ConcretePerm.t23 then -1 else -1) =
      (oneDimensionalFDRep v4DisjointRowTwoCharacter).character h
  rcases v4Disjoint_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Disjoint_facts])
    simp [v4DisjointRowTwoCharacter, v4DisjointUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Disjoint_facts, t23_ne_t01] <;> norm_num

theorem v4Disjoint_rowThree_character :
    (rowOfIndex .v4Disjoint ⟨3, by decide⟩).coeff =
      (oneDimensionalFDRep v4DisjointRowThreeCharacter).character := by
  funext h
  change (if h.1 = 1 then 1 else if h.1 = ConcretePerm.t01 ∨
    h.1 = ConcretePerm.t23 then -1 else 1) =
      (oneDimensionalFDRep v4DisjointRowThreeCharacter).character h
  rcases v4Disjoint_exhaust h with hh | hh | hh | hh
  · have ht : h = 1 := Subtype.ext hh
    subst h
    simp
  all_goals
    have hne : h ≠ 1 := subgroupElement_ne_one_of_val_ne_one (by
      simp [hh, v4Disjoint_facts])
    simp [v4DisjointRowThreeCharacter, v4DisjointUnitCharacter, kleinUnitCharacter, hh,
      hne, v4Disjoint_facts, t23_ne_t01] <;> norm_num

theorem v4Disjoint_rowOne_degree :
    (rowOfIndex .v4Disjoint ⟨1, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]
theorem v4Disjoint_rowTwo_degree :
    (rowOfIndex .v4Disjoint ⟨2, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]
theorem v4Disjoint_rowThree_degree :
    (rowOfIndex .v4Disjoint ⟨3, by decide⟩).degree = 1 := by
  norm_num [rowOfIndex, v4Row, mkRow]

instance v4Disjoint_rowOne_simple : Simple (oneDimensionalFDRep v4DisjointRowOneCharacter) :=
  oneDimensionalFDRep_simple _
instance v4Disjoint_rowTwo_simple : Simple (oneDimensionalFDRep v4DisjointRowTwoCharacter) :=
  oneDimensionalFDRep_simple _
instance v4Disjoint_rowThree_simple : Simple (oneDimensionalFDRep v4DisjointRowThreeCharacter) :=
  oneDimensionalFDRep_simple _

end PermanentalDominance.N4
