import PermanentalDominance.N4.CharacterRealization

/-!
# Completeness of the registered abelian character rows

Every simple complex representation of one of the seven abelian representatives is
one-dimensional.  This file classifies its determinant character against the concrete rows.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

local instance (k : SubgroupKind) : Fintype (representative k) := Fintype.ofFinite _

private theorem trivialCarrier_commutes :
    ∀ a ∈ representativeCarrier .trivial, ∀ b ∈ representativeCarrier .trivial,
      a * b = b * a := by native_decide
private theorem c2TranspositionCarrier_commutes :
    ∀ a ∈ representativeCarrier .c2Transposition,
      ∀ b ∈ representativeCarrier .c2Transposition, a * b = b * a := by native_decide
private theorem c2DoubleTranspositionCarrier_commutes :
    ∀ a ∈ representativeCarrier .c2DoubleTransposition,
      ∀ b ∈ representativeCarrier .c2DoubleTransposition, a * b = b * a := by native_decide
private theorem c3Carrier_commutes :
    ∀ a ∈ representativeCarrier .c3, ∀ b ∈ representativeCarrier .c3,
      a * b = b * a := by native_decide
private theorem c4Carrier_commutes :
    ∀ a ∈ representativeCarrier .c4, ∀ b ∈ representativeCarrier .c4,
      a * b = b * a := by native_decide
private theorem v4NormalCarrier_commutes :
    ∀ a ∈ representativeCarrier .v4Normal, ∀ b ∈ representativeCarrier .v4Normal,
      a * b = b * a := by native_decide
private theorem v4DisjointCarrier_commutes :
    ∀ a ∈ representativeCarrier .v4Disjoint,
      ∀ b ∈ representativeCarrier .v4Disjoint, a * b = b * a := by native_decide

instance trivialRepresentative_isMulCommutative :
    IsMulCommutative (representative .trivial) := ⟨⟨fun a b =>
  Subtype.ext (trivialCarrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance c2TranspositionRepresentative_isMulCommutative :
    IsMulCommutative (representative .c2Transposition) := ⟨⟨fun a b =>
  Subtype.ext (c2TranspositionCarrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance c2DoubleTranspositionRepresentative_isMulCommutative :
    IsMulCommutative (representative .c2DoubleTransposition) := ⟨⟨fun a b =>
  Subtype.ext (c2DoubleTranspositionCarrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance c3Representative_isMulCommutative :
    IsMulCommutative (representative .c3) := ⟨⟨fun a b =>
  Subtype.ext (c3Carrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance c4Representative_isMulCommutative :
    IsMulCommutative (representative .c4) := ⟨⟨fun a b =>
  Subtype.ext (c4Carrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance v4NormalRepresentative_isMulCommutative :
    IsMulCommutative (representative .v4Normal) := ⟨⟨fun a b =>
  Subtype.ext (v4NormalCarrier_commutes a.1 a.2 b.1 b.2)⟩⟩
instance v4DisjointRepresentative_isMulCommutative :
    IsMulCommutative (representative .v4Disjoint) := ⟨⟨fun a b =>
  Subtype.ext (v4DisjointCarrier_commutes a.1 a.2 b.1 b.2)⟩⟩

theorem complex_sq_eq_one_cases {z : ℂ} (hz : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  have hf : (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z + 1) = z ^ 2 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

def c2TranspositionGenerator : representative .c2Transposition :=
  ⟨ConcretePerm.t01, by
    show ConcretePerm.t01 ∈ representativeCarrier .c2Transposition
    native_decide⟩

def c2DoubleTranspositionGenerator : representative .c2DoubleTransposition :=
  ⟨ConcretePerm.double01_23, by
    show ConcretePerm.double01_23 ∈ representativeCarrier .c2DoubleTransposition
    native_decide⟩

theorem trivial_simple_complete (V : FDRep ℂ (representative .trivial)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative .trivial))) := by
  apply nonempty_iso_of_character_eq
  funext h
  rw [character_eq_determinantUnitCharacter]
  have hh := h.property
  change h.1 ∈ ({1} : Finset S4) at hh
  have ht : h = 1 := Subtype.ext (Finset.mem_singleton.mp hh)
  subst h
  simp

theorem c2Transposition_simple_complete
    (V : FDRep ℂ (representative .c2Transposition)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep
      (trivialUnitCharacter (representative .c2Transposition))) ∨
    Nonempty (V ≅ oneDimensionalFDRep c2TranspositionUnitCharacter) := by
  let psi := determinantUnitCharacter V
  have hg2 : c2TranspositionGenerator ^ 2 = 1 := by
    apply Subtype.ext
    native_decide
  have hsqU : psi c2TranspositionGenerator ^ 2 = 1 := by
    rw [← map_pow, hg2, map_one]
  have hsq : (psi c2TranspositionGenerator : ℂ) ^ 2 = 1 := by
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hsqU
  rcases complex_sq_eq_one_cases hsq with hpos | hneg
  · left
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c2Transposition_exhaust h with hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c2TranspositionGenerator := Subtype.ext hh
      subst h
      simpa [psi] using hpos
  · right
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c2Transposition_exhaust h with hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c2TranspositionGenerator := Subtype.ext hh
      subst h
      simpa [psi] using hneg

theorem c2DoubleTransposition_simple_complete
    (V : FDRep ℂ (representative .c2DoubleTransposition)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep
      (trivialUnitCharacter (representative .c2DoubleTransposition))) ∨
    Nonempty (V ≅ oneDimensionalFDRep c2DoubleTranspositionUnitCharacter) := by
  let psi := determinantUnitCharacter V
  have hg2 : c2DoubleTranspositionGenerator ^ 2 = 1 := by
    apply Subtype.ext
    native_decide
  have hsqU : psi c2DoubleTranspositionGenerator ^ 2 = 1 := by
    rw [← map_pow, hg2, map_one]
  have hsq : (psi c2DoubleTranspositionGenerator : ℂ) ^ 2 = 1 := by
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hsqU
  rcases complex_sq_eq_one_cases hsq with hpos | hneg
  · left
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c2DoubleTransposition_exhaust h with hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c2DoubleTranspositionGenerator := Subtype.ext hh
      subst h
      simpa [psi] using hpos
  · right
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c2DoubleTransposition_exhaust h with hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c2DoubleTranspositionGenerator := Subtype.ext hh
      subst h
      simpa [psi] using hneg

theorem complex_cube_eq_one_cases {z : ℂ} (hz : z ^ 3 = 1) :
    z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have hf : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  rcases mul_eq_zero.mp hf with h1 | hq
  · exact Or.inl (sub_eq_zero.mp h1)
  right
  have hsum : omega + omega ^ 2 = -1 := by
    have h := omega_quadratic
    linear_combination h
  have hprod : omega * omega ^ 2 = 1 := omega_mul_sq
  have hfactor : (z - omega) * (z - omega ^ 2) = 0 := by
    calc
      (z - omega) * (z - omega ^ 2) =
          z ^ 2 - (omega + omega ^ 2) * z + omega * omega ^ 2 := by ring
      _ = z ^ 2 + z + 1 := by rw [hsum, hprod]; ring
      _ = 0 := hq
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

def c3Generator : representative .c3 :=
  ⟨ConcretePerm.cycle012, by
    show ConcretePerm.cycle012 ∈ representativeCarrier .c3
    native_decide⟩

@[simp] theorem c3Generator_val : (c3Generator : S4) = ConcretePerm.cycle012 := rfl

theorem c3Generator_ne_one : c3Generator ≠ 1 := by
  intro h
  have hv := congrArg Subtype.val h
  simpa using cycle012_ne_one hv

theorem c3_simple_complete (V : FDRep ℂ (representative .c3)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative .c3))) ∨
    Nonempty (V ≅ oneDimensionalFDRep c3OmegaUnitCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep c3OmegaSqUnitCharacter) := by
  let psi := determinantUnitCharacter V
  have hg3 : c3Generator ^ 3 = 1 := by
    apply Subtype.ext
    native_decide
  have hcubeU : psi c3Generator ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  have hcube : (psi c3Generator : ℂ) ^ 3 = 1 := by
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hcubeU
  rcases complex_cube_eq_one_cases hcube with hroot | hroot | hroot
  · left
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c3_exhaust h with hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c3Generator := Subtype.ext hh
      subst h
      simpa [psi] using hroot
    · have ht : h = c3Generator ^ 2 := Subtype.ext hh
      subst h
      simpa [psi, map_pow, hroot, c3Generator_ne_one, omega_sq_sq,
        show ConcretePerm.cycle012 ≠ (1 : S4) by native_decide]
  · right; left
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c3_exhaust h with hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c3Generator := Subtype.ext hh
      subst h
      simpa [psi] using hroot
    · have ht : h = c3Generator ^ 2 := Subtype.ext hh
      subst h
      simpa [psi, map_pow, hroot, c3Generator_ne_one, omega_sq_sq,
        show ConcretePerm.cycle012 ≠ (1 : S4) by native_decide]
  · right; right
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter]
    rcases c3_exhaust h with hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c3Generator := Subtype.ext hh
      subst h
      simpa [psi] using hroot
    · have ht : h = c3Generator ^ 2 := Subtype.ext hh
      subst h
      simpa [psi, map_pow, hroot, c3Generator_ne_one, omega_sq_sq, omega_cube,
        show ConcretePerm.cycle012 ≠ (1 : S4) by native_decide]

theorem complex_fourth_eq_one_cases {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I := by
  have hz2 : (z ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hz
  rcases complex_sq_eq_one_cases hz2 with hp | hn
  · rcases complex_sq_eq_one_cases hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · have hf : (z - Complex.I) * (z + Complex.I) = 0 := by
      calc
        (z - Complex.I) * (z + Complex.I) = z * z - Complex.I * Complex.I := by ring
        _ = z ^ 2 + 1 := by rw [Complex.I_mul_I]; ring
        _ = 0 := by rw [hn]; ring
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

def c4Generator : representative .c4 :=
  ⟨ConcretePerm.cycle0123, by
    show ConcretePerm.cycle0123 ∈ representativeCarrier .c4
    native_decide⟩

@[simp] theorem c4Generator_val : (c4Generator : S4) = ConcretePerm.cycle0123 := rfl

theorem c4_simple_complete (V : FDRep ℂ (representative .c4)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative .c4))) ∨
    Nonempty (V ≅ oneDimensionalFDRep c4IUnitCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep c4MinusOneUnitCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep c4MinusIUnitCharacter) := by
  let psi := determinantUnitCharacter V
  have hg4 : c4Generator ^ 4 = 1 := by
    apply Subtype.ext
    native_decide
  have hfourU : psi c4Generator ^ 4 = 1 := by
    rw [← map_pow, hg4, map_one]
  have hfour : (psi c4Generator : ℂ) ^ 4 = 1 := by
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hfourU
  have iso_of_generator (chi : representative .c4 →* ℂˣ)
      (hgen : (psi c4Generator : ℂ) = (chi c4Generator : ℂ)) :
      Nonempty (V ≅ oneDimensionalFDRep chi) := by
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter, oneDimensionalFDRep_character]
    rcases c4_exhaust h with hh | hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = c4Generator := Subtype.ext hh
      subst h
      exact hgen
    · have ht : h = c4Generator ^ 2 := Subtype.ext hh
      subst h
      simpa [map_pow] using congrArg (fun z : ℂ => z ^ 2) hgen
    · have ht : h = c4Generator ^ 3 := Subtype.ext hh
      subst h
      simpa [map_pow] using congrArg (fun z : ℂ => z ^ 3) hgen
  rcases complex_fourth_eq_one_cases hfour with hroot | hroot | hroot | hroot
  · left
    apply iso_of_generator
    simpa [psi] using hroot
  · right; left
    apply iso_of_generator
    simpa [psi, c4Generator] using hroot
  · right; right; left
    apply iso_of_generator
    simpa [psi, c4Generator] using hroot
  · right; right; right
    apply iso_of_generator
    simpa [psi, c4Generator] using hroot

def v4NormalGeneratorA : representative .v4Normal :=
  ⟨ConcretePerm.double01_23, by
    show ConcretePerm.double01_23 ∈ representativeCarrier .v4Normal
    native_decide⟩

def v4NormalGeneratorB : representative .v4Normal :=
  ⟨ConcretePerm.double02_13, by
    show ConcretePerm.double02_13 ∈ representativeCarrier .v4Normal
    native_decide⟩

theorem v4Normal_simple_complete (V : FDRep ℂ (representative .v4Normal)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative .v4Normal))) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4NormalRowOneCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4NormalRowTwoCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4NormalRowThreeCharacter) := by
  let psi := determinantUnitCharacter V
  have ha2 : v4NormalGeneratorA ^ 2 = 1 := by apply Subtype.ext; native_decide
  have hb2 : v4NormalGeneratorB ^ 2 = 1 := by apply Subtype.ext; native_decide
  have hsqA : (psi v4NormalGeneratorA : ℂ) ^ 2 = 1 := by
    have hu : psi v4NormalGeneratorA ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hu
  have hsqB : (psi v4NormalGeneratorB : ℂ) ^ 2 = 1 := by
    have hu : psi v4NormalGeneratorB ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hu
  have iso_of_generators (chi : representative .v4Normal →* ℂˣ)
      (ha : (psi v4NormalGeneratorA : ℂ) = (chi v4NormalGeneratorA : ℂ))
      (hb : (psi v4NormalGeneratorB : ℂ) = (chi v4NormalGeneratorB : ℂ)) :
      Nonempty (V ≅ oneDimensionalFDRep chi) := by
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter, oneDimensionalFDRep_character]
    rcases v4Normal_exhaust h with hh | hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = v4NormalGeneratorA := Subtype.ext hh
      subst h
      exact ha
    · have ht : h = v4NormalGeneratorB := Subtype.ext hh
      subst h
      exact hb
    · have ht : h = v4NormalGeneratorA * v4NormalGeneratorB := Subtype.ext hh
      subst h
      simp only [map_mul, Units.val_mul]
      rw [ha, hb]
  rcases complex_sq_eq_one_cases hsqA with ha | ha <;>
    rcases complex_sq_eq_one_cases hsqB with hb | hb
  · left
    apply iso_of_generators
    · simpa [psi] using ha
    · simpa [psi] using hb
  · right; right; left
    apply iso_of_generators
    · simpa [psi, v4NormalGeneratorA, v4NormalRowTwoCharacter,
        v4NormalUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.double01_23 ≠ (1 : S4) by native_decide] using ha
    · simpa [psi, v4NormalGeneratorB, v4NormalRowOneCharacter,
        v4NormalUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.double02_13 ≠ (1 : S4) by native_decide,
        show ConcretePerm.double02_13 ≠ ConcretePerm.double01_23 by native_decide] using hb
  · right; left
    apply iso_of_generators
    · simpa [psi, v4NormalGeneratorA] using ha
    · simpa [psi, v4NormalGeneratorB, v4NormalRowOneCharacter,
        v4NormalUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.double02_13 ≠ (1 : S4) by native_decide,
        show ConcretePerm.double02_13 ≠ ConcretePerm.double01_23 by native_decide] using hb
  · right; right; right
    apply iso_of_generators
    · simpa [psi, v4NormalGeneratorA] using ha
    · simpa [psi, v4NormalGeneratorB] using hb

def v4DisjointGeneratorA : representative .v4Disjoint :=
  ⟨ConcretePerm.t01, by
    show ConcretePerm.t01 ∈ representativeCarrier .v4Disjoint
    native_decide⟩

def v4DisjointGeneratorB : representative .v4Disjoint :=
  ⟨ConcretePerm.t23, by
    show ConcretePerm.t23 ∈ representativeCarrier .v4Disjoint
    native_decide⟩

theorem v4Disjoint_simple_complete (V : FDRep ℂ (representative .v4Disjoint)) [Simple V] :
    Nonempty (V ≅ oneDimensionalFDRep (trivialUnitCharacter (representative .v4Disjoint))) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4DisjointRowOneCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4DisjointRowTwoCharacter) ∨
    Nonempty (V ≅ oneDimensionalFDRep v4DisjointRowThreeCharacter) := by
  let psi := determinantUnitCharacter V
  have ha2 : v4DisjointGeneratorA ^ 2 = 1 := by apply Subtype.ext; native_decide
  have hb2 : v4DisjointGeneratorB ^ 2 = 1 := by apply Subtype.ext; native_decide
  have hsqA : (psi v4DisjointGeneratorA : ℂ) ^ 2 = 1 := by
    have hu : psi v4DisjointGeneratorA ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hu
  have hsqB : (psi v4DisjointGeneratorB : ℂ) ^ 2 = 1 := by
    have hu : psi v4DisjointGeneratorB ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
    simpa using congrArg (fun u : ℂˣ => (u : ℂ)) hu
  have iso_of_generators (chi : representative .v4Disjoint →* ℂˣ)
      (ha : (psi v4DisjointGeneratorA : ℂ) = (chi v4DisjointGeneratorA : ℂ))
      (hb : (psi v4DisjointGeneratorB : ℂ) = (chi v4DisjointGeneratorB : ℂ)) :
      Nonempty (V ≅ oneDimensionalFDRep chi) := by
    apply nonempty_iso_of_character_eq
    funext h
    rw [character_eq_determinantUnitCharacter, oneDimensionalFDRep_character]
    rcases v4Disjoint_exhaust h with hh | hh | hh | hh
    · have ht : h = 1 := Subtype.ext hh
      subst h
      simp
    · have ht : h = v4DisjointGeneratorA := Subtype.ext hh
      subst h
      exact ha
    · have ht : h = v4DisjointGeneratorB := Subtype.ext hh
      subst h
      exact hb
    · have ht : h = v4DisjointGeneratorA * v4DisjointGeneratorB := Subtype.ext hh
      subst h
      simp only [map_mul, Units.val_mul]
      rw [ha, hb]
  rcases complex_sq_eq_one_cases hsqA with ha | ha <;>
    rcases complex_sq_eq_one_cases hsqB with hb | hb
  · left
    apply iso_of_generators
    · simpa [psi] using ha
    · simpa [psi] using hb
  · right; right; left
    apply iso_of_generators
    · simpa [psi, v4DisjointGeneratorA, v4DisjointRowTwoCharacter,
        v4DisjointUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.t01 ≠ (1 : S4) by native_decide] using ha
    · simpa [psi, v4DisjointGeneratorB, v4DisjointRowOneCharacter,
        v4DisjointUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.t23 ≠ (1 : S4) by native_decide,
        show ConcretePerm.t23 ≠ ConcretePerm.t01 by native_decide] using hb
  · right; left
    apply iso_of_generators
    · simpa [psi, v4DisjointGeneratorA] using ha
    · simpa [psi, v4DisjointGeneratorB, v4DisjointRowOneCharacter,
        v4DisjointUnitCharacter, kleinUnitCharacter,
        show ConcretePerm.t23 ≠ (1 : S4) by native_decide,
        show ConcretePerm.t23 ≠ ConcretePerm.t01 by native_decide] using hb
  · right; right; right
    apply iso_of_generators
    · simpa [psi, v4DisjointGeneratorA] using ha
    · simpa [psi, v4DisjointGeneratorB] using hb

end PermanentalDominance.N4
