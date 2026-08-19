import PermanentalDominance.N4.CharacterRealization

/-!
# A reusable completeness criterion for finite character tables

A finite list of actual simple representations is complete as soon as its degree-weighted
character sum is the regular character.  The proof below is the usual one-line regular-character
argument, expanded using Mathlib's character orthogonality theorem.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4

/-- If the degree-weighted sum of a finite family of irreducible characters is the regular
character, every irreducible representation occurs in that family. -/
theorem simple_complete_of_regular_character_identity
    {H ι : Type} [Group H] [Fintype H] [DecidableEq H] [Fintype ι]
    (W : ι → FDRep ℂ H) [∀ i, Simple (W i)]
    (hregular : ∀ g : H,
      ∑ i : ι, (Module.finrank ℂ (W i) : ℂ) * (W i).character g =
        if g = 1 then (Fintype.card H : ℂ) else 0)
    (V : FDRep ℂ H) [Simple V] : ∃ i : ι, Nonempty (V ≅ W i) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hinv : ⅟ (Fintype.card H : ℂ) ≠ 0 := by
    intro hz
    have hu := invOf_mul_self (Fintype.card H : ℂ)
    rw [hz, zero_mul] at hu
    exact zero_ne_one hu
  have horth (i : ι) :
      ∑ g : H, V.character g * (W i).character g⁻¹ = 0 := by
    have hi := FDRep.char_orthonormal V (W i)
    rw [if_neg (hnone i)] at hi
    rw [smul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left hinv
  have hweighted :
      ∑ i : ι, (Module.finrank ℂ (W i) : ℂ) *
        (∑ g : H, V.character g * (W i).character g⁻¹) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [horth i, mul_zero]
  have hdouble :
      ∑ g : H, V.character g *
        (∑ i : ι, (Module.finrank ℂ (W i) : ℂ) * (W i).character g⁻¹) = 0 := by
    calc
      ∑ g : H, V.character g *
          (∑ i : ι, (Module.finrank ℂ (W i) : ℂ) * (W i).character g⁻¹) =
          ∑ g : H, ∑ i : ι, (Module.finrank ℂ (W i) : ℂ) *
            (V.character g * (W i).character g⁻¹) := by
              apply Finset.sum_congr rfl
              intro g hg
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = ∑ i : ι, ∑ g : H, (Module.finrank ℂ (W i) : ℂ) *
            (V.character g * (W i).character g⁻¹) := Finset.sum_comm
      _ = ∑ i : ι, (Module.finrank ℂ (W i) : ℂ) *
            (∑ g : H, V.character g * (W i).character g⁻¹) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
      _ = 0 := hweighted
  simp_rw [hregular] at hdouble
  have hzero : V.character 1 * (Fintype.card H : ℂ) = 0 := by
    simpa [mul_ite] using hdouble
  have hchar : V.character 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hcard
  rw [FDRep.char_one] at hchar
  haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp (by
    intro hsub
    apply CategoryTheory.id_nonzero V
    apply Action.Hom.ext
    ext x
    exact @Subsingleton.elim V hsub x 0)
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  exact (Nat.ne_of_gt hpos) (by exact_mod_cast hchar)

end PermanentalDominance.N4
