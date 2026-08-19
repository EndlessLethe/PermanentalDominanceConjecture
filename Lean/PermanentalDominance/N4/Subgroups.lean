import PermanentalDominance.Basic
import Mathlib.GroupTheory.Coset.Card

/-!
# Numerical subgroup classification for `S₄`

The full proof treats subgroup conjugacy types separately.  This file supplies the first
kernel-checked finite reduction: every subgroup order is one of the eight divisors of `24`.
-/

namespace PermanentalDominance.N4

abbrev S4 := Perm (Fin 4)

theorem natCard_S4 : Nat.card S4 = 24 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

theorem subgroup_order_dvd_24 (H : Subgroup S4) : Nat.card H ∣ 24 := by
  simpa [natCard_S4] using H.card_subgroup_dvd_card

theorem subgroup_order_cases (H : Subgroup S4) :
    Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 ∨ Nat.card H = 4 ∨
      Nat.card H = 6 ∨ Nat.card H = 8 ∨ Nat.card H = 12 ∨ Nat.card H = 24 := by
  have hd := subgroup_order_dvd_24 H
  have hp : 0 < Nat.card H := Nat.card_pos
  have hu : Nat.card H ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  interval_cases h : Nat.card H <;> norm_num at hd ⊢

end PermanentalDominance.N4

