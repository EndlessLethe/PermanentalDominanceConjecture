import PermanentalDominance.Basic

/-!
# The four cyclic rows after scalar expansion

For a generator monomial `q = x+iy` and the square-of-generator monomial
`r ≥ 0`, the four real parts are the four expressions below.  The common
majorant isolates the sole analytic estimate required from the block
contraction module.
-/

namespace PermanentalDominance.N4.C4Cases

def rowReal (j : Fin 4) (r x y : ℝ) : ℝ :=
  if j = 0 then 1 + r + 2 * x
  else if j = 1 then 1 - r - 2 * y
  else if j = 2 then 1 + r - 2 * x
  else 1 - r + 2 * y

theorem rowReal_le_majorant (j : Fin 4) {r x y : ℝ} (hr : 0 ≤ r) :
    rowReal j r x y ≤ 1 + r + 2 * |x| + 2 * |y| := by
  have hx₁ : x ≤ |x| := le_abs_self x
  have hx₂ : -x ≤ |x| := neg_le_abs x
  have hy₁ : y ≤ |y| := le_abs_self y
  have hy₂ : -y ≤ |y| := neg_le_abs y
  fin_cases j <;> simp [rowReal] <;> linarith

theorem all_rows_of_majorant {P r x y : ℝ} (hr : 0 ≤ r)
    (hmajor : 1 + r + 2 * |x| + 2 * |y| ≤ P) (j : Fin 4) :
    rowReal j r x y ≤ P :=
  (rowReal_le_majorant j hr).trans hmajor

end PermanentalDominance.N4.C4Cases
