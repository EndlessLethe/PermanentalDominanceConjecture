import PermanentalDominance.Basic

noncomputable section

/-!
# Scalar cycle aggregates for a four by four correlation matrix

The finite permutation expansions in the case files reduce to four real
aggregates: transpositions `T`, double transpositions `D`, paired three-cycles
`C`, and paired four-cycles `F`.  This small file records the common affine
forms, independently of the six-coordinate realization.
-/

namespace PermanentalDominance.N4.ScalarAggregates

def permanentForm (T D C F : ℝ) : ℝ := 1 + T + D + C + F
def determinantForm (T D C F : ℝ) : ℝ := 1 - T + D + C - F

def s4Standard31 (T D C F : ℝ) : ℝ := 1 + T / 3 - D / 3 - F / 3
def s4Standard211 (T D C F : ℝ) : ℝ := 1 - T / 3 - D / 3 + F / 3
def s4Standard22 (T D C F : ℝ) : ℝ := 1 + D - C / 2

theorem permanent_sub_determinant (T D C F : ℝ) :
    permanentForm T D C F - determinantForm T D C F = 2 * (T + F) := by
  simp [permanentForm, determinantForm]
  ring

end PermanentalDominance.N4.ScalarAggregates
