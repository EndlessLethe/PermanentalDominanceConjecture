import PermanentalDominance.N4.CycleCoordinates
import PermanentalDominance.N4.Subgroups

/-!
# An explicit enumeration of `S₄`

The enumeration is used only to turn the two finite sums (permanent and
registered character rows) into ring expressions.  Exhaustiveness and
absence of duplicates are kernel-checked by `native_decide`.
-/

noncomputable section

open Equiv
open scoped BigOperators

namespace PermanentalDominance.N4.PermutationEnumeration

abbrev f0 : Fin 4 := 0
abbrev f1 : Fin 4 := 1
abbrev f2 : Fin 4 := 2
abbrev f3 : Fin 4 := 3

def s01 : S4 := Equiv.swap f0 f1
def s02 : S4 := Equiv.swap f0 f2
def s03 : S4 := Equiv.swap f0 f3
def s12 : S4 := Equiv.swap f1 f2
def s13 : S4 := Equiv.swap f1 f3
def s23 : S4 := Equiv.swap f2 f3

def cyc3 (i j k : Fin 4) : S4 := Equiv.swap i j * Equiv.swap j k
def cyc4 (i j k l : Fin 4) : S4 :=
  Equiv.swap i j * Equiv.swap j k * Equiv.swap k l

/-! Explicit-vector presentations keep the later symbolic expansion shallow.
Both the forward and inverse maps are supplied, so these permutations remain
executable and may occur in `native_decide` certificates. -/

def permOfVectors (forward inverse : Fin 4 → Fin 4)
    (left : Function.LeftInverse inverse forward)
    (right : Function.RightInverse inverse forward) : S4 :=
  ⟨forward, inverse, left, right⟩

def p0123 : S4 := permOfVectors ![0, 1, 2, 3] ![0, 1, 2, 3] (by native_decide) (by native_decide)
def p0132 : S4 := permOfVectors ![0, 1, 3, 2] ![0, 1, 3, 2] (by native_decide) (by native_decide)
def p0213 : S4 := permOfVectors ![0, 2, 1, 3] ![0, 2, 1, 3] (by native_decide) (by native_decide)
def p0231 : S4 := permOfVectors ![0, 2, 3, 1] ![0, 3, 1, 2] (by native_decide) (by native_decide)
def p0312 : S4 := permOfVectors ![0, 3, 1, 2] ![0, 2, 3, 1] (by native_decide) (by native_decide)
def p0321 : S4 := permOfVectors ![0, 3, 2, 1] ![0, 3, 2, 1] (by native_decide) (by native_decide)
def p1023 : S4 := permOfVectors ![1, 0, 2, 3] ![1, 0, 2, 3] (by native_decide) (by native_decide)
def p1032 : S4 := permOfVectors ![1, 0, 3, 2] ![1, 0, 3, 2] (by native_decide) (by native_decide)
def p1203 : S4 := permOfVectors ![1, 2, 0, 3] ![2, 0, 1, 3] (by native_decide) (by native_decide)
def p1230 : S4 := permOfVectors ![1, 2, 3, 0] ![3, 0, 1, 2] (by native_decide) (by native_decide)
def p1302 : S4 := permOfVectors ![1, 3, 0, 2] ![2, 0, 3, 1] (by native_decide) (by native_decide)
def p1320 : S4 := permOfVectors ![1, 3, 2, 0] ![3, 0, 2, 1] (by native_decide) (by native_decide)
def p2013 : S4 := permOfVectors ![2, 0, 1, 3] ![1, 2, 0, 3] (by native_decide) (by native_decide)
def p2031 : S4 := permOfVectors ![2, 0, 3, 1] ![1, 3, 0, 2] (by native_decide) (by native_decide)
def p2103 : S4 := permOfVectors ![2, 1, 0, 3] ![2, 1, 0, 3] (by native_decide) (by native_decide)
def p2130 : S4 := permOfVectors ![2, 1, 3, 0] ![3, 1, 0, 2] (by native_decide) (by native_decide)
def p2301 : S4 := permOfVectors ![2, 3, 0, 1] ![2, 3, 0, 1] (by native_decide) (by native_decide)
def p2310 : S4 := permOfVectors ![2, 3, 1, 0] ![3, 2, 0, 1] (by native_decide) (by native_decide)
def p3012 : S4 := permOfVectors ![3, 0, 1, 2] ![1, 2, 3, 0] (by native_decide) (by native_decide)
def p3021 : S4 := permOfVectors ![3, 0, 2, 1] ![1, 3, 2, 0] (by native_decide) (by native_decide)
def p3102 : S4 := permOfVectors ![3, 1, 0, 2] ![2, 1, 3, 0] (by native_decide) (by native_decide)
def p3120 : S4 := permOfVectors ![3, 1, 2, 0] ![3, 1, 2, 0] (by native_decide) (by native_decide)
def p3201 : S4 := permOfVectors ![3, 2, 0, 1] ![2, 3, 1, 0] (by native_decide) (by native_decide)
def p3210 : S4 := permOfVectors ![3, 2, 1, 0] ![3, 2, 1, 0] (by native_decide) (by native_decide)

def allPermsList : Multiset S4 :=
  [p0123, p1023, p2103, p3120, p0213, p0321, p0132,
   p1032, p2301, p3210,
   p1203, p2013, p1320, p3021, p2130, p3102, p0231, p0312,
   p1230, p1302, p2310, p2031, p3201, p3012]

theorem allPermsList_nodup : allPermsList.Nodup := by
  native_decide

def allPerms : Finset S4 := ⟨allPermsList, allPermsList_nodup⟩

theorem allPerms_eq_univ : allPerms = Finset.univ := by
  native_decide

open CycleCoordinates CorrelationReduction ScalarAggregates

theorem product_p0123 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0123 i) i) = 1 := by
  simp [p0123, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p0132 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0132 i) i) = star f * f := by
  simp [p0132, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p0213 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0213 i) i) = star d * d := by
  simp [p0213, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p0231 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0231 i) i) = star d * star f * e := by
  simp [p0231, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p0312 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0312 i) i) = star e * d * f := by
  simp [p0312, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p0321 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p0321 i) i) = star e * e := by
  simp [p0321, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1023 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1023 i) i) = star a * a := by
  simp [p1023, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1032 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1032 i) i) = star a * a * star f * f := by
  simp [p1032, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1203 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1203 i) i) = star a * star d * b := by
  simp [p1203, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1230 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1230 i) i) = star a * star d * star f * c := by
  simp [p1230, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1302 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1302 i) i) = star a * star e * b * f := by
  simp [p1302, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p1320 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p1320 i) i) = star a * star e * c := by
  simp [p1320, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2013 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2013 i) i) = star b * a * d := by
  simp [p2013, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2031 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2031 i) i) = star b * a * star f * e := by
  simp [p2031, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2103 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2103 i) i) = star b * b := by
  simp [p2103, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2130 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2130 i) i) = star b * star f * c := by
  simp [p2130, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2301 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2301 i) i) = star b * star e * b * e := by
  simp [p2301, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p2310 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p2310 i) i) = star b * star e * d * c := by
  simp [p2310, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3012 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3012 i) i) = star c * a * d * f := by
  simp [p3012, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3021 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3021 i) i) = star c * a * e := by
  simp [p3021, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3102 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3102 i) i) = star c * b * f := by
  simp [p3102, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3120 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3120 i) i) = star c * c := by
  simp [p3120, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3201 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3201 i) i) = star c * star d * b * e := by
  simp [p3201, permOfVectors, correlation, Fin.prod_univ_four]

theorem product_p3210 (a b c d e f : ℂ) :
    (∏ i, correlation a b c d e f (p3210 i) i) = star c * star d * d * c := by
  simp [p3210, permOfVectors, correlation, Fin.prod_univ_four]

/-! The row-oriented monomials used by generalized matrix functions. -/

theorem monomial_p0123 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0123 = 1 := by
  simp [permutationMonomial, p0123, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p0132 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0132 = f * star f := by
  simp [permutationMonomial, p0132, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p0213 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0213 = d * star d := by
  simp [permutationMonomial, p0213, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p0231 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0231 = d * f * star e := by
  simp [permutationMonomial, p0231, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p0312 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0312 = e * star d * star f := by
  simp [permutationMonomial, p0312, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p0321 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p0321 = e * star e := by
  simp [permutationMonomial, p0321, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1023 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1023 = a * star a := by
  simp [permutationMonomial, p1023, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1032 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1032 = a * star a * f * star f := by
  simp [permutationMonomial, p1032, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1203 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1203 = a * d * star b := by
  simp [permutationMonomial, p1203, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1230 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1230 = a * d * f * star c := by
  simp [permutationMonomial, p1230, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1302 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1302 = a * e * star b * star f := by
  simp [permutationMonomial, p1302, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p1320 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p1320 = a * e * star c := by
  simp [permutationMonomial, p1320, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2013 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2013 = b * star a * star d := by
  simp [permutationMonomial, p2013, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2031 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2031 = b * star a * f * star e := by
  simp [permutationMonomial, p2031, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2103 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2103 = b * star b := by
  simp [permutationMonomial, p2103, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2130 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2130 = b * f * star c := by
  simp [permutationMonomial, p2130, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2301 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2301 = b * e * star b * star e := by
  simp [permutationMonomial, p2301, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p2310 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p2310 = b * e * star d * star c := by
  simp [permutationMonomial, p2310, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3012 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3012 = c * star a * star d * star f := by
  simp [permutationMonomial, p3012, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3021 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3021 = c * star a * star e := by
  simp [permutationMonomial, p3021, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3102 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3102 = c * star b * star f := by
  simp [permutationMonomial, p3102, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3120 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3120 = c * star c := by
  simp [permutationMonomial, p3120, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3201 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3201 = c * d * star b * star e := by
  simp [permutationMonomial, p3201, permOfVectors, correlation, Fin.prod_univ_four]
theorem monomial_p3210 (a b c d e f : ℂ) :
    permutationMonomial (correlation a b c d e f) p3210 = c * d * star d * star c := by
  simp [permutationMonomial, p3210, permOfVectors, correlation, Fin.prod_univ_four]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem permanent_expansion (a b c d e f : ℂ) :
    (correlation a b c d e f).permanent.re =
      permanentForm (T a b c d e f) (D a b c d e f)
        (C a b c d e f) (F a b c d e f) := by
  have hstar_re (z : ℂ) : (star z).re = z.re := rfl
  have hstar_im (z : ℂ) : (star z).im = -z.im := rfl
  rw [Matrix.permanent, ← allPerms_eq_univ]
  simp [allPerms, allPermsList,
    product_p0123, product_p0132, product_p0213, product_p0231,
    product_p0312, product_p0321, product_p1023, product_p1032,
    product_p1203, product_p1230, product_p1302, product_p1320,
    product_p2013, product_p2031, product_p2103, product_p2130,
    product_p2301, product_p2310, product_p3012, product_p3021,
    product_p3102, product_p3120, product_p3201, product_p3210]
  simp only [permanentForm, T, D, C, F, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
  ring

end PermanentalDominance.N4.PermutationEnumeration
