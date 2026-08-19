import PermanentalDominance.N4.Subgroups

/-!
# Character-table rows and their analytic gaps

This module is deliberately representation-theory free.  A row records only
the coefficient function and its (nonzero, in applications positive integer)
degree.  Consequently the finite character-table computation and the analytic
inequalities can be developed independently and joined by definitional
reduction.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4

/-- The analytic data carried by one normalized character-table row. -/
structure IrrepDatum (H : Subgroup S4) where
  coeff : H → ℂ
  degree : ℂ

namespace IrrepDatum

local instance {H : Subgroup S4} : Fintype H := Fintype.ofFinite H

/-- Two table rows are equal when their coefficient functions and degrees
agree.  Keeping this extensionality lemma explicit makes the later
representation-realization bridges independent of structure projection
normalization. -/
@[ext] theorem ext {H : Subgroup S4} {x y : IrrepDatum H}
    (hcoeff : x.coeff = y.coeff) (hdegree : x.degree = y.degree) : x = y := by
  cases x
  cases y
  simp_all

/-- The coefficient actually occurring after degree normalization. -/
def normalizedCoeff {H : Subgroup S4} (row : IrrepDatum H) (sigma : H) : ℂ :=
  row.coeff sigma / row.degree

/-- The normalized generalized matrix function represented by a table row. -/
def tableMatrixFunction {H : Subgroup S4} (row : IrrepDatum H)
    (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  normalizedMatrixFunction H row.coeff row.degree A

theorem tableMatrixFunction_eq_sum {H : Subgroup S4} (row : IrrepDatum H)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    row.tableMatrixFunction A =
      ∑ sigma : H, row.normalizedCoeff sigma * permutationMonomial A sigma.1 := by
  classical
  simp only [tableMatrixFunction, normalizedMatrixFunction, generalizedMatrixFunction,
    normalizedCoeff, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma _
  ring

/-- Permanent minus the real part of a normalized table row. -/
def tableGap {H : Subgroup S4} (row : IrrepDatum H)
    (A : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  A.permanent.re - (row.tableMatrixFunction A).re

/-- A table row is dominated on the entire positive-semidefinite cone. -/
def TableDominates {H : Subgroup S4} (row : IrrepDatum H) : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℂ, IsPSD A → 0 ≤ row.tableGap A

theorem dominatesAt_iff_tableGap_nonneg {H : Subgroup S4}
    (row : IrrepDatum H) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    DominatesAt H row.coeff row.degree A ↔ 0 ≤ row.tableGap A := by
  simp only [DominatesAt, tableGap, tableMatrixFunction, sub_nonneg]

theorem tableDominates_iff {H : Subgroup S4} (row : IrrepDatum H) :
    row.TableDominates ↔
      ∀ A : Matrix (Fin 4) (Fin 4) ℂ,
        IsPSD A → DominatesAt H row.coeff row.degree A := by
  simp only [TableDominates, dominatesAt_iff_tableGap_nonneg]

theorem TableDominates.at {H : Subgroup S4} {row : IrrepDatum H}
    (h : row.TableDominates) {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) : DominatesAt H row.coeff row.degree A :=
  (row.dominatesAt_iff_tableGap_nonneg A).2 (h A hA)

/-- Analytic dominance depends only on the normalized coefficient row. -/
theorem TableDominates.congr_normalizedCoeff {H : Subgroup S4}
    {row row' : IrrepDatum H} (hrow : row.TableDominates)
    (h : ∀ sigma : H, row'.normalizedCoeff sigma = row.normalizedCoeff sigma) :
    row'.TableDominates := by
  intro A hA
  have hfun : row'.tableMatrixFunction A = row.tableMatrixFunction A := by
    rw [row'.tableMatrixFunction_eq_sum, row.tableMatrixFunction_eq_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [h sigma]
  simpa [tableGap, hfun] using hrow A hA

/-- A convex combination of two certified normalized rows is certified. -/
theorem TableDominates.convex {H : Subgroup S4}
    {row row₁ row₂ : IrrepDatum H} (h₁ : row₁.TableDominates)
    (h₂ : row₂.TableDominates) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hcoeff : ∀ sigma : H,
      row.normalizedCoeff sigma =
        (t : ℂ) * row₁.normalizedCoeff sigma +
          ((1 - t : ℝ) : ℂ) * row₂.normalizedCoeff sigma) :
    row.TableDominates := by
  intro A hA
  have hfun : row.tableMatrixFunction A =
      (t : ℂ) * row₁.tableMatrixFunction A +
        ((1 - t : ℝ) : ℂ) * row₂.tableMatrixFunction A := by
    rw [row.tableMatrixFunction_eq_sum, row₁.tableMatrixFunction_eq_sum,
      row₂.tableMatrixFunction_eq_sum]
    simp_rw [hcoeff]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro sigma _
    ring
  have hg₁ := h₁ A hA
  have hg₂ := h₂ A hA
  rw [tableGap, hfun]
  simp only [map_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [show A.permanent.re -
      (t * (row₁.tableMatrixFunction A).re +
        (1 - t) * (row₂.tableMatrixFunction A).re) =
      t * row₁.tableGap A + (1 - t) * row₂.tableGap A by
        simp only [tableGap]
        ring]
  exact add_nonneg (mul_nonneg ht₀ hg₁)
    (mul_nonneg (sub_nonneg.mpr ht₁) hg₂)

/-- A finite table is certified when every row in it is certified. -/
def TableCertified {H : Subgroup S4} (rows : List (IrrepDatum H)) : Prop :=
  ∀ row ∈ rows, row.TableDominates

theorem TableCertified.nil {H : Subgroup S4} :
    TableCertified ([] : List (IrrepDatum H)) := by
  simp [TableCertified]

theorem TableCertified.cons {H : Subgroup S4} {row : IrrepDatum H}
    {rows : List (IrrepDatum H)} (hrow : row.TableDominates)
    (hrows : TableCertified rows) : TableCertified (row :: rows) := by
  intro r hr
  rcases List.mem_cons.mp hr with h | hr
  · subst r
    exact hrow
  · exact hrows r hr

theorem TableCertified.get {H : Subgroup S4} {rows : List (IrrepDatum H)}
    (h : TableCertified rows) {row : IrrepDatum H} (hr : row ∈ rows) :
    row.TableDominates :=
  h row hr

end IrrepDatum

end PermanentalDominance.N4
