import PermanentalDominance.N4.Reality
import PermanentalDominance.N4.CorrelationLift
import PermanentalDominance.N4.CharacterTables

/-!
# Parameterized final assembly

This module isolates the two transport steps which do not depend on any
case-specific analytic certificate:

* simultaneous relabelling of a matrix by `g : S₄` transports a table row
  across subgroup conjugation;
* the exhaustive subgroup registry reduces an arbitrary subgroup to one of
  the eleven representatives.

The final theorem is deliberately parameterized by (i) dominance of every
registered representative row and (ii) representation-theoretic completeness
of those rows.  Thus it can be instantiated as soon as the nonabelian
realization registry is finished, without changing the transport proof.
-/

noncomputable section

open Complex Matrix
open CategoryTheory
open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.FinalAssembly

/-- The group equivalence induced by `sigma ↦ g⁻¹ sigma g`. -/
def subgroupConjugationEquiv {H K : Subgroup S4} (g : S4)
    (hmem : ∀ sigma : S4, sigma ∈ H ↔ g⁻¹ * sigma * g ∈ K) : H ≃* K where
  toFun sigma := ⟨g⁻¹ * sigma.1 * g, (hmem sigma.1).1 sigma.2⟩
  invFun tau := ⟨g * tau.1 * g⁻¹, by
    apply (hmem _).2
    simpa [mul_assoc] using tau.2⟩
  left_inv sigma := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv tau := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' sigma tau := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Pull a row on `H` across a group equivalence `H ≃ K`. -/
def transportRow {H K : Subgroup S4} (e : H ≃* K)
    (row : IrrepDatum H) : IrrepDatum K where
  coeff tau := row.coeff (e.symm tau)
  degree := row.degree

@[simp] theorem transportRow_degree {H K : Subgroup S4} (e : H ≃* K)
    (row : IrrepDatum H) : (transportRow e row).degree = row.degree := rfl

@[simp] theorem transportRow_normalizedCoeff {H K : Subgroup S4}
    (e : H ≃* K) (row : IrrepDatum H) (tau : K) :
    (transportRow e row).normalizedCoeff tau = row.normalizedCoeff (e.symm tau) := rfl

/-- Simultaneously relabel rows and columns by a permutation. -/
def relabelMatrix (g : S4) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ := A.submatrix g g

theorem relabelMatrix_psd {g : S4} {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsPSD A) : IsPSD (relabelMatrix g A) := by
  exact hA.submatrix g

theorem permanent_relabelMatrix (g : S4)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (relabelMatrix g A).permanent = A.permanent := by
  calc
    (relabelMatrix g A).permanent =
        ((A.submatrix g id).submatrix id g).permanent := by
          rfl
    _ = (A.submatrix g id).permanent :=
      Matrix.permanent_permute_rows g (A.submatrix g id)
    _ = A.permanent := Matrix.permanent_permute_cols g A

theorem permutationMonomial_relabel_conjugate (g sigma : S4)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permutationMonomial (relabelMatrix g A) (g⁻¹ * sigma * g) =
      permutationMonomial A sigma := by
  rw [permutationMonomial, permutationMonomial]
  change (∏ i : Fin 4, A (g i) (g ((g⁻¹ * sigma * g) i))) =
    ∏ i : Fin 4, A i (sigma i)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.inv_def,
    g.apply_symm_apply]
  exact Fintype.prod_equiv g _ _ (fun _ => rfl)

/-- The normalized table function is invariant under simultaneous matrix
relabeling and conjugate transport of its row. -/
theorem tableMatrixFunction_transport_conjugation
    {H K : Subgroup S4} (g : S4)
    (hmem : ∀ sigma : S4, sigma ∈ H ↔ g⁻¹ * sigma * g ∈ K)
    (row : IrrepDatum H) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (transportRow (subgroupConjugationEquiv g hmem) row).tableMatrixFunction
        (relabelMatrix g A) = row.tableMatrixFunction A := by
  let e := subgroupConjugationEquiv g hmem
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype K := Fintype.ofFinite K
  rw [(transportRow e row).tableMatrixFunction_eq_sum,
    row.tableMatrixFunction_eq_sum]
  symm
  apply Fintype.sum_equiv e
  intro sigma
  change row.normalizedCoeff sigma * permutationMonomial A sigma.1 =
    row.normalizedCoeff (e.symm (e sigma)) *
      permutationMonomial (relabelMatrix g A) (e sigma).1
  rw [e.symm_apply_apply]
  have he : (e sigma).1 = g⁻¹ * sigma.1 * g := rfl
  rw [he, permutationMonomial_relabel_conjugate]

theorem tableGap_transport_conjugation
    {H K : Subgroup S4} (g : S4)
    (hmem : ∀ sigma : S4, sigma ∈ H ↔ g⁻¹ * sigma * g ∈ K)
    (row : IrrepDatum H) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (transportRow (subgroupConjugationEquiv g hmem) row).tableGap
        (relabelMatrix g A) = row.tableGap A := by
  rw [IrrepDatum.tableGap, IrrepDatum.tableGap,
    permanent_relabelMatrix,
    tableMatrixFunction_transport_conjugation g hmem]

/-- Dominance transports from a conjugate row back to the original row. -/
theorem tableDominates_of_transport_conjugation
    {H K : Subgroup S4} (g : S4)
    (hmem : ∀ sigma : S4, sigma ∈ H ↔ g⁻¹ * sigma * g ∈ K)
    (row : IrrepDatum H)
    (hdom : (transportRow (subgroupConjugationEquiv g hmem) row).TableDominates) :
    row.TableDominates := by
  intro A hA
  have h := hdom (relabelMatrix g A) (relabelMatrix_psd hA)
  rwa [tableGap_transport_conjugation g hmem row A] at h

/-- Membership form of the exhaustive subgroup-conjugacy certificate. -/
theorem exists_representative_conjugation (H : Subgroup S4) :
    ∃ k : SubgroupKind, ∃ g : S4,
      ∀ sigma : S4, sigma ∈ H ↔ g⁻¹ * sigma * g ∈ representative k := by
  rcases subgroup_conjugacy_exhaustive H with ⟨k, g, hHg⟩
  refine ⟨k, g, fun sigma => ?_⟩
  rw [hHg]
  exact conjugateElements_mem_map k g sigma

/-- The natural table datum attached to a finite-dimensional representation. -/
def fdRepRow {H : Subgroup S4} (V : FDRep ℂ H) : IrrepDatum H where
  coeff := V.character
  degree := (Module.finrank ℂ V : ℂ)

/-- Parameterized completeness statement for one row: after every concrete
representative conjugation supplied by the subgroup registry, the transported
row is one of the registered rows. -/
def RepresentativeRowComplete {H : Subgroup S4} (row : IrrepDatum H) : Prop :=
  ∀ (k : SubgroupKind) (g : S4)
    (hmem : ∀ sigma : S4,
      sigma ∈ H ↔ g⁻¹ * sigma * g ∈ representative k),
    ∃ i : Fin (rowCount k),
      transportRow (subgroupConjugationEquiv g hmem) row = rowOfIndex k i

/-- All registered representative rows have already been proved dominant. -/
def RepresentativeDominanceRegistry : Prop :=
  ∀ (k : SubgroupKind) (i : Fin (rowCount k)),
    (rowOfIndex k i).TableDominates

/-- All simple representations are realized by the registered rows after
conjugating their subgroup to a representative. -/
def SimpleRepresentativeCompleteness : Prop :=
  ∀ (H : Subgroup S4) (V : FDRep ℂ H),
    Simple V → RepresentativeRowComplete (fdRepRow V)

/-- The parameterized final assembly for one simple representation. -/
theorem simple_fdRep_tableDominates_of_registries
    (hdominance : RepresentativeDominanceRegistry)
    (hcomplete : SimpleRepresentativeCompleteness)
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V] :
    (fdRepRow V).TableDominates := by
  rcases exists_representative_conjugation H with ⟨k, g, hmem⟩
  rcases hcomplete H V inferInstance k g hmem with ⟨i, hrow⟩
  apply tableDominates_of_transport_conjugation g hmem (fdRepRow V)
  rw [hrow]
  exact hdominance k i

/-- Pointwise `DominatesAt` consequence on an arbitrary PSD matrix. -/
theorem simple_fdRep_dominatesAt_of_registries
    (hdominance : RepresentativeDominanceRegistry)
    (hcomplete : SimpleRepresentativeCompleteness)
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V]
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) :
    DominatesAt H V.character (Module.finrank ℂ V : ℂ) A := by
  exact (simple_fdRep_tableDominates_of_registries
    hdominance hcomplete H V).at hA

/-- The final pointwise statement with reality made explicit: on a
positive-semidefinite matrix both quantities being compared are real, and the
normalized representation value is at most the permanent. -/
theorem simple_fdRep_real_dominance_of_registries
    (hdominance : RepresentativeDominanceRegistry)
    (hcomplete : SimpleRepresentativeCompleteness)
    (H : Subgroup S4) (V : FDRep ℂ H) [Simple V]
    {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : IsPSD A) :
    (normalizedMatrixFunction H V.character
        (Module.finrank ℂ V : ℂ) A).im = 0 ∧
      A.permanent.im = 0 ∧
      (normalizedMatrixFunction H V.character
          (Module.finrank ℂ V : ℂ) A).re ≤ A.permanent.re := by
  refine ⟨Reality.fdRep_normalizedMatrixFunction_im_eq_zero
      H V hA.isHermitian,
    Reality.permanent_im_eq_zero hA.isHermitian, ?_⟩
  exact simple_fdRep_dominatesAt_of_registries
    hdominance hcomplete H V hA

end PermanentalDominance.N4.FinalAssembly
