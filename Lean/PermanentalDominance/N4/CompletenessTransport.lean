import PermanentalDominance.N4.FinalAssembly
import PermanentalDominance.N4.S4Realization

/-!
# Transport of representative character completeness

Representation-theoretic completeness only has to be proved on the eleven
fixed representative subgroups.  Restriction along the inverse of a subgroup
conjugation equivalence transports an arbitrary simple representation to the
corresponding representative without changing its character degree.
-/

noncomputable section

open CategoryTheory

namespace PermanentalDominance.N4.CompletenessTransport

/-- Character completeness stated solely on the eleven concrete
representatives.  This is the interface supplied by the finite character
table realization modules. -/
def RepresentativeSimpleCompleteness : Prop :=
  ∀ (k : SubgroupKind) (V : FDRep ℂ (representative k)),
    Simple V → ∃ i : Fin (rowCount k),
      FinalAssembly.fdRepRow V = rowOfIndex k i

/-- An isomorphism with a concrete realization identifies the corresponding
`fdRepRow`.  This packages the two invariants needed by all finite-table
completeness dispatchers: character and dimension. -/
theorem fdRepRow_eq_of_iso {H : Subgroup S4} {V W : FDRep ℂ H}
    (iVW : V ≅ W) (row : IrrepDatum H)
    (hchar : row.coeff = W.character)
    (hdegree : row.degree = (Module.finrank ℂ W : ℂ)) :
    FinalAssembly.fdRepRow V = row := by
  apply IrrepDatum.ext
  · change V.character = row.coeff
    exact (FDRep.char_iso iVW).trans hchar.symm
  · change (Module.finrank ℂ V : ℂ) = row.degree
    rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv iVW)]
    exact hdegree.symm

/-- Pulling a representation from `H` to `K` along the inverse of an
equivalence turns its row into `transportRow e`. -/
theorem transport_fdRepRow_eq_pullback
    {H K : Subgroup S4} (e : H ≃* K) (V : FDRep ℂ H) :
    FinalAssembly.transportRow e (FinalAssembly.fdRepRow V) =
      FinalAssembly.fdRepRow (pullbackFDRep e.symm.toMonoidHom V) := by
  apply IrrepDatum.ext
  · funext tau
    change V.character (e.symm tau) =
      (pullbackFDRep e.symm.toMonoidHom V).character tau
    rw [pullbackFDRep_character]
    rfl
  · change (Module.finrank ℂ V : ℂ) =
      (Module.finrank ℂ (pullbackFDRep e.symm.toMonoidHom V) : ℂ)
    rw [pullbackFDRep_finrank]

/-- Completeness on the representative groups implies the conjugation-aware
completeness predicate consumed by `FinalAssembly`. -/
theorem simpleRepresentativeCompleteness_of_representatives
    (hrep : RepresentativeSimpleCompleteness) :
    FinalAssembly.SimpleRepresentativeCompleteness := by
  intro H V hsimple
  letI : Simple V := hsimple
  intro k g hmem
  let e : H ≃* representative k :=
    FinalAssembly.subgroupConjugationEquiv g hmem
  let W : FDRep ℂ (representative k) :=
    pullbackFDRep e.symm.toMonoidHom V
  letI : Simple W := pullbackFDRep_simple_of_surjective
    e.symm.toMonoidHom e.symm.surjective V
  rcases hrep k W inferInstance with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [transport_fdRepRow_eq_pullback e V]
  exact hi

end PermanentalDominance.N4.CompletenessTransport
