import PermanentalDominance.N4.CharacterRealization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators

/-!
# Reality of character matrix functions on Hermitian matrices

The key representation-theoretic fact is proved by the standard averaged
Gram matrix.  In an arbitrary basis put
`P = ∑_h ρ(h)ᴴ ρ(h)`.  It is positive definite (the identity summand is
positive definite), and `ρ(g)ᴴ P ρ(g) = P`.  Hence `ρ(g⁻¹)` is similar to
`ρ(g)ᴴ`, which gives
`chi(g⁻¹) = conj (chi(g))` after taking traces.

On a Hermitian matrix, the monomial indexed by an inverse permutation is
the conjugate of the original monomial.  Reindexing the finite character
sum by inversion therefore proves that generalized and normalized character
matrix functions are real.  The same argument applies to the permanent.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace PermanentalDominance.N4.Reality

/-! ## The finite-dimensional character identity -/

/-- Matrix form of the inverse-character identity. -/
theorem trace_inv_eq_star_trace_of_finite_matrix_rep
    {G n : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype n] [DecidableEq n]
    (R : G → Matrix n n ℂ)
    (hone : R 1 = 1) (hmul : ∀ g h, R (g * h) = R g * R h) (g : G) :
    Matrix.trace (R g⁻¹) = star (Matrix.trace (R g)) := by
  let gram : G → Matrix n n ℂ := fun h => (R h).conjTranspose * R h
  let P : Matrix n n ℂ := ∑ h : G, gram h
  have hgram (h : G) : IsPSD (gram h) := by
    exact Matrix.posSemidef_conjTranspose_mul_self (R h)
  have hsum (s : Finset G) : IsPSD (∑ h ∈ s, gram h) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : IsPSD (0 : Matrix n n ℂ))
    | @insert h s hnot ih =>
        rw [Finset.sum_insert hnot]
        exact IsPSD.add (hgram h) ih
  have hP : Matrix.PosDef P := by
    classical
    dsimp [P]
    rw [← Finset.add_sum_erase Finset.univ gram (Finset.mem_univ (1 : G))]
    have hgram_one : gram 1 = (1 : Matrix n n ℂ) := by
      simp [gram, hone]
    rw [hgram_one]
    exact Matrix.PosDef.one.add_posSemidef (hsum (Finset.univ.erase 1))
  have hterm (h : G) :
      (R g).conjTranspose * gram h * R g = gram (h * g) := by
    rw [show gram h = (R h).conjTranspose * R h by rfl,
      show gram (h * g) = (R (h * g)).conjTranspose * R (h * g) by rfl,
      hmul]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPinvariant : (R g).conjTranspose * P * R g = P := by
    dsimp [P]
    calc
      (R g).conjTranspose * (∑ h : G, gram h) * R g =
          ∑ h : G, (R g).conjTranspose * gram h * R g := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G, gram (h * g) := by
            apply Finset.sum_congr rfl
            intro h _
            exact hterm h
      _ = ∑ h : G, gram h := by
            exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)
  have hright : R g * R g⁻¹ = 1 := by
    calc
      R g * R g⁻¹ = R (g * g⁻¹) := (hmul _ _).symm
      _ = 1 := by simp [hone]
  have hleft : R g⁻¹ * R g = 1 := by
    calc
      R g⁻¹ * R g = R (g⁻¹ * g) := (hmul _ _).symm
      _ = 1 := by simp [hone]
  have hcongruence : (R g).conjTranspose * P = P * R g⁻¹ := by
    calc
      (R g).conjTranspose * P = ((R g).conjTranspose * P) * 1 := by rw [mul_one]
      _ = ((R g).conjTranspose * P) * (R g * R g⁻¹) := by rw [hright]
      _ = ((R g).conjTranspose * P * R g) * R g⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = P * R g⁻¹ := by rw [hPinvariant]
  have hPunit : IsUnit P := hP.isUnit
  have hPdet : IsUnit P.det :=
    isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hsimilar : P⁻¹ * (R g).conjTranspose * P = R g⁻¹ := by
    calc
      P⁻¹ * (R g).conjTranspose * P = P⁻¹ * ((R g).conjTranspose * P) := by
        rw [Matrix.mul_assoc]
      _ = P⁻¹ * (P * R g⁻¹) := by rw [hcongruence]
      _ = (P⁻¹ * P) * R g⁻¹ := by rw [Matrix.mul_assoc]
      _ = R g⁻¹ := by rw [Matrix.nonsing_inv_mul P hPdet, Matrix.one_mul]
  rw [← hsimilar]
  rw [Matrix.trace_conj' hPunit]
  exact Matrix.trace_conjTranspose (R g)

/-- For every finite complex representation, the value at an inverse is
the complex conjugate character value. -/
theorem fdRep_character_inv_eq_star
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = star (V.character g) := by
  let b := Module.finBasis ℂ V
  let R : G → Matrix (Fin (Module.finrank ℂ V))
      (Fin (Module.finrank ℂ V)) ℂ :=
    fun h => LinearMap.toMatrix b b (V.ρ h)
  have hone : R 1 = 1 := by
    dsimp [R]
    rw [map_one, LinearMap.toMatrix_one]
  have hmul : ∀ h k, R (h * k) = R h * R k := by
    intro h k
    dsimp [R]
    rw [map_mul, LinearMap.toMatrix_mul]
  rw [FDRep.character, FDRep.character,
    LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℂ b]
  exact trace_inv_eq_star_trace_of_finite_matrix_rep R hone hmul g

/-! ## Inverse pairing of matrix monomials -/

theorem permutationMonomial_inv_eq_star {m : Type*}
    [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (sigma : Perm m) :
    permutationMonomial A sigma⁻¹ = star (permutationMonomial A sigma) := by
  rw [permutationMonomial, permutationMonomial]
  calc
    (∏ i : m, A i (sigma⁻¹ i)) = ∏ i : m, A (sigma i) i := by
      exact Fintype.prod_equiv sigma.symm _ _ (fun i => by
        simp [Equiv.Perm.inv_def])
    _ = ∏ i : m, star (A i (sigma i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hA.apply (sigma i) i).symm
    _ = star (∏ i : m, A i (sigma i)) := by
      exact (map_prod (starRingEnd ℂ) _ _).symm

def InverseConjugateCoefficient {G : Type*} [Group G] (χ : G → ℂ) : Prop :=
  ∀ g : G, χ g⁻¹ = star (χ g)

theorem generalizedMatrixFunction_star_eq_self
    {m : Type*} [Fintype m] [DecidableEq m]
    (H : Subgroup (Perm m)) (χ : H → ℂ)
    (hχ : InverseConjugateCoefficient χ)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    star (generalizedMatrixFunction H χ A) =
      generalizedMatrixFunction H χ A := by
  letI : Fintype H := Fintype.ofFinite H
  change (starRingEnd ℂ) (generalizedMatrixFunction H χ A) =
    generalizedMatrixFunction H χ A
  rw [generalizedMatrixFunction]
  rw [map_sum]
  calc
    (∑ sigma : H, star (χ sigma * permutationMonomial A sigma.1)) =
        ∑ sigma : H, χ sigma⁻¹ * permutationMonomial A sigma⁻¹.1 := by
          apply Finset.sum_congr rfl
          intro sigma _
          change (starRingEnd ℂ)
            (χ sigma * permutationMonomial A sigma.1) =
              χ sigma⁻¹ * permutationMonomial A sigma⁻¹.1
          have hc := hχ sigma
          change χ sigma⁻¹ = (starRingEnd ℂ) (χ sigma) at hc
          have hm := permutationMonomial_inv_eq_star hA sigma.1
          change permutationMonomial A sigma.1⁻¹ =
            (starRingEnd ℂ) (permutationMonomial A sigma.1) at hm
          rw [map_mul, ← hc, ← hm]
          rfl
    _ = ∑ sigma : H, χ sigma * permutationMonomial A sigma.1 := by
      exact Fintype.sum_equiv (Equiv.inv H) _ _ (fun _ => rfl)

theorem generalizedMatrixFunction_im_eq_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    (H : Subgroup (Perm m)) (χ : H → ℂ)
    (hχ : InverseConjugateCoefficient χ)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    (generalizedMatrixFunction H χ A).im = 0 := by
  exact Complex.conj_eq_iff_im.mp
    (generalizedMatrixFunction_star_eq_self H χ hχ hA)

theorem normalizedMatrixFunction_im_eq_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    (H : Subgroup (Perm m)) (χ : H → ℂ) (degree : ℂ)
    (hχ : InverseConjugateCoefficient χ) (hdegree : star degree = degree)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    (normalizedMatrixFunction H χ degree A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change (starRingEnd ℂ) (normalizedMatrixFunction H χ degree A) =
    normalizedMatrixFunction H χ degree A
  have hg := generalizedMatrixFunction_star_eq_self H χ hχ hA
  change (starRingEnd ℂ) (generalizedMatrixFunction H χ A) =
    generalizedMatrixFunction H χ A at hg
  have hd := hdegree
  change (starRingEnd ℂ) degree = degree at hd
  rw [normalizedMatrixFunction, map_div₀, hg, hd]

theorem fdRep_normalizedMatrixFunction_im_eq_zero
    {m : Type} [Fintype m] [DecidableEq m]
    (H : Subgroup (Perm m)) (V : FDRep ℂ H)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    (normalizedMatrixFunction H V.character
      (Module.finrank ℂ V : ℂ) A).im = 0 := by
  letI : Fintype H := Fintype.ofFinite H
  apply normalizedMatrixFunction_im_eq_zero H V.character
  · exact fdRep_character_inv_eq_star V
  · norm_num
  · exact hA

theorem permanent_star_eq_self {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    star A.permanent = A.permanent := by
  change (starRingEnd ℂ) A.permanent = A.permanent
  have hcolumn (sigma : Perm m) :
      (∏ i, A (sigma i) i) = permutationMonomial A sigma⁻¹ := by
    rw [permutationMonomial]
    exact (Fintype.prod_equiv sigma.symm _ _ (fun i => by
      simp [Equiv.Perm.inv_def])).symm
  have hterm (sigma : Perm m) :
      (starRingEnd ℂ) (∏ i, A (sigma i) i) =
        ∏ i, A (sigma⁻¹ i) i := by
    rw [hcolumn sigma, hcolumn sigma⁻¹]
    have hm := permutationMonomial_inv_eq_star hA sigma⁻¹
    change permutationMonomial A (sigma⁻¹)⁻¹ =
      (starRingEnd ℂ) (permutationMonomial A sigma⁻¹) at hm
    simpa using hm.symm
  rw [Matrix.permanent, map_sum]
  calc
    (∑ sigma : Perm m, star (∏ i, A (sigma i) i)) =
        ∑ sigma : Perm m, ∏ i, A (sigma⁻¹ i) i := by
          apply Finset.sum_congr rfl
          intro sigma _
          exact hterm sigma
    _ = ∑ sigma : Perm m, ∏ i, A (sigma i) i := by
      exact Fintype.sum_equiv (Equiv.inv (Perm m)) _ _ (fun _ => rfl)

theorem permanent_im_eq_zero {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) : A.permanent.im = 0 :=
  Complex.conj_eq_iff_im.mp (permanent_star_eq_self hA)

end PermanentalDominance.N4.Reality
