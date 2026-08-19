import PermanentalDominance.Completion

/-!
# Generic Hermitian quadratic extension lemmas

These lemmas isolate the dimension-independent linear algebra behind the
Gram-extension step used by the geometric permanental-dominance proofs.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.GramExtension

/-- The Schur slack of the last Gram vector is nonnegative whenever its
inner-product column lies in the span of the preceding Gram block. -/
theorem block_slack_nonneg
    {n : Type*} [Fintype n]
    {G : Matrix n n ℂ} {h z : n → ℂ} {c : ℝ}
    (hR : (Matrix.fromBlocks G (Completion.column h) (Completion.column h)ᴴ
      (fun _ _ => (c : ℂ))).PosSemidef)
    (hz : h = G *ᵥ z) :
    (dotProduct (star z) (G *ᵥ z)).re ≤ c := by
  let v : n ⊕ Fin 1 → ℂ := Sum.elim (-z) (fun _ => 1)
  have hv := (RCLike.nonneg_iff.mp (hR.2 v)).1
  have hG : G.IsHermitian := (hR.submatrix Sum.inl).isHermitian
  have hswap :
      dotProduct (star (G *ᵥ z)) z = dotProduct (star z) (G *ᵥ z) := by
    rw [Matrix.star_mulVec, hG.eq, ← Matrix.dotProduct_mulVec]
  have htop :
      G *ᵥ (-z) + Completion.column h *ᵥ (fun _ : Fin 1 => 1) = 0 := by
    ext i
    rw [Matrix.mulVec_neg]
    simp [hz, Completion.column, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  have hcol :
      (Completion.column h)ᴴ *ᵥ (-z) =
        fun _ : Fin 1 => -dotProduct (star h) z := by
    ext i
    fin_cases i
    simp [Completion.column, Matrix.mulVec, dotProduct]
  have hbottom :
      (Completion.column h)ᴴ *ᵥ (-z) +
          (fun _ _ : Fin 1 => (c : ℂ)) *ᵥ (fun _ => 1) =
        fun _ => (c : ℂ) - dotProduct (star z) (G *ᵥ z) := by
    rw [hcol, hz, hswap]
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hform :
      dotProduct (star v)
          (Matrix.fromBlocks G (Completion.column h) (Completion.column h)ᴴ
            (fun _ _ => (c : ℂ)) *ᵥ v) =
        (c : ℂ) - dotProduct (star z) (G *ᵥ z) := by
    rw [Matrix.fromBlocks_mulVec]
    change dotProduct (star v)
      (Sum.elim
        (G *ᵥ (-z) + Completion.column h *ᵥ (fun _ : Fin 1 => 1))
        ((Completion.column h)ᴴ *ᵥ (-z) +
          (fun _ _ : Fin 1 => (c : ℂ)) *ᵥ (fun _ => 1))) = _
    rw [htop, hbottom]
    simp [v, dotProduct]
  rw [hform] at hv
  simpa [Complex.sub_re] using hv

theorem hermitian_mulVec_dot
    {n : Type*} [Fintype n]
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (x y : n → ℂ) :
    dotProduct (star (Q *ᵥ x)) y = dotProduct (star x) (Q *ᵥ y) := by
  rw [Matrix.star_mulVec, hQ.eq, ← Matrix.dotProduct_mulVec]

/-- Completing the square for a Hermitian form in arbitrary finite dimension. -/
theorem hermitian_quadratic_shift
    {n : Type*} [Fintype n]
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (C : ℝ) (k x z : n → ℂ) (hsolve : Q *ᵥ x = -k) :
    C + 2 * (dotProduct (star k) z).re +
        (dotProduct (star z) (Q *ᵥ z)).re =
      C + (dotProduct (star k) x).re +
        (dotProduct (star (z - x)) (Q *ᵥ (z - x))).re := by
  have hxz : dotProduct (star x) (Q *ᵥ z) =
      -dotProduct (star k) z := by
    rw [← hermitian_mulVec_dot hQ, hsolve]
    simp
  have hzx : dotProduct (star z) (Q *ᵥ x) =
      -dotProduct (star z) k := by
    rw [hsolve]
    simp
  have hxx : dotProduct (star x) (Q *ᵥ x) =
      -dotProduct (star x) k := by
    rw [hsolve]
    simp
  have hre_zk : (dotProduct (star z) k).re =
      (dotProduct (star k) z).re := by
    rw [star_dotProduct]
    simp
  have hre_xk : (dotProduct (star x) k).re =
      (dotProduct (star k) x).re := by
    rw [star_dotProduct]
    simp
  simp_rw [Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct]
  rw [hxz, hzx, hxx]
  simp only [map_sub, Complex.sub_re, Complex.neg_re]
  rw [hre_zk, hre_xk]
  ring

/-- A positive Hermitian Hessian and a nonnegative value at its critical
point imply global nonnegativity of the quadratic. -/
theorem hermitian_quadratic_nonneg_of_minimum
    {n : Type*} [Fintype n]
    {Q : Matrix n n ℂ} (hQ : Q.PosSemidef)
    {C : ℝ} {k x : n → ℂ} (hsolve : Q *ᵥ x = -k)
    (hmin : 0 ≤ C + (dotProduct (star k) x).re) (z : n → ℂ) :
    0 ≤ C + 2 * (dotProduct (star k) z).re +
      (dotProduct (star z) (Q *ᵥ z)).re := by
  rw [hermitian_quadratic_shift hQ.isHermitian C k x z hsolve]
  exact add_nonneg hmin (hQ.re_dotProduct_nonneg (z - x))

/-- Strict version used in positive-definite interior arguments. -/
theorem hermitian_quadratic_pos_of_minimum
    {n : Type*} [Fintype n]
    {Q : Matrix n n ℂ} (hQ : Q.PosSemidef)
    {C : ℝ} {k x : n → ℂ} (hsolve : Q *ᵥ x = -k)
    (hmin : 0 < C + (dotProduct (star k) x).re) (z : n → ℂ) :
    0 < C + 2 * (dotProduct (star k) z).re +
      (dotProduct (star z) (Q *ᵥ z)).re := by
  rw [hermitian_quadratic_shift hQ.isHermitian C k x z hsolve]
  exact add_pos_of_pos_of_nonneg hmin
    (hQ.re_dotProduct_nonneg (z - x))

/-! ## Conditional scalar certificates -/

/-- A one-multiplier certificate for the discriminant on the half-space
`B₁ < 0`.  The identity behind the proof is

`4 B₀ B₂ - B₁² = (4 B₀ B₂ + C B₁) + (-B₁) (B₁ + C)`.

The parameter `C` is certificate data rather than part of the target
inequality. -/
theorem discriminant_pos_of_shift_certificate
    {B₀ B₁ B₂ C : ℝ}
    (hcoupled : 0 < 4 * B₀ * B₂ + C * B₁)
    (hshift : 0 < B₁ + C) (hnegative : B₁ < 0) :
    0 < 4 * B₀ * B₂ - B₁ ^ 2 := by
  rw [show 4 * B₀ * B₂ - B₁ ^ 2 =
      (4 * B₀ * B₂ + C * B₁) + (-B₁) * (B₁ + C) by ring]
  exact add_pos hcoupled (mul_pos (neg_pos.mpr hnegative) hshift)

end PermanentalDominance.GramExtension
