import PermanentalDominance.N4.Subgroups

/-!
# The eleven conjugacy classes of subgroups of `S₄`

The finite certificate in this file avoids deciding membership in an abstract `Subgroup`.
Instead, it registers the thirty concrete conjugate carriers. Starting from the trivial carrier,
adjoining any one permutation and performing five multiplication-saturation rounds again lands in
the registry. A finite-set induction on an arbitrary subgroup carrier proves the classification.
-/

namespace PermanentalDominance.N4

inductive SubgroupKind
  | trivial | c2Transposition | c2DoubleTransposition | c3 | c4
  | v4Normal | v4Disjoint | s3 | d8 | a4 | s4
  deriving DecidableEq, Repr, Fintype

namespace ConcretePerm

private abbrev f0 : Fin 4 := 0
private abbrev f1 : Fin 4 := 1
private abbrev f2 : Fin 4 := 2
private abbrev f3 : Fin 4 := 3

def t01 : S4 := Equiv.swap f0 f1
def t12 : S4 := Equiv.swap f1 f2
def t23 : S4 := Equiv.swap f2 f3
def t02 : S4 := Equiv.swap f0 f2
def t13 : S4 := Equiv.swap f1 f3

def double01_23 : S4 := t01 * t23
def double02_13 : S4 := t02 * t13
def cycle012 : S4 := t01 * t12
def cycle013 : S4 := t01 * t13
def cycle023 : S4 := t02 * t23
def cycle123 : S4 := t12 * t23
def cycle0123 : S4 := t01 * t12 * t23

end ConcretePerm

open ConcretePerm

private def trivialCarrier : Finset S4 := {1}
private def c2TranspositionCarrier : Finset S4 := {1, t01}
private def c2DoubleTranspositionCarrier : Finset S4 := {1, double01_23}
private def c3Carrier : Finset S4 := {1, cycle012, cycle012 ^ 2}
private def c4Carrier : Finset S4 := {1, cycle0123, cycle0123 ^ 2, cycle0123 ^ 3}
private def v4NormalCarrier : Finset S4 :=
  {1, double01_23, double02_13, double01_23 * double02_13}
private def v4DisjointCarrier : Finset S4 := {1, t01, t23, t01 * t23}
private def s3Carrier : Finset S4 := Finset.univ.filter fun σ => σ 3 = 3
private def d8Carrier : Finset S4 :=
  {1, cycle0123, cycle0123 ^ 2, cycle0123 ^ 3,
    t02, t02 * cycle0123, t02 * cycle0123 ^ 2, t02 * cycle0123 ^ 3}
private def a4Carrier : Finset S4 :=
  {1,
    double01_23, double02_13, double01_23 * double02_13,
    cycle012, cycle012 ^ 2, cycle013, cycle013 ^ 2,
    cycle023, cycle023 ^ 2, cycle123, cycle123 ^ 2}
private def s4Carrier : Finset S4 := Finset.univ

/-- The concrete carrier attached to a subgroup kind. -/
def representativeCarrier : SubgroupKind → Finset S4
  | .trivial => trivialCarrier
  | .c2Transposition => c2TranspositionCarrier
  | .c2DoubleTransposition => c2DoubleTranspositionCarrier
  | .c3 => c3Carrier
  | .c4 => c4Carrier
  | .v4Normal => v4NormalCarrier
  | .v4Disjoint => v4DisjointCarrier
  | .s3 => s3Carrier
  | .d8 => d8Carrier
  | .a4 => a4Carrier
  | .s4 => s4Carrier

private structure FiniteSubgroupCertificate (s : Finset S4) : Prop where
  one_mem : 1 ∈ s
  mul_mem : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s
  inv_mem : ∀ a ∈ s, a⁻¹ ∈ s

private instance (s : Finset S4) : Decidable (FiniteSubgroupCertificate s) :=
  decidable_of_iff
    (1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a ∈ s, a⁻¹ ∈ s))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
      fun h => ⟨h.one_mem, h.mul_mem, h.inv_mem⟩⟩

private theorem representativeCarrier_certificate (k : SubgroupKind) :
    FiniteSubgroupCertificate (representativeCarrier k) := by
  cases k <;> native_decide

private def subgroupOfCertifiedCarrier (s : Finset S4)
    (hs : FiniteSubgroupCertificate s) : Subgroup S4 where
  carrier := {x | x ∈ s}
  one_mem' := hs.one_mem
  mul_mem' ha hb := hs.mul_mem _ ha _ hb
  inv_mem' ha := hs.inv_mem _ ha

/-- A concrete subgroup representing each conjugacy type. -/
def representative (k : SubgroupKind) : Subgroup S4 :=
  subgroupOfCertifiedCarrier (representativeCarrier k) (representativeCarrier_certificate k)

@[simp] theorem mem_representative_iff (k : SubgroupKind) (σ : S4) :
    σ ∈ representative k ↔ σ ∈ representativeCarrier k := Iff.rfl

/-- Elementary elementwise subgroup conjugacy. -/
def SubgroupConjugate (H K : Subgroup S4) : Prop :=
  ∃ g : S4, ∀ σ : S4, σ ∈ H ↔ g * σ * g⁻¹ ∈ K

theorem SubgroupConjugate.refl (H : Subgroup S4) : SubgroupConjugate H H := by
  refine ⟨1, ?_⟩
  simp

theorem SubgroupConjugate.symm {H K : Subgroup S4}
    (hHK : SubgroupConjugate H K) : SubgroupConjugate K H := by
  rcases hHK with ⟨g, hg⟩
  refine ⟨g⁻¹, fun σ => ?_⟩
  convert (hg (g⁻¹ * σ * g)).symm using 1 <;> group

theorem SubgroupConjugate.trans {H K L : Subgroup S4}
    (hHK : SubgroupConjugate H K) (hKL : SubgroupConjugate K L) :
    SubgroupConjugate H L := by
  rcases hHK with ⟨g, hg⟩
  rcases hKL with ⟨h, hh⟩
  refine ⟨h * g, fun σ => ?_⟩
  rw [hg, hh]
  simp only [mul_inv_rev, mul_assoc]

/-- Carrier of the conjugate of representative `k` by `g`. -/
def conjugateCarrier (k : SubgroupKind) (g : S4) : Finset S4 :=
  Finset.univ.filter fun σ => g⁻¹ * σ * g ∈ representativeCarrier k

@[simp] theorem mem_conjugateCarrier (k : SubgroupKind) (g σ : S4) :
    σ ∈ conjugateCarrier k g ↔ g⁻¹ * σ * g ∈ representativeCarrier k := by
  simp [conjugateCarrier]

/-- All concrete conjugate carriers. Duplicate presentations are removed by `image`. -/
def registeredCarriers : Finset (Finset S4) :=
  Finset.univ.image fun p : SubgroupKind × S4 => conjugateCarrier p.1 p.2

theorem mem_registeredCarriers_iff (C : Finset S4) :
    C ∈ registeredCarriers ↔
      ∃ k : SubgroupKind, ∃ g : S4, C = conjugateCarrier k g := by
  simp only [registeredCarriers, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨k, g, rfl⟩
    exact ⟨(k, g), rfl⟩

/-! The computational certificate below uses base-four codes in `Fin 256`; group multiplication
then becomes four table lookups on natural numbers rather than evaluation of `Equiv` closures. -/

/-- Base-four encoding of the four values of a permutation. -/
def encode (σ : S4) : Fin 256 :=
  ⟨((σ 0).val + 4 * (σ 1).val + 16 * (σ 2).val + 64 * (σ 3).val) % 256,
    Nat.mod_lt _ (by norm_num)⟩

private def codeDigit (c : Fin 256) (i : Nat) : Nat := (c.val / 4 ^ i) % 4

/-- Multiplication directly on base-four permutation codes. -/
def codeMul (a b : Fin 256) : Fin 256 :=
  ⟨(codeDigit a (codeDigit b 0) +
      4 * codeDigit a (codeDigit b 1) +
      16 * codeDigit a (codeDigit b 2) +
      64 * codeDigit a (codeDigit b 3)) % 256,
    Nat.mod_lt _ (by norm_num)⟩

theorem encode_injective : Function.Injective encode := by
  native_decide

theorem encode_mul : ∀ σ τ : S4, encode (σ * τ) = codeMul (encode σ) (encode τ) := by
  native_decide

private def codeCarrier (C : Finset S4) : Finset (Fin 256) := C.image encode

private def registeredCodeCarriers : Finset (Finset (Fin 256)) :=
  registeredCarriers.image codeCarrier

private theorem mem_registeredCodeCarriers_iff (D : Finset (Fin 256)) :
    D ∈ registeredCodeCarriers ↔
      ∃ C ∈ registeredCarriers, D = codeCarrier C := by
  simp [registeredCodeCarriers, eq_comm]

private def codeSaturate (C : Finset (Fin 256)) : Finset (Fin 256) :=
  C ∪ C.biUnion fun a => C.image fun b => codeMul a b

private def codeClosureRounds : Nat → Finset (Fin 256) → Finset (Fin 256)
  | 0, C => C
  | n + 1, C => codeClosureRounds n (codeSaturate C)

def codeFiniteClosure (C : Finset (Fin 256)) : Finset (Fin 256) :=
  codeClosureRounds 5 C

private theorem subset_codeSaturate (C : Finset (Fin 256)) : C ⊆ codeSaturate C := by
  intro x hx
  exact Finset.mem_union_left _ hx

private theorem subset_codeClosureRounds (n : Nat) (C : Finset (Fin 256)) :
    C ⊆ codeClosureRounds n C := by
  induction n generalizing C with
  | zero => exact fun _ h => h
  | succ n ih =>
      exact Finset.Subset.trans (subset_codeSaturate C) (ih (codeSaturate C))

private theorem subset_codeFiniteClosure (C : Finset (Fin 256)) :
    C ⊆ codeFiniteClosure C := subset_codeClosureRounds 5 C

private def CodesRealizedIn (H : Subgroup S4) (D : Finset (Fin 256)) : Prop :=
  ∀ c ∈ D, ∃ σ : S4, σ ∈ H ∧ encode σ = c

private theorem codeSaturate_realized (H : Subgroup S4) {D : Finset (Fin 256)}
    (hD : CodesRealizedIn H D) : CodesRealizedIn H (codeSaturate D) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact hD c hc
  · rcases Finset.mem_biUnion.mp hc with ⟨a, ha, hc⟩
    rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
    rcases hD a ha with ⟨σ, hσ, rfl⟩
    rcases hD b hb with ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, H.mul_mem hσ hτ, encode_mul σ τ⟩

private theorem codeClosureRounds_realized (H : Subgroup S4) (n : Nat)
    {D : Finset (Fin 256)} (hD : CodesRealizedIn H D) :
    CodesRealizedIn H (codeClosureRounds n D) := by
  induction n generalizing D with
  | zero => exact hD
  | succ n ih => exact ih (codeSaturate_realized H hD)

private theorem codeFiniteClosure_realized (H : Subgroup S4) {D : Finset (Fin 256)}
    (hD : CodesRealizedIn H D) : CodesRealizedIn H (codeFiniteClosure D) :=
  codeClosureRounds_realized H 5 hD

private theorem mem_codeCarrier_of_mem {C : Finset S4} {σ : S4} (hσ : σ ∈ C) :
    encode σ ∈ codeCarrier C := Finset.mem_image.mpr ⟨σ, hσ, rfl⟩

private theorem mem_of_encode_mem_codeCarrier {C : Finset S4} {σ : S4}
    (hσ : encode σ ∈ codeCarrier C) : σ ∈ C := by
  rcases Finset.mem_image.mp hσ with ⟨τ, hτ, he⟩
  exact encode_injective he ▸ hτ

/-- The code transition core has only `11 × 24 × 24` small integer cases. -/
private theorem registered_code_transition_all :
    ∀ k : SubgroupKind, ∀ g x : S4,
      codeFiniteClosure
          (insert (encode x) (codeCarrier (conjugateCarrier k g))) ∈
        registeredCodeCarriers := by
  native_decide

/-- One registered-carrier transition, together with the two inclusions needed by induction. -/
private theorem registered_transition (H : Subgroup S4) (C : Finset S4)
    (hCreg : C ∈ registeredCarriers) (x : S4) (hxH : x ∈ H)
    (hCH : ∀ y ∈ C, y ∈ H) :
    ∃ D ∈ registeredCarriers, insert x C ⊆ D ∧ ∀ y ∈ D, y ∈ H := by
  rcases (mem_registeredCarriers_iff C).1 hCreg with ⟨k, g, rfl⟩
  let E := codeFiniteClosure
    (insert (encode x) (codeCarrier (conjugateCarrier k g)))
  have hEreg : E ∈ registeredCodeCarriers := registered_code_transition_all k g x
  rcases (mem_registeredCodeCarriers_iff E).1 hEreg with ⟨D, hDreg, hED⟩
  refine ⟨D, hDreg, ?_, ?_⟩
  · intro y hy
    apply mem_of_encode_mem_codeCarrier
    rw [← hED]
    apply subset_codeFiniteClosure
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_codeCarrier_of_mem hy)
  · have hstart : CodesRealizedIn H
        (insert (encode x) (codeCarrier (conjugateCarrier k g))) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨x, hxH, rfl⟩
      · rcases Finset.mem_image.mp hc with ⟨y, hy, rfl⟩
        exact ⟨y, hCH y hy, rfl⟩
    have hreal : CodesRealizedIn H E := codeFiniteClosure_realized H hstart
    intro y hy
    have hey : encode y ∈ E := by rw [hED]; exact mem_codeCarrier_of_mem hy
    rcases hreal (encode y) hey with ⟨z, hzH, heq⟩
    have hzy : z = y := encode_injective heq
    simpa [hzy] using hzH

private theorem singleton_one_registered : ({1} : Finset S4) ∈ registeredCarriers := by
  native_decide

private theorem subset_has_registered_closure (H : Subgroup S4) (s : Finset S4)
    (hsH : ∀ x ∈ s, x ∈ H) :
    ∃ C ∈ registeredCarriers, s ⊆ C ∧ ∀ x ∈ C, x ∈ H := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨{1}, singleton_one_registered, ?_, ?_⟩
      · simp
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact H.one_mem
  | @insert x s hxs ih =>
      have hxH : x ∈ H := hsH x (Finset.mem_insert_self x s)
      have hsH' : ∀ y ∈ s, y ∈ H := fun y hy => hsH y (Finset.mem_insert_of_mem hy)
      rcases ih hsH' with ⟨C, hCreg, hsC, hCH⟩
      rcases registered_transition H C hCreg x hxH hCH with ⟨D, hDreg, hxCD, hDH⟩
      refine ⟨D, hDreg, ?_, hDH⟩
      intro y hy
      apply hxCD
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hsC hy)

private theorem exists_registered_carrier_eq (H : Subgroup S4) :
    ∃ C ∈ registeredCarriers, ∀ σ : S4, σ ∈ H ↔ σ ∈ C := by
  classical
  let s : Finset S4 := Finset.univ.filter fun σ => σ ∈ H
  have hsH : ∀ σ ∈ s, σ ∈ H := by simp [s]
  rcases subset_has_registered_closure H s hsH with ⟨C, hCreg, hsC, hCH⟩
  refine ⟨C, hCreg, fun σ => ⟨?_, hCH σ⟩⟩
  intro hσ
  apply hsC
  simp [s, hσ]

theorem conjugateElements_mem_map (k : SubgroupKind) (g σ : S4) :
    σ ∈ (representative k).map (MulAut.conj g).toMonoidHom ↔
      g⁻¹ * σ * g ∈ representative k := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hτ
  · intro hσ
    refine ⟨g⁻¹ * σ * g, hσ, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- Every subgroup of `S₄` is a conjugate of one of the eleven representatives. -/
theorem subgroup_conjugacy_exhaustive (H : Subgroup S4) :
    ∃ k : SubgroupKind, ∃ g : S4,
      H = (representative k).map (MulAut.conj g).toMonoidHom := by
  rcases exists_registered_carrier_eq H with ⟨C, hCreg, hHC⟩
  rcases (mem_registeredCarriers_iff C).1 hCreg with ⟨k, g, rfl⟩
  refine ⟨k, g, SetLike.ext fun σ => ?_⟩
  rw [conjugateElements_mem_map]
  exact (hHC σ).trans (by simp)

end PermanentalDominance.N4
