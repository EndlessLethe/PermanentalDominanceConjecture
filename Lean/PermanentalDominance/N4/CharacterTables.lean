import PermanentalDominance.N4.SubgroupRegistry
import PermanentalDominance.N4.TableClosure

/-!
# Explicit character-table rows for the eleven subgroup types of `S₄`

There are thirty-seven rows in total.  We record them as coefficient functions on the concrete
representatives from `SubgroupRegistry`.  All tests in the definitions below are tests of finite
permutations; no choice of an enumeration of a subgroup enters the public API.
-/

noncomputable section

namespace PermanentalDominance.N4

open scoped ComplexOrder

/-- The primitive cube root with negative imaginary part, matching `A4Certificate.omega`. -/
def omega : ℂ := (-1 / 2 : ℝ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I

theorem omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [omega] at this

def mkRow {H : Subgroup S4} (χ : H → ℂ) (d : ℂ) : IrrepDatum H :=
  ⟨χ, d⟩

def trivialRow (H : Subgroup S4) : IrrepDatum H :=
  mkRow (fun _ => 1) 1

def c2NontrivialRow {H : Subgroup S4} : IrrepDatum H :=
  mkRow (fun σ => if σ.1 = 1 then 1 else -1) 1

def c3Row (g : S4) (j : Bool) {H : Subgroup S4} : IrrepDatum H :=
  mkRow (fun σ =>
    if σ.1 = 1 then 1
    else if σ.1 = g then if j then omega ^ 2 else omega
    else if j then omega else omega ^ 2) 1

def c4Row (g : S4) (j : Fin 4) {H : Subgroup S4} : IrrepDatum H :=
  mkRow (fun σ =>
    if j = 0 then 1
    else if j = 1 then
      if σ.1 = 1 then 1 else if σ.1 = g then Complex.I
        else if σ.1 = g ^ 2 then -1 else -Complex.I
    else if j = 2 then
      if σ.1 = 1 ∨ σ.1 = g ^ 2 then 1 else -1
    else
      if σ.1 = 1 then 1 else if σ.1 = g then -Complex.I
        else if σ.1 = g ^ 2 then -1 else Complex.I) 1

def v4Row (a b : S4) (j : Fin 4) {H : Subgroup S4} : IrrepDatum H :=
  mkRow (fun σ =>
    if j = 0 then 1
    else if σ.1 = 1 then 1
    else if j = 1 then if σ.1 = a then -1 else if σ.1 = b then 1 else -1
    else if j = 2 then if σ.1 = a then 1 else if σ.1 = b then -1 else -1
    else if σ.1 = a ∨ σ.1 = b then -1 else 1) 1

/-- Executable class code on the chosen `S₃`: identity, transposition, or three-cycle. -/
def s3Class (σ : S4) : Fin 3 :=
  if h0 : σ = 1 then 0
  else if h1 : σ * σ = 1 then 1
  else 2

def s3Row (j : Fin 3) : IrrepDatum (representative .s3) :=
  mkRow (fun σ =>
    if j = 0 then 1
    else if j = 1 then if s3Class σ.1 = 1 then -1 else 1
    else if s3Class σ.1 = 0 then 2 else if s3Class σ.1 = 2 then -1 else 0)
    (if j = 2 then 2 else 1)

def d8LinearValue (g s σ : S4) (eg es : Bool) : ℂ :=
  if σ = 1 then 1
  else if σ = g then if eg then -1 else 1
  else if σ = g ^ 2 then 1
  else if σ = g ^ 3 then if eg then -1 else 1
  else if σ = s then if es then -1 else 1
  else if σ = s * g then if Bool.xor eg es then -1 else 1
  else if σ = s * g ^ 2 then if es then -1 else 1
  else if Bool.xor eg es then -1 else 1

def d8Row (j : Fin 5) : IrrepDatum (representative .d8) :=
  let g := ConcretePerm.cycle0123
  let s := ConcretePerm.t02
  if h0 : j = 0 then trivialRow _
  else if h1 : j = 1 then mkRow (fun σ => d8LinearValue g s σ.1 true false) 1
  else if h2 : j = 2 then mkRow (fun σ => d8LinearValue g s σ.1 false true) 1
  else if h3 : j = 3 then mkRow (fun σ => d8LinearValue g s σ.1 true true) 1
  else mkRow (fun σ => if σ.1 = 1 then 2 else if σ.1 = g ^ 2 then -2 else 0) 2

def fixedCount (σ : S4) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => σ i = i).card

def a4PositiveClass : Finset S4 :=
  (representativeCarrier .v4Normal).image fun v =>
    v * ConcretePerm.cycle012 * v⁻¹

def inA4PositiveClass (σ : S4) : Prop := σ ∈ a4PositiveClass

private instance (σ : S4) : Decidable (inA4PositiveClass σ) :=
  by
    change Decidable (σ ∈ a4PositiveClass)
    infer_instance

def a4Row (j : Fin 4) : IrrepDatum (representative .a4) :=
  mkRow (fun σ =>
    if j = 0 then 1
    else if j = 3 then
      if σ.1 = 1 then 3 else if σ.1 * σ.1 = 1 then -1 else 0
    else if σ.1 = 1 ∨ σ.1 * σ.1 = 1 then 1
    else if inA4PositiveClass σ.1 then if j = 1 then omega else omega ^ 2
    else if j = 1 then omega ^ 2 else omega)
    (if j = 3 then 3 else 1)

/-- Executable conjugacy-class code on `S₄`: identity, transposition, double transposition,
three-cycle, and four-cycle, in that order. -/
def s4Class (σ : S4) : Fin 5 :=
  if h0 : σ = 1 then 0
  else if h1 : fixedCount σ = 2 then 1
  else if h2 : σ * σ = 1 then 2
  else if h3 : fixedCount σ = 1 then 3
  else 4

def s4Row (j : Fin 5) : IrrepDatum (representative .s4) :=
  mkRow (fun σ =>
    if j = 0 then 1
    else if j = 1 then
      if s4Class σ.1 = 1 ∨ s4Class σ.1 = 4 then -1 else 1
    else if j = 2 then
      if s4Class σ.1 = 0 then 3
      else if s4Class σ.1 = 1 then 1
      else if s4Class σ.1 = 2 then -1
      else if s4Class σ.1 = 3 then 0 else -1
    else if j = 3 then
      if s4Class σ.1 = 0 then 3
      else if s4Class σ.1 = 1 then -1
      else if s4Class σ.1 = 2 then -1
      else if s4Class σ.1 = 3 then 0 else 1
    else if s4Class σ.1 = 0 then 2
      else if s4Class σ.1 = 1 then 0
      else if s4Class σ.1 = 2 then 2
      else if s4Class σ.1 = 3 then -1 else 0)
    (if j = 0 ∨ j = 1 then 1 else if j = 4 then 2 else 3)

/-- Number of irreducible rows for each representative. -/
def rowCount : SubgroupKind → Nat
  | .trivial => 1
  | .c2Transposition => 2
  | .c2DoubleTransposition => 2
  | .c3 => 3
  | .c4 => 4
  | .v4Normal => 4
  | .v4Disjoint => 4
  | .s3 => 3
  | .d8 => 5
  | .a4 => 4
  | .s4 => 5

/-- The indexed character row for a representative subgroup. -/
def rowOfIndex : (k : SubgroupKind) → Fin (rowCount k) → IrrepDatum (representative k)
  | .trivial => fun _ => trivialRow _
  | .c2Transposition => fun i => if i.val = 0 then trivialRow _ else c2NontrivialRow
  | .c2DoubleTransposition => fun i => if i.val = 0 then trivialRow _ else c2NontrivialRow
  | .c3 => fun i => if i.val = 0 then trivialRow _
      else if i.val = 1 then c3Row ConcretePerm.cycle012 false else c3Row ConcretePerm.cycle012 true
  | .c4 => fun i => c4Row ConcretePerm.cycle0123 i
  | .v4Normal => fun i => v4Row ConcretePerm.double01_23 ConcretePerm.double02_13 i
  | .v4Disjoint => fun i => v4Row ConcretePerm.t01 ConcretePerm.t23 i
  | .s3 => fun i => s3Row i
  | .d8 => fun i => d8Row i
  | .a4 => fun i => a4Row i
  | .s4 => fun i => s4Row i

/-- The finite list version of the table. -/
def subgroupTable (k : SubgroupKind) : List (IrrepDatum (representative k)) :=
  List.ofFn (rowOfIndex k)

theorem mem_subgroupTable_iff {k : SubgroupKind} {row : IrrepDatum (representative k)} :
    row ∈ subgroupTable k ↔ ∃ i : Fin (rowCount k), row = rowOfIndex k i := by
  simp [subgroupTable, eq_comm]

/-- There are thirty-seven rows across the eleven tables. -/
theorem total_row_count :
    (Finset.univ.sum fun k : SubgroupKind => rowCount k) = 37 := by
  native_decide

end PermanentalDominance.N4
