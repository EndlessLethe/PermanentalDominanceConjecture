# Permanental Dominance Conjecture

This repository contains a Lean formalization of the normalized permanental-dominance theorem in dimension four.

## Status

The formalized result proves that for every subgroup (H \le S_4), every irreducible finite-dimensional complex representation (V) of (H), and every positive-semidefinite complex (4 \times 4) matrix (A), the normalized generalized matrix function attached to (V) is bounded above by the permanent (on real parts; both quantities are also proved real).

The main public theorems are:

- `PermanentalDominance.N4.normalized_permanental_dominance_n4`
- `PermanentalDominance.N4.normalized_permanental_dominance_n4_real`

This is the complete (n=4) result. It is not a proof in arbitrary dimension.

## Repository layout

- `Lean/`: a standalone Lean 4 project containing the formal proof, an axiom audit, and a proof map.
- `README.md`: scope, status, and build instructions.

A manuscript directory will be added when there is a standalone paper to build; this repository does not include empty publication scaffolding.

## Proof route

The formal proof has three main layers:

1. classify the subgroup and irreducible-character rows that can occur inside (S_4);
2. reduce the positive-semidefinite matrix problem to correlation data and discharge all routine rows;
3. handle the remaining non-real (A_4) row by a direct residual-vector/Gram-geometric certificate, then assemble the registry into the final theorem.

The active (A_4) path is geometric. The older characteristic-polynomial/scalar-certificate alternative is intentionally not included.

## Verification

Install Lean through `elan`, then run:

```sh
cd Lean
./verify.sh
```

The project pins Lean and Mathlib through `Lean/lean-toolchain` and `Lean/lakefile.toml`.

## Provenance

The proof was extracted from [`EndlessLethe/math`](https://github.com/EndlessLethe/math) at merge commit [`c5e4d8c61f08d05ffe7c28bfa1ea732d8827b485`](https://github.com/EndlessLethe/math/commit/c5e4d8c61f08d05ffe7c28bfa1ea732d8827b485). Only the dependency closure of the final (n=4) geometric route is carried here.
