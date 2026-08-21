# Permanental Dominance Conjecture

This repository contains a Lean formalization and a mathematical manuscript for the normalized permanental-dominance theorem in dimension four.

## Status

The result proves that for every subgroup $H \le S_4$, every irreducible finite-dimensional complex representation $V$ of $H$, and every positive-semidefinite complex $4 \times 4$ matrix $A$, the normalized generalized matrix function attached to $V$ is bounded above by the permanent (on real parts; both quantities are also proved real).

The main public theorems are:

- `PermanentalDominance.N4.normalized_permanental_dominance_n4`
- `PermanentalDominance.N4.normalized_permanental_dominance_n4_real`

This is the complete $n=4$ result. It is not a proof in arbitrary dimension.

## Repository layout

- `Lean/`: a standalone Lean 4 project containing the formal proof, an axiom audit, and a proof map.
- `LaTeX/`: the original paper source and compiled PDF of the direct geometric proof.
- `preprint/`: a self-contained ELA/SIAM submission build with cited literature, BibTeX, generated bibliography, and compiled PDF.
- `README.md`: scope, status, and build instructions.

## Proof route

The proof has three main layers:

1. classify the subgroup and irreducible-character rows that can occur inside $S_4$;
2. reduce the positive-semidefinite matrix problem to correlation data and discharge all routine rows;
3. handle the remaining non-real $A_4$ rows by a direct residual-vector/Gram-geometric certificate, then assemble the registry into the final theorem.


## Verification

To verify the formalization, install Lean through `elan`, then run:

```sh
cd Lean
./verify.sh
```

The project pins Lean and Mathlib through `Lean/lean-toolchain` and `Lean/lakefile.toml`.

To rebuild the manuscript PDF, install a standard TeX Live distribution with `latexmk`, then run:

```sh
cd LaTeX
latexmk -pdf -interaction=nonstopmode -halt-on-error PermanentalDominanceN4.tex
```

To rebuild the ELA preprint with its bibliography, run:

```sh
cd preprint
latexmk -pdf -interaction=nonstopmode -halt-on-error permanental_dominance_n4.tex
```
