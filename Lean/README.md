# Lean formalization

This directory is a standalone Lean project for the normalized permanental-dominance theorem in dimension four.

## Toolchain

- Lean: `v4.19.0`
- Mathlib: `v4.19.0`

Both versions are pinned in the project files.

## Build and audit

From this directory:

```sh
./verify.sh
```

The script runs `lake build` and then elaborates `AxiomAudit.lean`.

## Public API

Import `PermanentalDominance` to obtain the two final endpoints:

```lean
PermanentalDominance.N4.normalized_permanental_dominance_n4
PermanentalDominance.N4.normalized_permanental_dominance_n4_real
```

Selected geometric certificate endpoints are also available:

```lean
PermanentalDominance.N4.A4GeometricPSD.geometricP_nonneg_of_posSemidef
PermanentalDominance.N4.A4GeometricFourVector.fourVectorProperty
PermanentalDominance.N4.A4GeometricBridge.certificate_posSemidef_geometric
```

See `FORMALIZATION_MAP.md` for the dependency-level proof outline.

## Scope and trust boundary

The source set is the exact internal import closure of the final (n=4) theorem at the provenance commit recorded in the root README. It excludes unrelated NIEP developments and the superseded spectral/scalar-certificate route. A source scan of this closure finds no `sorry`, `admit`, custom `axiom`, or `unsafe` declarations. `AxiomAudit.lean` asks Lean to print the axioms of the public endpoints.
