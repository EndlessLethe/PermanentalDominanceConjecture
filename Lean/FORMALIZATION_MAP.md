# Formalization map

The public endpoint is:

```text
normalized_permanental_dominance_n4
└─ FinalAssembly
   ├─ RepresentativeCompletenessRegistry
   │  ├─ subgroup representatives and carrier completeness
   │  └─ realization/classification of simple complex representations
   └─ RepresentativeDominanceRegistry
      ├─ abelian, low-order, D₈, and S₄ character rows
      └─ A4Registry
         └─ A4Gap
            └─ A4GeometricBridge
               └─ A4GeometricFourVector
                  └─ A4GeometricPSD
                     ├─ A4GeometricMinimum
                     ├─ A4GeometricNoncollinear
                     ├─ A4GeometricCollinear
                     ├─ A4GeometricQuadratic
                     ├─ A4GeometricGram
                     └─ A4GeometricNormalization
```

## Layer 1: general definitions

`Basic`, `PSD`, `Completion`, `Gauge`, and `GramExtension` define generalized matrix functions, positive semidefiniteness, normalization/completion tools, phase gauges, and Gram extensions.

## Layer 2: finite $n=4$ classification

`SubgroupRegistry`, `CharacterTables`, the realization modules, and the completeness registries reduce every subgroup of $S_4$ and every simple complex representation to a finite list of registered rows.

## Layer 3: rowwise dominance

The table-bridge and registry modules prove the required inequality for the routine rows. `S4Cases` still imports `SpectralThreeCycle` for a concrete three-cycle computation; this shared lemma is part of the active dependency closure and is distinct from the omitted spectral-certificate route.

## Layer 4: the exceptional non-real $A_4$ rows

`A4Gap` expands the remaining character rows into a certificate problem. The active proof passes through:

```text
positive-semidefinite correlation matrix
→ normalized residual Gram data
→ nonnegativity of the geometric polynomial
→ four-vector property
→ positive-semidefinite certificate
→ A₄ row dominance
```

The direct geometric bridge is `A4GeometricBridge.certificate_posSemidef_geometric`.

## Layer 5: final assembly

`RepresentativeDominanceRegistry` supplies dominance for every registered row, while `RepresentativeCompletenessRegistry` proves every simple representation is represented. `NormalizedPermanentalDominance` combines them into the public theorem.
