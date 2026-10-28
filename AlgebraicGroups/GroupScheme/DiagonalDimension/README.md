# Dimension of canonical split tori

Import `AlgebraicGroups.GroupScheme.DiagonalDimension`. The coordinate algebra is `MonoidAlgebra
K (Multiplicative (ι →₀ ℤ))`. Its retained polynomial-localization equivalence and variable
formulas give coordinate-ring and underlying-scheme dimension `Fintype.card ι` over every field.
The algebra presentation holds over arbitrary commutative rings, including zero rings and empty
indices. Dimension uses the canonical localization theorem rather than a duplicate
supplied-point helper.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/DiagonalDimension/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), item 2.9: diagonal matrices over a
  field. The general-base ideal equality and the field dimension calculation
  here are not claimed as statements of that passage.
- Mathlib, `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.RingTheory.Spectrum.Prime.Topology`: polynomial and affine-spectrum
  dimension. The local supplied-point localization and coordinate-elimination
  results cited above are distinct earlier Formal Frontier implementations.
- Contributor credit appears in the repository's [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
