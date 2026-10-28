# Dimension of canonical upper-triangular groups

Import `AlgebraicGroups.GroupScheme.UpperTriangularDimension`. The statements concern
`TauCeti.GeneralLinear.UpperTriangular` at numerical rank `N`. The retained
polynomial-localization presentation and coordinate formulas identify the canonical Hopf algebra
with polynomial coordinates on the retained upper entries and invertible diagonal product. Over
any field the ring and underlying-scheme dimension is `N + N.choose 2`, including rank zero.
Algebra presentations allow arbitrary commutative bases and zero rings.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UpperTriangularDimension/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), items 2.9 and 2.40: triangular
  matrices and their coordinate algebra over a field. The ideal equality over
  arbitrary rings and the field dimension calculation are proved here, not
  asserted as dimension statements in the cited passages.
- Mathlib, `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.RingTheory.Spectrum.Prime.Topology`: dimension of polynomial rings
  and affine spectra. The separate local
  `AlgebraicGroups.Algebra.LocalizedCoordinateQuotient`,
  `AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension` and
  `AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices` modules supply
  the elimination equivalence, supplied-point dimension theorem and count.
- Contributor and third-party credit appears in the repository's
  [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
