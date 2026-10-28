# Canonical diagonal group schemes

Use `TauCeti.SplitTorus.groupScheme K ι`, represented by `MonoidAlgebra K (Multiplicative (ι →₀
ℤ))`. Its points are unit tuples via `TauCeti.SplitTorus.pointsMulEquiv`; its characters give
canonical projection maps to `TauCeti.DiagonalizableGroup.multiplicativeGroupScheme`. The
duplicate diagonal GL quotient and its external scheme wrappers are removed. Independently,
`Matrix.DiagonalGroup` retains native arbitrary-index matrix-subgroup mathematics and
`unitsEquiv`. The retained `DiagonalProduct` module proves the categorical product universal
property against arbitrary test schemes, and `DiagonalDimension` proves the
polynomial-localization presentation and dimension. Empty indices, zero rings and nonreduced
test algebras remain included.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/Diagonal/README.md) preserves the full context.
Current APIs are described above.

Milne, *Algebraic Groups* (2017), §§2.8–2.9 (pp. 41–42), defines the
determinant-localized `GL_n` and its diagonal algebraic subgroup `D_n` over a
field and its algebras; §12.d (p. 234, after Definition 12.11) identifies
`D_n` with a product of `Gₘ`. This library extends the base to arbitrary
commutative rings and proves the Hopf-quotient and represented-group claims.
The group and Hopf-coordinate constructions use Mathlib's
`Mathlib.Data.Matrix.Basic`, `Mathlib.Algebra.Group.Pi.Units`,
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
`Mathlib.RingTheory.HopfAlgebra.Quotient`, and
`Mathlib.AlgebraicGeometry.Group.Affine`; the GL coordinate ring and group
scheme are provided by `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing`
and `AlgebraicGroups.GroupScheme.GeneralLinear`.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
