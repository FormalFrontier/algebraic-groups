# Categorical products of canonical split tori

Import `AlgebraicGroups.GroupScheme.DiagonalProduct`. `diagonalGroupHomUnits` classifies maps
from any scheme over `Spec K` to `TauCeti.SplitTorus.groupScheme K ι` by families of global
units. The actual character projections give `diagonalGroupProductFanForgetIsLimit`,
`diagonalGroupProductFanIsLimit` and `diagonalGroupSchemeProductIso`, including the empty
terminal case. The theorem concerns the categorical group-scheme product, beyond a pointwise
unit-tuple equivalence. The old diagonal model and deprecated aliases are removed.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/DiagonalProduct/README.md) preserves the full context.
Current APIs are described above.

Milne, *Algebraic Groups* (2017), §2.9 (p. 42) introduces `D_n` over
algebras of a field, and §12.d (p. 234, after Definition 12.11) identifies
it with a finite product of `Gₘ`. The construction here proves the product
universal property for possibly nonaffine test schemes over a commutative base.
It uses Mathlib's `Mathlib.AlgebraicGeometry.Group.Affine`
(`algΓAlgSpecAdjunction`),
`Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`, and
`Mathlib.CategoryTheory.Limits.Shapes.Products` and
`Mathlib.CategoryTheory.Limits.Shapes.IsTerminal`, together with
`AlgebraicGroups.GroupScheme.Multiplicative` and
`AlgebraicGroups.GroupScheme.Diagonal`.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
