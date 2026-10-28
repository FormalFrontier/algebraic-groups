<!-- SPDX-License-Identifier: Apache-2.0 -->

# Closed stages on canonical unitriangular coordinates

Import `AlgebraicGroups.GroupScheme.UnitriangularStages`. Stage vanishing ideals and their Hopf
quotients are constructed directly on the canonical Tau Ceti polynomial unitriangular Hopf
carrier. Retained successor inclusions, point formulas and closed immersions allow arbitrary
commutative bases, empty ranks and exhausted stages. Normality, whole-superdiagonal coordinates,
affine-space presentations, projection sections of underlying schemes and the successor kernel
are in their focused modules. An affine-space coordinate presentation does not make the group
additive or split the group morphism.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UnitriangularStages/README.md) preserves the full context.
Current APIs are described above.

Milne's full unitriangular functor over a field is evaluated on every
commutative algebra over that field. His finer filtration by individual
entries has whole-stage superdiagonal block endpoints; its subgroup and
one-entry quotient results
antecede the field-case stages here. The Hopf quotients and natural functors
below also cover arbitrary commutative base rings.

- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field*, Cambridge University Press, 2017, item 2.9 (the unitriangular
  group functor and polynomial coordinate ring), Example 6.36 and §6.49
  (the finer normal central filtration and its one-entry additive quotients).
- Mathlib contributors, `Mathlib.RingTheory.HopfAlgebra.Quotient` (Hopf ideals
  and their quotients), `Mathlib.AlgebraicGeometry.Group.Affine` (`hopfSpec`),
  and `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (closed immersion
  induced by a surjective coordinate map).
- The existing `UnitriangularCoordinateRing` and `Unitriangular` group scheme supply the
  full-group coordinates and multiplicative point comparison.

With the repository's pinned toolchain and dependency cache ready, scoped
checks run as:

```sh
lake exe cache get
lake build AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
lake build AlgebraicGroups.GroupScheme.UnitriangularStages
lake build AlgebraicGroupsTest.GroupScheme.UnitriangularStages
```
