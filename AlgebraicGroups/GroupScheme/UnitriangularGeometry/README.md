# Geometry of canonical unitriangular groups

Import `AlgebraicGroups.GroupScheme.UnitriangularGeometry`. The underlying spectrum of
`TauCeti.UpperUnitriangular.coordinateHopfAlgebra` is affine space on strict upper pairs.
Retained results give smooth structure morphisms, geometrically integral fibers, integral total
spaces over domains and field dimension equal to the number of strict upper pairs. Empty ranks
and zero rings are permitted in relative assertions. The affine-space comparison is an
underlying-scheme result; the unitriangular product is not coordinatewise addition.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), item 2.9: the unitriangular
  polynomial-coordinate presentation over a field. The over-scheme isomorphism
  and the relative geometric statements for all commutative rings follow from
  the existing `UnitriangularCoordinateRing.freeEquiv` and the APIs below;
  they are not attributed wholesale to this passage.
- Mathlib, `Mathlib.AlgebraicGeometry.AffineSpace` (Andrew Yang's affine-space
  `SpecIso` and Justus Springer's geometric-integrality instance),
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
  `Mathlib.RingTheory.Smooth.StandardSmooth` (smoothness),
  `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.Data.Fintype.Prod` (field dimension and strict-pair count).
- The [unitriangular group-scheme guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/Unitriangular/README.md) describes
  the earlier polynomial equivalence and Hopf quotient; the geometry in this
  guide does not equate its group law with affine-space addition.
