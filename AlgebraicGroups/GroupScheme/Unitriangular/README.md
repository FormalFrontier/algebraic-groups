# Upper-unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.Unitriangular` (or `AlgebraicGroups`) to use
the affine finite-type group scheme
`AlgebraicGeometry.unitriangularGroupScheme K n` over any commutative ring `K`
and finite linearly ordered index type `n`. Its points form the subgroup
`Matrix.UnitriangularGroup n R` of `Matrix.GeneralLinearGroup n R`: entries
below the diagonal vanish, and diagonal entries equal one. Inverse closure
uses matrix-unit invertibility, not a field hypothesis.

`UnitriangularCoordinateRing.CoordinateRing K n` is the Hopf quotient of the
determinant-localized general-linear coordinate algebra. Its ideal is generated
by lower entries and diagonal-minus-one relations. The coideal descends in the
tensor product of both quotient algebras, and the antipode uses the invertible
universal GL matrix. `coordinatePolynomialEquiv K n` identifies this localized
quotient with the quotient of the unlocalized, all-entry polynomial ring by
the same relations; `polynomialEquiv K n` reverses that bridge.
`polynomialFreeEquiv K n` presents the all-entry quotient as the free
polynomial algebra on `UnitriangularCoordinateRing.StrictUpperPair n`, and
`freeEquiv K n` composes the bridges. The determinant and its inverse become
one even over the zero ring. These are algebra equivalences, not
identifications of the represented group scheme with an additive group
scheme or equivalences of the specified Hopf structures.

`AlgebraicGeometry.unitriangularInclusion K n` and
`unitriangularInclusion_isClosedImmersion` give the closed GL group-scheme
inclusion. `unitriangularGroupMulEquivAlgHom K n R` and
`unitriangularGroupMulEquivPoints K n R` identify its `K`-algebra points
multiplicatively with native units. `unitriangularGroupPointsIso K n` is
natural in the coefficient algebra, with determinant-inverse and entry
readbacks. `unitriangularInclusion_point` identifies the inclusion on points;
`Matrix.UnitriangularGroup.map`, `unitriangularToGL_natural` and
`unitriangularFromGL_natural` express coefficient-map naturality.

The ordinary-import client `AlgebraicGroupsTest.Unitriangular` contains ten
anonymous examples covering `Fin 2` multiplication, the genuine `Fin 3`
cross term, algebra maps and the inclusion square, together with `Fin 0`,
`Fin 1` and zero-ring boundaries. The general group law is not coordinate-wise
addition. This focused module does not itself construct triangular or diagonal
group schemes or compare changes of the base ring. Those are separate developments:
see the [upper-triangular](../UpperTriangular/README.md) and
[diagonal](../Diagonal/README.md) guides, the
[unitriangular base-change module](../UnitriangularBaseChange.lean), and its
[identity and scalar-tower coherence guide](../../../docs/UnitriangularSchemeBaseChangeCoherence.md).
The base-change comparisons and these coherence laws do not assert unrestricted
naturality for all group-scheme morphisms. This library does not classify
unipotent groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.8–2.9: `GL_n` as a functor on
  commutative algebras over a field, and its upper-unitriangular subgroup
  with the unlocalized polynomial-quotient presentation. The group scheme
  here also admits arbitrary commutative base rings and empty indices.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` and
  `Mathlib/LinearAlgebra/Matrix/Block.lean`: matrix units and triangular
  product, inverse and determinant results;
  `Mathlib/RingTheory/HopfAlgebra/Quotient.lean` and
  `Mathlib/RingTheory/Bialgebra/Quotient.lean`: Hopf-ideal quotient machinery.
* `AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` supplies the
  localized GL coordinate algebra and its matrix laws;
  `AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean` supplies the
  earlier comparison between a GL Hopf quotient and a polynomial quotient.

For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
