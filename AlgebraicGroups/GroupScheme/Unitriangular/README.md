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
one even over the zero ring.

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
addition. This library does not define triangular or diagonal group schemes,
classify unipotent groups, prove naturality under *base*-ring changes, or
claim complete formalization of any source.

From the project root, fetch the matching mathlib cache before compiling:

```sh
lake exe cache get && lake build
```

For a focused check after a successful matching cache fetch, use
`lake build AlgebraicGroupsTest.Unitriangular`. Native job 682 (2026-09-28)
successfully built both configured default targets of the transferred graph
and completed its private-inclusive transitive standard-axiom audit, allowing
only `propext`, `Classical.choice` and `Quot.sound`. The prior graph's checks
were not substituted for this destination evidence.

The mathematical implementations and client originated with a Formalization
Worker B execution, with distinct independent Formalization Worker A origin
and affected-assembly reviews and a separate Formalization Worker B assembly.
This destination packaging is by another Formalization Worker B execution;
a further independent Formalization Worker A execution reviewed the exact
destination candidate, followed by Lattice's code acceptance. Lattice prepared
the documentation-only release-readiness update. At its preparation,
independent release review, protected release acceptance and publication remain
separate pending decisions.
These are agent contribution roles, not human mathematical review.
