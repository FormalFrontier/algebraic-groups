# Current release context (2026-09-29)

Official P9 `8fdf180d3b56c6bfb4a5fe8c63204ad9a7abf827` includes the
generation/derived results described below. Accepted development main
`45d4c5ddfcd491f298c4c968561d2e2eccf82e06` additionally includes
the native point-group exponent transfer, checked in original destination
job 932 and independently reviewed; its own release is still pending.
The 2026-09-28 context below is dated history, not a current count or
publication status. No new group-scheme assertion follows from exponent.

## Dated release context (2026-09-28; historical)

The group-scheme construction below was published in an earlier official
release, and the subsequent sharpness result is published at official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8`. The separate native
point-group lower-central equality, checked in original native job 865 on
the then-143-module graph, was published at official P8
`441817ab159b20bb7c9c855b05d49abfa3d85c92`. Development main
`a77d4e4d19f6dc366eb9a40f16503f5855421cf3` additionally integrates
positive-stage generation, exact commutators and native derived series:
original native run 895 checked both default targets and all 3,679 audited
module-origin pairs across 145 total Lean modules (107 production, 38 tests),
including 1,168 private-named and all generated origins under only the
standard three axioms. Fresh independent destination review and maintainer
code acceptance/protected integration are complete; this contribution's own
release review, acceptance and publication remain pending. These native
point-group results assert no new group-scheme constructions. The final
paragraph below describes this group-scheme module's earlier preparation,
not the current release status.

---

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
