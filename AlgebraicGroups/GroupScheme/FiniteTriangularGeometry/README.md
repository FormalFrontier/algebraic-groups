# Relative geometry of finite triangular group schemes

Import `AlgebraicGroups.GroupScheme.FiniteTriangularGeometry` for the native
structural morphisms to `Spec K`. For every `[CommRing K]`, the module provides
`Smooth` and `GeometricallyIntegral` instances for
`multiplicativeGroupUnderlyingScheme K`,
`diagonalGroupUnderlyingScheme K index` with `[Fintype index] [DecidableEq index]`,
and `upperTriangularGroupUnderlyingScheme K index` with
`[Fintype index] [LinearOrder index]`. Under the additional `[IsDomain K]`
assumption, each **total underlying scheme** is `IsIntegral`. Relative
smoothness and geometric integrality do not require a domain, nonzero ring,
field, positive rank, or nonempty index type.

The multiplicative group uses its Laurent-polynomial coordinate algebra:
polynomial localization gives standard smoothness, and scalar extension to any
field gives an integral group algebra. The diagonal case uses the existing
finite product of multiplicative groups, including the terminal empty product.
The triangular case uses the existing section-first split-kernel isomorphism
of **underlying schemes** with the diagonal and unitriangular factors; it does
not assert a direct-product group law. This module uses the earlier AG
unitriangular relative geometry rather than reproving it.

Over a reducible base such as `ℤ × ℤ`, integral geometric fibers do not imply
an integral total scheme. Over the zero ring, the fiber condition is vacuous.
These instances alone give no Krull dimension or general product-dimension
formula; see the separate [native triangular dimension
module](../UpperTriangularDimension/README.md) for its field-specific result.
The [producer](../FiniteTriangularGeometry.lean) and [ordinary-import
client](../../../AlgebraicGroupsTest/GroupScheme/FiniteTriangularGeometry.lean)
exercise empty, singleton, nontrivial, domain, reducible and zero-ring cases.

From this repository's root, install its pinned Lean toolchain, fetch the
matching mathlib cache successfully, and build the focused producer and client:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups.GroupScheme.FiniteTriangularGeometry \
  AlgebraicGroupsTest.GroupScheme.FiniteTriangularGeometry
```

This geometry module and its client are contributions by Formal Frontier agents;
the pre-existing multiplicative, diagonal-product, unitriangular and split-kernel
APIs retain their own authorship and history.
