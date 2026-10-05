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

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.2: the multiplicative group;
  item 2.9: diagonal, unitriangular and upper-triangular groups over a field;
  item 2.40: field-case triangular coordinate rings and integrality. These
  passages are not cited for the arbitrary-base smoothness or geometric-fiber
  proofs here.
- J. S. Milne, preliminary *Algebraic Groups* course notes, v2.00 (2015),
  Definition 2.20 and Proposition 2.21: the triangular splitting and its
  split-kernel criterion over a field. These locators are not item 2.9 of the
  2017 book; the isomorphism used here is of underlying over-schemes, not group
  products.
- Mathlib, `Mathlib.RingTheory.Smooth.StandardSmooth` (polynomial localization),
  `Mathlib.RingTheory.TensorProduct.MonoidAlgebra` (field scalar extension),
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` and
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (geometric fibers).
  The local `DiagonalProduct`, `UnitriangularGeometry`, `UpperTriangularSplitKernel`,
  `GroupObject.SplitKernelProduct` and `Scheme.Smooth` modules provide separate
  previously formalized ingredients; see [CREDITS](../../../CREDITS.md) for
  their contributor credit.
