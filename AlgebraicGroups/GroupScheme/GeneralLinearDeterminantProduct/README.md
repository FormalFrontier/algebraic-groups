# Finite determinant: actual scheme product and smoothness

For any commutative ring `K`, finite decidable index type `n`, and explicit
`pivot : n`, `AlgebraicGeometry.generalLinearDeterminantProductIso` gives an
isomorphism in `Over (Spec (.of K))`:

```
specialLinearGroupUnderlyingScheme K n ⊗ multiplicativeGroupUnderlyingScheme K
  ≅ generalLinearGroupUnderlyingScheme K n
```

Its forward map is `(s,t) ↦ diagonalSection(t) * inclusion(s)`. Its inverse is
`g ↦ (kernelLift (diagonalSection(det(g))⁻¹ * g), det(g))`, with the indicated
noncommutative multiplication order. The public triangle and inverse-readback
theorems identify the genuine determinant projection and normalized kernel lift,
not merely values on affine points. This is an isomorphism of **underlying
schemes over the base**, not a direct-product group-scheme isomorphism.

`generalLinearDeterminantSchemeHom_smooth` proves `Smooth` of the actual scheme
map `(generalLinearDeterminantSchemeHom K n).hom.hom.left`: the second projection
is the base change of the smooth special-linear structure morphism and the
product iso transports this smoothness to determinant. Rank one and the zero
ring are covered; rank zero is deliberately **not** claimed because no `pivot`
exists. There are no field, reducedness, nontrivial-ring, flat-descent, or
pointwise-test assumptions.

The module reuses `AlgebraicGroups.GroupObject.SplitKernelProduct` for the
abstract product and the published `AlgebraicGroups.GroupScheme` determinant,
section, kernel pullback and smoothness APIs. For a pinned project checkout,
run `lake exe cache get` before focused warning-fatal builds:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct
lake build AlgebraicGroupsTest.GeneralLinearDeterminantProduct
```

The producer and its persistent ordinary-import client were originally authored
by a separate Formalization Worker B execution. Exact contribution, review and
release decisions are recorded outside this shipping guide. The focused imports
are also reached by the aggregate production import and the default-build test
roots; build success alone is not release acceptance.
