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

## References

- J. S. Milne, [*Basic Theory of Affine Group Schemes*, XIII §3,
  item 3.14](https://www.jmilne.org/math/CourseNotes/AGS.pdf):
  a field-base functorial decomposition with the diagonal factor on the
  **right**. The present section-first scheme isomorphism, inverse with left
  normalization and smoothness argument are not assertions of that proof.
- J. S. Milne, *Algebraic Groups*, §2.8: the field-base GL coordinates and a
  mention of SL, not the arbitrary-base split-kernel or smoothness argument.
- [SplitKernelProduct](../../GroupObject/SplitKernelProduct.lean) supplies the
  categorical isomorphism and readbacks;
  [SpecialLinearKernel](../SpecialLinearKernel.lean) supplies its kernel square.
  [GeneralSpecialLinearSmooth](../GeneralSpecialLinearSmooth.lean) establishes
  the smooth SL structure morphism. Mathlib's
  `AlgebraicGeometry/Morphisms/Smooth.lean` supplies base-change stability,
  applied to the second projection.

For a pinned project checkout, fetch the matching mathlib cache before
focused builds:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct
lake build AlgebraicGroupsTest.GeneralLinearDeterminantProduct
```

The focused imports are also reached by the aggregate production import and
the default-build test roots.
