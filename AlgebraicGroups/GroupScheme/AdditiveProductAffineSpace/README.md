<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Finite products of additive group schemes

Import `AlgebraicGroups.GroupScheme.AdditiveProductAffineSpace`. Given
`K : Type u` with `[CommRing K]` and `D : Type u` with `[Fintype D]`,
`additiveGroupProductUnderlyingSpecIso K D` identifies the **underlying
over-scheme** of the actual categorical group-scheme product
`∏ᶜ fun _ : D => additiveGroupScheme K` with the spectrum of
`MvPolynomial D K` over `Spec K`. Composing with
`additiveGroupAffineProductSpecToSpaceIso` gives
`additiveGroupProductUnderlyingAffineSpaceIso`, the underlying affine
`D`-space comparison. Neither result is a group-scheme or Hopf-algebra
isomorphism.

`additiveProductCoordinateAlgHom K D d` sends the additive coordinate to
`MvPolynomial.X d`. Its over-scheme map
`additiveGroupAffineProductProjection K D d` is the `d`-th projection of
the affine candidate. `additiveGroupAffineProductFan_isLimit K D` proves the
universal property for maps from **every** scheme over `Spec K`, including
nonaffine schemes: `affineSpecHomOverEquiv` relates an affine target to its
algebra maps into global sections, `additiveGroupHomOverEquiv` reads a single
section, and `MvPolynomial.aeval` collects the sections. Both equivalences
live in the independent `AlgebraicGroups.GroupScheme.AffineHomOver` module
and work over any commutative base ring.

`additiveGroupProductUnderlyingFan_isLimit` identifies the cone obtained
from the genuine group-object product. Comparing the two limit cones gives
the spectrum isomorphism;
`additiveGroupProductUnderlyingSpecIso_hom_projection` identifies its
composite with each *actual* group-product projection. For a map from any
over-scheme, `additiveGroupProductUnderlyingAffineSpaceIso_coordinate`
reads the corresponding global polynomial coordinate after transport back
through the polynomial-spectrum comparison. This is not a claim about a
separate `AffineSpace.coord` map.

The theorem requires neither a field nor nonempty `D` nor a nonzero ring:
`D = Fin 0` gives the empty product and `K = ZMod 1` is allowed. Its
ordinary-import clients, including these edge cases and the actual
projection law, are registered in
`AlgebraicGroupsTest.GroupScheme.AdditiveProductAffineSpace`. With pinned
dependencies, fetch the matching mathlib cache with `lake exe cache get`
and run `lake build AlgebraicGroupsTest.GroupScheme.AdditiveProductAffineSpace`
to build this client.

## References

Milne, *Algebraic Groups* (2017), item 2.1 describes the additive group.
Item 2.6 gives a chosen-basis group-scheme isomorphism `Gₐ^n ≃ Vₐ` for a
finite-dimensional vector space over a field, a published antecedent for
finite additive products. The project's `VectorProduct` module formalizes
this field/basis product as `vectorGroupSchemeProductIso`. The result here
instead identifies the **underlying over-scheme** of the literal finite
product with `Spec (MvPolynomial D K)` and affine `D`-space for arbitrary
commutative `K`, without asserting a group-scheme isomorphism. The Lean
construction follows Mathlib's `algΓAlgSpecAdjunction` for affine targets
and global sections,
`MvPolynomial.aeval` for freely chosen coordinates,
`Limits.productIsProduct` and `Grp.forget` for genuine categorical products,
and `AffineSpace.SpecIso` for the underlying affine-space identification.
The local `Additive` and `AffineHomOver` modules provide the additive scheme
and the over-scheme map/section equivalences used here.

Formal Frontier Agents contributed this Lean comparison and proof, rather
than claiming invention of the underlying mathematical constructions. See
[credits and bibliography](../../../CREDITS.md) for the sources and attribution.
