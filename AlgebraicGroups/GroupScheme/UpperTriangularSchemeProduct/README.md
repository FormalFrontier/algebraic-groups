# Represented U-first triangular products

Import `AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`. On the canonical Tau Ceti
upper-triangular, unitriangular and split-torus models at numerical rank `N`, the retained
underlying over-scheme isomorphism is `U ⊗ D ≅ T`. Its forward map is `i(u)e(d)`, and its
inverse uses the diagonal and column normalization. Conjugation scales `(i,j)` by `dᵢ dⱼ⁻¹`;
multiplication is the U-first semidirect law, not the direct-product group law. Arbitrary
commutative bases, zero rings, rank zero and all test schemes are included where stated.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md) preserves the full context.
Current APIs are described above.

* J. S. Milne, *Algebraic Groups* (course notes, version 2.00), §§2.20–2.21:
  the field-base upper-triangular split and semidirect product. The
  categorical U-first coordinate change, arbitrary-base scheme isomorphism
  and arbitrary-test twisted law here go beyond that example.
* `AlgebraicGroups/GroupObject/SplitKernelProduct.lean` and
  `AlgebraicGroups/GroupObject/SplitKernelSemidirect.lean` give the earlier
  categorical section-first product and conjugation laws used by the
  specialized construction. The [split-kernel producer](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean)
  supplies the actual represented kernel and section.
* Mathlib, `Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean`: group-object
  multiplication and inversion of arrows from arbitrary test objects.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
