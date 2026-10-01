# Geometric integrality of finite general and special linear schemes

Import `AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral` or
`AlgebraicGroups` to use the
actual determinant-localized general linear coordinate algebra and its
determinant-one quotient. For any finite index type `n` with decidable equality:

* If `K` is a commutative integral domain, the existing
  `GeneralLinearCoordinateRing.CoordinateRing K n` and
  `SpecialLinearCoordinateRing.CoordinateRing K n` have `IsDomain` instances.
  The total spaces `(generalLinearGroupUnderlyingScheme K n).left` and
  `(specialLinearGroupUnderlyingScheme K n).left` have `IsIntegral` instances.
* For **every** commutative ring `K`, the genuine structure morphisms
  `(generalLinearGroupUnderlyingScheme K n).hom` and
  `(specialLinearGroupUnderlyingScheme K n).hom` have
  `GeometricallyIntegral` instances. In particular, every base change to a
  field algebra has an integral scheme as its fiber. Mathlib's native
  instances then provide geometric irreducibility and reducedness; no
  extra rank, field, domain, characteristic or nonzero-base hypothesis is
  imposed on the geometric statement.

The generic determinant is nonzero in the polynomial ring over a domain, so
its principal localization gives the GL domain. In nonempty ranks the
existing normalization section splits the *actual* SL quotient. In rank zero
the determinant is one and the defining ideal is bottom, giving the quotient
equivalence. For any field algebra `F` of `K`, polynomial coefficient extension
identifies `F ⊗[K] K[X]` with `F[X]` and carries the determinant to the generic
determinant over `F`. Coefficient base change of principal localization gives
a domain for `F ⊗[K] GL_K`; tensoring the SL **split equation** (not an arbitrary
injection) gives a domain for `F ⊗[K] SL_K`. The affine Spec pullback
isomorphism identifies these rings with the fibers of the actual morphisms.

Rank one is covered without a separate presentation theorem. Over `ℤ`, the
total spaces really are integral despite the base not being a field. Over the
zero ring (`ZMod 1`), there is no field algebra: geometric integrality of the
structure morphisms is vacuous, **not** an integral-total-space assertion.
Likewise, no integral total space is asserted over a nonintegral base.

`AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral` imports the
producer ordinarily and checks generic bases, `ℤ` at ranks zero/one/two, and
geometric integrality over the zero ring. In a checkout with the pinned Lean
toolchain and dependencies, first fetch the matching mathlib cache:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral
lake build AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral
```


The argument uses mathlib polynomial, localization, tensor and geometric-fiber
APIs and this library's previously defined finite coordinate rings and
normalization section. Its original project contributors are credited in the
[credits](../../../CREDITS.md). No source-coverage decision follows.
