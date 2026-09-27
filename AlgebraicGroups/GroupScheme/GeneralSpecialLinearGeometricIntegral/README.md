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
LEAN_NUM_THREADS=1 lake --wfail build AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral
LEAN_NUM_THREADS=1 lake --wfail build AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral
```

This original source-independent argument reuses mathlib's polynomial,
localization, tensor and geometric-fiber APIs. The finite coordinate rings,
true schemes and public normalization section are existing `AlgebraicGroups`
results (original module authors: Formal Frontier Agents;
the normalization-section contribution was by Worker A, Hive Task
`hive-request-a5e6c90d8ec39f1e9fa69dab1ca73e6f793e8dfd`, UID
`9d7acf51-7653-4b52-a05e-c0cd9d9599e0`).
The unimplemented planning investigation was by Worker B, Hive Task
`hive-request-4694e54904a86ba5cd23a09f174650df4ec77484`, UID
`62aa584a-e574-4ca7-bf87-d5548e0cd712`. This implementation is by Worker B,
Hive Task `hive-request-902e3e18b35d53eb4fd3b421954a339ef7741dd5`,
UID `8c21821f-f9ac-4e4b-80b6-b1452edb4276` (2026-09-27). A distinct Worker B
execution prepared the destination import and client-namespace transfer; it did
not author these mathematical proofs. The original project contributions and
this transfer are Apache-2.0 licensed. The incubator origin and original
source-only transfer were independently reviewed. The combined 130-module
destination graph is now accepted on main after fresh affected review and
successful native job 533 default build and complete private-inclusive
standard-axiom audit. The documentation-only release candidate retains those
checked inputs but is unaccepted and unpublished. No source-coverage decision
follows from the transfer.
