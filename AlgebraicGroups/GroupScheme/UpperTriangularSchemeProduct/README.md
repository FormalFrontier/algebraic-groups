# Represented U-first upper-triangular product

Import `AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`. For an
arbitrary commutative `K` and finite linearly ordered same-universe `n`, the
categorical product `U ⊗ D` over fixed `Spec K` is isomorphic as an underlying
scheme to the upper-triangular scheme `T`. The actual maps are inclusion
`i : U ⟶ T`, diagonal projection `q : T ⟶ D` and section `e : D ⟶ T`;
`upperTriangularUFirstIso` sends `(u,d)` to `i(u)e(d)`. Its inverse uses
`q(t)` and right-column normalization to extract the unitriangular factor.
The `U` here is the scheme-theoretic identity fiber, not merely a pointwise
kernel. `upperTriangularDiagonalConj` restricts represented diagonal
conjugation to `U`, and `upperTriangularUFirstTwistedMul_comp_hom` identifies
the arbitrary-test multiplication diagram. In U-first coordinates,
`(u,d)*(u',d') = (u*α(d,u'), d*d')`; this is **not** the canonical
direct-product group law, and no global transported `GrpObj` is asserted.

For every commutative `K`-algebra `R`, including zero and nonreduced rings,
the point readbacks recover the native action with entries
`α(d,u)ᵢⱼ = dᵢ*uᵢⱼ*dⱼ⁻¹`, the U-first forward map and its inverse. Empty
indices and noninjective coefficient maps remain in scope. The
[producer](../UpperTriangularSchemeProduct.lean),
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSchemeProduct.lean),
[split guide](../UpperTriangularSplitKernel/README.md),
[generic section-first product](../../GroupObject/SplitKernelProduct/README.md)
and [diagonal-product guide](../DiagonalProduct/README.md) give the declarations,
hypotheses and examples. No arbitrary-base-scheme change, `GL` normality,
smoothness/dimension result or source-coverage conclusion follows.

From this destination's root, reproduce both defaults with the pinned toolchain
and a successful matching mathlib-cache fetch **before** building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups AlgebraicGroupsTest
```

The [building guide](../../../docs/BUILDING.md) provides optional focused
commands and the fixed official dependency pins. Older `Incubator.*` imports,
the donor's 26-package graph and evidence collectors in the historical text
below are not part of ordinary destination use. This introduction is
documentary work by worker-a Hive Task
`hive-request-5b09e086919b2a86fb5230d5fd2ee02ac1f4e585` (UID
`e8705205-8984-46ec-9e40-00d34c8821b3`), not mathematical authorship.
Independent worker-b Task
`hive-request-5186ffa0cc57c5b0a78f71c7cf9553af92e82e06` (UID
`1eaec47f-e234-4d83-80b1-f8e82cbeb924`) gave a **static exact-P code**
approval (4979) on 2026-09-29, distinct from a computational result, human
review or release decision. Original contributor and reviewer histories follow.

## Historical preceding represented-product guide (complete P snapshot, 2026-09-29)

The full preceding guide follows byte-for-byte; its dated donor imports and
collector commands are historical, not shipping instructions.

# U-first coordinates and represented diagonal action for upper-triangular group schemes

Import `AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`. For a
commutative ring `K` and same-universe finite linearly ordered `n`, let `U`,
`D`, and `T` be the unitriangular, diagonal, and upper-triangular group
schemes **over the fixed base** `Spec K`. The categorical products below are
products of schemes over that base. Neither a field/domain nor a nonzero,
reduced, flat, or nonempty-index assumption is required. The actual closed
unitriangular subgroup `U` is the scheme-theoretic pullback kernel of
`T → D`, not just a pointwise kernel.

## Mathematical interface

The diagonal section `e : D ⟶ T` and inclusion `i : U ⟶ T` define represented
conjugation `α : D ⊗ U ⟶ U`. The readback
`upperTriangularDiagonalConj_lift_comp_inclusion` identifies its inclusion
with `e(d) * i(u) * e(d)⁻¹` for **every** test scheme over `Spec K`.
The published generic split-kernel action and section-first product already
supply the action laws and `F(v,d) = e(d)i(v)`; this module specializes that
product as `upperTriangularSectionFirstIso`. The distinct categorical
`upperTriangularCoordinateChange` is
`H(u,d) = (α(d⁻¹,u),d)`, with inverse `(v,d) ↦ (α(d,v),d)`.
Consequently `upperTriangularUFirstIso = H ≪≫ F : U ⊗ D ≅ T` has forward
arrow `K(u,d) = i(u)e(d)`. Both inverse triangles hold categorically, not
just on points. Its forward readbacks include `upperTriangularUFirstIso_hom`
and `upperTriangularUFirstIso_hom_comp_diagonal`; inverse readbacks include
`upperTriangularUFirstIso_inv_comp_snd` and
`upperTriangularUFirstIso_inv_fst_comp_inclusion`. The latter is right-column
normalization `i(v(t)) = (𝟙 T) * (q(t) ≫ e)⁻¹` as an arrow **out of `T`**:
`𝟙 T` here denotes the identity **arrow**, not the constant group identity.

For arbitrary arrows `u,d,u',d'` out of an arbitrary test object over `Spec K`,
`upperTriangularUFirstIso_mul_lift` proves
`K(u,d) * K(u',d') = K(u * α(d,u'), d*d')`.
`upperTriangularUFirstTwistedMul` realizes the right-hand coordinates as an
arrow `(U ⊗ D) ⊗ (U ⊗ D) ⟶ U ⊗ D`, and
`upperTriangularUFirstTwistedMul_comp_hom` gives the represented multiplication
diagram. This is **not** a direct-product group law or a global transported
group-object instance. For every commutative `K`-algebra `R`, the native
point-formula theorems give

```text
α_R(d,u)ᵢⱼ = (↑dᵢ : R) * uᵢⱼ * (↑(dⱼ⁻¹) : R)
v(t)ᵢⱼ   = tᵢⱼ * (↑(diagonal(t)ⱼ⁻¹) : R)
K_R(u,d)ᵢⱼ = uᵢⱼ * (↑dⱼ : R).
```

The diagonal entries are units; inversion precedes coercion to `R`. The
ordinary-import client exercises `Fin 0`, `Fin 1`, independent-unit/sign
shear over `Fin 2`, zero ring (`ZMod 1`), a nonzero square-zero dual-number
shear, and a noninjective coefficient reduction map. No arbitrary
**base-scheme** change, normality of `U` in `GL`, smoothness/dimension, or
source-specific mathematical correspondence is asserted.

## Imports, dependencies, and reproduction

The [producer](../UpperTriangularSchemeProduct.lean) imports the
[split-kernel producer](../UpperTriangularSplitKernel.lean) and published
`AlgebraicGroups.GroupObject.SplitKernelSemidirect`; the
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSchemeProduct.lean)
is explicitly rooted in `lakefile.toml`. See also the
[split guide](../UpperTriangularSplitKernel/README.md),
[published generic product](../../GroupObject/SplitKernelProduct/README.md),
[diagonal-product guide](../DiagonalProduct/README.md) and
[building instructions](../../../docs/BUILDING.md). This destination
has Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and official published
GitHub dependencies general-linear-groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`. The unchanged resolved
manifest has 13 packages and six total root fields. Reproduce from this
project's root only after installing its pinned toolchain and successfully
fetching the matching precompiled mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

Those are reproduction commands, not evidence that this transfer ran them.
The isolated donor's old 26-package graph, `Incubator.*` imports and collector
commands in the *complete historical guide below* do not describe this
shipping destination. Its evidence-only collector is not copied or imported.
A fresh separate evidence checkout, if used later, needs a successful matching
cache fetch **and both focused producer/client builds before** running that
collector; the historical commands alone do not establish such a check.

## Attribution and historical guide

The original represented-product Lean proofs and client were authored by
worker-b Task `hive-request-11a837cffae2a0d3e1de1e4e3f0444427ad7a828`
(UID `b67820b5-a408-4e53-bab5-e7af661d2353`), following the static plan
by worker-b Task `hive-request-5d589562fb7692f86ca72de5d84c264091553738`
(UID `bc5f6113-fa14-4f56-ba9c-ac7639e154ca`). Fresh isolated review was
by worker-a Task `hive-request-aa13d3eca9bdf0ad5f1f9c49d27e7ecd9e923da0`
(UID `a2611c06-0dd9-4a21-bb29-ae5bf1acdeb7`); accepted isolated C is
`67b652f5ef12456fd2ad849eed54717634c5d0e2`. Static promotion mapping
was by worker-b Task `hive-request-f56766f9697db772d9e397c3b7ae12298bb65652`
(UID `58fed302-a059-4c18-ba9b-dec2f890d65e`), report `9045aadf45708275519cb0ec1a59f05889074e23`.
This byte-preserving destination transfer is by worker-a Task
`hive-request-16662b4a0160f02f68b640e62104e2ff35408ba0`
(UID `e0fab456-6fa3-450a-9345-5229c475857d`), **not** a new mathematical
author or independent reviewer. The split prerequisite's original author
worker-b Task `hive-request-8a894f4ae8eb1e23cb2c2b0a446e015aaf0aa44f`
(UID `22e1595e-13f2-4d64-9e28-503288271bc8`) and independent worker-a
reviewer `hive-request-51ab92c80330e9f0a5fa961d6322cb184d1cd3c3`
(UID `dc3a8b31-7303-481f-bcbb-e24e63d73c85`) retain distinct credit.
The [existing split guide](../UpperTriangularSplitKernel/README.md) and
[repository README](../../../README.md) retain the subsequent destination
renewal, product contributors and independent mathematical provenance.
All such agent review is distinct from human mathematical review, source-author
endorsement, destination acceptance and publication. The repository license
and conventional header are Apache-2.0; dependencies retain their own notices.

### Complete isolated incubator C guide (historical snapshot, 2026-09-29)

The entire original donor guide follows byte-for-byte, including its old
incubator imports, graph, status and collector instructions. They refer to
the *isolated* C checkout, not this destination; consult the current sections
above for the shipping import and build route.

# Upper-triangular group scheme: U-first product and diagonal action

Import `Incubator.GroupScheme.UpperTriangularSchemeProduct`. For any commutative
ring `K` and finite linearly ordered type `n` in the same universe, write `U`,
`D` and `T` for the existing unitriangular, diagonal and upper-triangular group
schemes over `Spec K`. No field, domain, nonzero, reduced, flat or nonempty-index
assumption is required. The products below are categorical products **over the
fixed base** `Spec K`; `U ⊗ D` initially carries no transported group law.

## Reusable mathematical API

* `upperTriangularDiagonalConj K n : D ⊗ U ⟶ U` is the restriction of
  conjugation by the diagonal section to the *actual* pullback kernel. The
  `upperTriangularDiagonalConj_lift_comp_inclusion` readback says for any test
  scheme `X` over `Spec K`, `d : X ⟶ D`, `u : X ⟶ U` and inclusion `i : U ⟶ T`:
  `i(α(d,u)) = e(d) * i(u) * e(d)⁻¹`. The defining pullback, section and three
  group-scheme maps come from `Incubator.GroupScheme.UpperTriangularSplitKernel`.
  The published generic `splitKernelConj_one/mul/map_mul/map_inv` describe the
  action; this module adds no competing generic action theory.
* `upperTriangularUFirstIso K n : U ⊗ D ≅ T` is an iso of **underlying schemes**.
  Its forward map is `K(u,d) = i(u) * e(d)`, established as an actual arrow by
  `upperTriangularUFirstIso_hom`. Its diagonal readbacks are
  `upperTriangularUFirstIso_hom_comp_diagonal` and
  `upperTriangularUFirstIso_inv_comp_snd`. The first inverse component `v(t)`
  satisfies `i(v(t)) = 𝟙 T * (q ≫ e)⁻¹` as an arrow out of `T`, by
  `upperTriangularUFirstIso_inv_fst_comp_inclusion`. Here `𝟙 T` is the
  **identity arrow**, not the constant identity of the group object; this is
  right (column) normalization.
* `upperTriangularUFirstIso_mul_lift` proves for **arbitrary** arrows out of any
  test scheme `X` over `Spec K`:

  ```text
  K(u,d) * K(u',d') = K(u * α(d,u'), d*d').
  ```

  `upperTriangularUFirstTwistedMul` realizes the right-hand coordinates as a
  morphism `(U ⊗ D) ⊗ (U ⊗ D) ⟶ U ⊗ D`;
  `upperTriangularUFirstTwistedMul_comp_hom` proves the product-projection
  diagram into `T` commutes with `μ[T]`. This is *not* a direct-product group
  isomorphism and introduces no global transported `GrpObj` instance.

The published `AlgebraicGroups.GroupObject.SplitKernelProduct` is already an
underlying **section-first** iso `F(v,d) = e(d) * i(v)`; it is exposed here by
`upperTriangularSectionFirstIso` only as a specialization of the published
construction. Published `SplitKernelSemidirect` provides the actual conjugation
action. `upperTriangularCoordinateChange` is the categorical iso
`H(u,d) = (α(d⁻¹,u), d)` with inverse `(v,d) ↦ (α(d,v),d)`. The U-first iso is
`H ≪≫ F`, not a renaming of `F`. Its inverse equations follow from the generic
action laws and cartesian-product hom-ext; the twisted law uses genuine arrow
multiplication. No equality of morphisms is inferred from points alone.

For **every** commutative `K`-algebra `R`, the point theorems
`upperTriangularDiagonalConj_point`, `upperTriangularUFirstIso_point`,
`upperTriangularUFirstIso_inv_point` and its two `inv_fst_point`/
`inv_snd_point` projections identify these arrows respectively with the native
`Matrix.UpperTriangularGroup.diagonalAction`, U-first `semidirEquiv`,
`unipotentPart`, and `diagonal`. The native formulas (already proved in
`Incubator.GroupTheory.UpperTriangular`) give

```text
α_R(d,u)ᵢⱼ = (↑dᵢ : R) * uᵢⱼ * (↑(dⱼ⁻¹) : R)
v(t)ᵢⱼ   = tᵢⱼ * (↑(diagonal(t)ⱼ⁻¹) : R)
K_R(u,d)ᵢⱼ = uᵢⱼ * (↑dⱼ : R).
```

The `dᵢ` are *units* in `Rˣ`: inversion precedes coercion to `R`. This is why
the statements remain valid for zero and nonreduced rings. Native fixed-base
coefficient maps commute with these operations even when noninjective; the
ordinary-import client checks this on reduction `ℤ → ZMod 2`. Its `Fin 2`
independent-unit shear gives `(-1,1)` acting on the upper entry `1` by `-1`,
proving that the twisted law differs from direct-product multiplication. It
also checks `Fin 0`, `Fin 1`, `ZMod 1`, and a nonzero square-zero shear over
`DualNumber ℤ`.

## Reproduction and status

This isolated additive module retains **all 196 inherited leaves** and the
26-package manifest with six top-level fields (`version`, `packagesDir`,
`name`, `lakeDir`, `fixedToolchain`, `packages`). Pins: Lean
`leanprover/lean4:v4.34.0-rc2`; mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; official published
algebraic-groups `f49141f0cd92a101d587a344eb3e2bd5bf4331d8`,
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`,
scheme-properties `193d4fe284cf1de71b168c198ad7b24a6eb71d39`.
From the isolated code revision:

```sh
lake exe cache get
LAKE_JOBS=2 lake build Incubator.GroupScheme.UpperTriangularSchemeProduct IncubatorTest.GroupScheme.UpperTriangularSchemeProduct
```

The transitive origin audit collector is **only on the separate evidence
checkout**, not an import of this code branch or the ordinary client. From
`worker-b/upper-triangular-scheme-product-evidence-20260929`:

```sh
lake exe cache get
lake env lean research/UpperTriangularSchemeProductImplementation/Collector.lean
```

The evidence branch's `REPORT.md` binds successful cache-first focused builds,
the complete producer/client private-and-generated declaration inventories and
their actual transitive axioms to the exact code revision and dependency graph.
The earlier accepted T/D/S producer and client evidence is reused without
replaying its full donor audits. Development checks are not fresh independent
review, owner acceptance, protected-main integration, promotion or publication.

## Provenance and limitations

Author: worker-b Hive Task
`hive-request-11a837cffae2a0d3e1de1e4e3f0444427ad7a828`, UID
`b67820b5-a408-4e53-bab5-e7af661d2353`, on sole accepted isolated parent
`3a98326860b04ee59e5af8a1839aa2dbd8135920`. The static, previously
uncompiled mathematical plan was authored by worker-b Task
`hive-request-5d589562fb7692f86ca72de5d84c264091553738`, UID
`bc5f6113-fa14-4f56-ba9c-ac7639e154ca`; the present proofs are separately
Lean-checked. The published generic split-kernel product/conjugation, U/GL
representations and mathlib retain their original authors and independent
release reviewers. Local D was developed by worker-a Task
`hive-request-25386fd8e578f7a1fd1a391d0547e995d3944f25` (UID
`eb3f1966-948e-4116-9fc4-f40697463287`); represented T by worker-b Task
`hive-request-85aefe5c15f83c43ba1ac6693f00c894245c5e44` (UID
`94c69b0a-c947-46f2-89ac-267ece213dcd`); accepted split kernel S by
worker-b Task `hive-request-8a894f4ae8eb1e23cb2c2b0a446e015aaf0aa44f`
(UID `22e1595e-13f2-4d64-9e28-503288271bc8`) with independent worker-a
reviewer `hive-request-51ab92c80330e9f0a5fa961d6322cb184d1cd3c3`
(UID `dc3a8b31-7303-481f-bcbb-e24e63d73c85`). Preexisting native T and
the published dependency authors/reviewers retain their separate credit.

The tracked repository license is Apache-2.0. This original additive
contribution copies no unpublished source asset or mathematical proof text.
Its fixed-base morphism laws are not a theorem of arbitrary **base-scheme**
change, a claim that U is normal in GL, smoothness/dimension, or any
source-specific correspondence/coverage decision. Users need no source
research record to import or interpret these independently reusable APIs.
