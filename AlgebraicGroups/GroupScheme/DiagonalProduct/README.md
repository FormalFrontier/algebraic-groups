# Finite products of diagonal group schemes

Import `AlgebraicGroups.GroupScheme.DiagonalProduct`. For every commutative
ring `K` and same-universe finite decidable index `n`, the API identifies
`diagonalGroupScheme K n` with the **literal finite categorical product**
of copies of `Gₘ` in `Grp (Over (Spec (.of K)))`. Actual Hopf projections
and global-sections universality for arbitrary test schemes, not merely
affine or point-valued tests, give both product-iso triangles. The empty
index is terminal; zero rings and nonreduced rings are covered by the
ordinary-import client. See the detailed definitions and examples in the
complete guide preserved below and the [producer](../DiagonalProduct.lean).

The integrated code at `ad5bff948f563bb9df49825f55dfcc8fcace8130`
has original native run 1058 and fresh independent worker-b code review
4912, followed by separate maintainer code acceptance and integration.
This documentation repair does not assert its own final review, native
success or publication. The complete historical guide below retains the
donor, mapper, transfer and reviewer identities; its AI-assisted agent
credits do not assert human mathematical review or source-author
endorsement. The product result does not establish a represented split or
semidirect product, smoothness/dimension, arbitrary-base scheme change, or
source-specific correspondence/coverage.

## Dated preparation snapshot — 2026-09-29, before publication-status repair; all lifecycle statements below are historical

The complete preceding product guide follows unchanged. Every nested
“current” status and release-pending assertion below belongs to the dated
pre-repair stage rather than to the present publication status.

---

# Finite diagonal-group-scheme product: accepted code, release pending

**Current status (2026-09-29).** For every commutative ring `K` and
same-universe finite decidable index `n`, the API below gives the literal
categorical product of copies of `Gₘ` in `Grp (Over (Spec (.of K)))`.
Genuine Hopf projections and arbitrary-test-scheme global-sections
universality establish both projection triangles and empty-index terminality,
including zero and nonreduced base rings. The exact destination code at
protected main `ad5bff948f563bb9df49825f55dfcc8fcace8130` passed original
native run 1058 (matching-cache both-target build and complete transitive
private/generated-inclusive standard-three audit), fresh independent
worker-b review 4912, separate maintainer acceptance and protected
integration. This four-document readiness update does not rerun those checks
and does not preserve their whole-shipping-file fingerprint. Consolidated
final release review, required native context, owner release acceptance,
protected release stages and verified private GitHub publication remain
pending. The previously published upper-triangular predecessor is not a
diagonal-product release. No represented split-kernel/semidirect,
dimension/smoothness, arbitrary-base scheme-change or source-specific
correspondence/coverage claim follows.

The product proofs and ordinary-import client were authored by worker-a Task
`hive-request-1eaf7759cab2877f525c118df8dfcc2cf02c5ecf` (UID
`24f5b359-e14d-4180-86e0-da0f1ae1315b`), with the source-independent
selection and first-transfer contributors credited in the complete history
below. The released-parent destination assembly was by worker-a Task
`hive-request-1ee0fb205d496a73f85e290bff57073a6b93f242` (UID
`f8cc5208-58cf-4d04-aecc-e9a541fddee1`). Fresh destination reviewer was
worker-b Task `hive-request-f3ed2d56e64cee367473bd214ef56cc2b7309857`
(UID `6ec4256e-2cda-4d7f-80e3-95ab945e1340`); Lattice made the separate
code-acceptance/integration decision. This is agent credit, not a claim of
human review or source-author endorsement.

## Dated predecessor guide (complete pre-1058/pre-integration C history, 2026-09-29)

The complete earlier guide follows unchanged. Its then-current unchecked
product labels and pending predecessor release statements are historical;
use the current status above for this accepted, unreleased product.

---

# Finite diagonal-group-scheme product: released-parent candidate

**Current status (2026-09-29):** This source-independent API and ordinary-import
client are a **static, unchecked** transfer from the accepted isolated donor
onto released algebraic-groups R `14cd731a7a934709e28945ba1f22cedac59c3438`
(tree `86d5e92730279411b7dd3d7b60f3f49c4c5320fe`), matching verified
official Q `7ea3256fedfc2baeb1e36590c1293aafbaede682` in shipping tree.
R's native and represented upper-triangular contribution is now published;
old PR235/pending-publication language below is dated history. This transfer
has no destination build, axiom audit, independent exact-parent review,
acceptance, integration or product release. Original donor evidence does not
verify this changed destination graph. The 14 declaration/file selections and
literal finite product with all-test-scheme universality are documented below;
no source-specific Milne correspondence or coverage is asserted.

The accepted isolated donor was authored by worker-a Task
`hive-request-1eaf7759cab2877f525c118df8dfcc2cf02c5ecf` (UID
`24f5b359-e14d-4180-86e0-da0f1ae1315b`), reviewed by worker-b Task
`hive-request-898d867f547ca4b701b12773b4c51c94231975cb` (UID
`5be2102f-b518-49ad-93e8-95474aa48bb6`), and mapped by worker-a Task
`hive-request-51140fa5920c4d93115eb0da62f20bd36c2266bc` (UID
`5d1ab42e-5c0a-4618-b3b9-a6ae72cf5ce4`). The prior sole-I transfer by
worker-a Task `hive-request-77855aa4697d890d8d4aaed8292f047886da599b`
(UID `9f032fe9-7431-43bc-b798-a6f1f5668416`) is fully retained on its
own branch; this released-parent assembly is by worker-a Task
`hive-request-1ee0fb205d496a73f85e290bff57073a6b93f242` (UID
`f8cc5208-58cf-4d04-aecc-e9a541fddee1`). Lattice owns later checks,
fresh review, acceptance, integration and publication. This is agent credit,
not human mathematical review or source-author endorsement.

## Dated original C guide (complete historical text, 2026-09-29)

The complete earlier guide follows unchanged, including its then-correct
sole-I product-transfer and pending upper-triangular publication statements.
Historical collectors remain in their separate evidence checkouts; no local
collector command is proposed here.

---

# Finite products of diagonal group schemes

Import `AlgebraicGroups.GroupScheme.DiagonalProduct` to identify the group scheme of
invertible diagonal matrices with the **literal categorical product** of copies
of `Gₘ`. For `K : Type u` with `[CommRing K]` and `n : Type u` with `[Fintype n]`
and `[DecidableEq n]`, use
`AlgebraicGeometry.diagonalGroupSchemeProductIso K n :
  diagonalGroupScheme K n ≅ (∏ᶜ fun _ : n => multiplicativeGroupScheme K)`
in `Grp (Over (Spec (.of K)))`. No field, domain, nonzero, reducedness,
inhabited-index, flatness, or ordering assumption is needed. In particular,
the empty index is genuinely terminal (`diagonalGroupSchemeEmptyIsTerminal`
for `PEmpty.{u+1}` with `K : Type u`, and
`diagonalGroupSchemeFin0IsTerminal` for `K : Type`), including over the zero ring.

The Hopf algebra is the accepted diagonal quotient
`DiagonalCoordinateRing.CoordinateRing K n` of the native GL coordinate ring.
For `j : n`, `diagonalGroupProjectionCoordinateMap K n j` maps the Laurent
coordinate of `multiplicativeGroupCoordinateRing K` to the quotient's `(j,j)`
matrix entry (`diagonalGroupProjection_coordinate`). Its counit is `1` and its
comultiplication is the tensor square: after mapping the GL matrix coproduct
through the quotient, every other summand vanishes because one factor is
off-diagonal. `diagonalGroupProjectionBialgHom` packages the actual Hopf map,
and `diagonalGroupProjection K n j` is the induced group-object morphism,
not merely a pointwise group homomorphism. Its underlying left scheme map is
the `Spec.map` of the coordinate ring hom (`diagonalGroupProjection_left`).
For an affine test algebra `R`, `diagonalGroupProjection_point` reads off the
native unit at `j`, including for nonreduced and zero rings.

For an **arbitrary** test scheme `X : Over (Spec (.of K))`, not necessarily
affine, `diagonalGroupHomUnits K n X` identifies morphisms to the diagonal
scheme with tuples of units in the global sections
`((algΓ (.of K)).obj X).unop`; `multiplicativeGroupHomUnits K X` does the
same for `Gₘ` with a single unit. A local CommRing adjunction helper translates
morphisms to affine targets into algebra maps on global sections without a
field assumption. `diagonalGroupProjection_globalUnit K n j X hom` proves
composition with the genuine projection reads exactly the `j`-th unit.
`diagonalGroupProductFan K n` and
`diagonalGroupProductFan_forget_isLimit K n` use this classification to
construct the universal lift and prove its uniqueness for **every** `X`.
`diagonalGroupProductFan_isLimit K n` reflects the limit from underlying
schemes through `Grp.forget`, producing the product iso. Both projection
triangles are available as simp lemmas
`diagonalGroupSchemeProductIso_hom_π` and
`diagonalGroupSchemeProductIso_inv_projection`. Affine point equivalence alone
would not establish this nonaffine universal property.

The ordinary-import client `AlgebraicGroupsTest.DiagonalProduct` checks
the polymorphic global-sections law and product triangles, `Fin 0/1/2`, the
zero ring `ZMod 1`, and both independent projections for the nonreduced
dual-number algebra `DualNumber ℤ` with unit `1 + ε` (inverse `1 - ε`).
The construction does not assert an explicit multi-Laurent algebra
presentation, dimension/smoothness, base change, a semidirect decomposition,
or source coverage.

Destination pinned inputs: Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official
`general-linear-groups` `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and `scheme-properties` `6b204a3e49f022e51d78a9f93e77513b99a87e00`.
The destination's 13 complete resolved packages differ from the original
isolated donor's 26; neither incubator nor an unpublished dependency is
imported. Both new modules are registered in the production aggregate and
explicit ordinary-import test roots respectively. For a later authorized
destination check from this project root, install the pinned toolchain, fetch
and verify the matching precompiled mathlib cache, then build **both** defaults:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The focused targets, if useful after that cache fetch, are
`AlgebraicGroups.GroupScheme.DiagonalProduct` and
`AlgebraicGroupsTest.DiagonalProduct`. These are instructions, not a report
that destination elaboration, build, axiom audit or client execution succeeded.

The accepted *isolated* product was authored by Forgejo
`formalization-worker-a`, Hive Task
`hive-request-1eaf7759cab2877f525c118df8dfcc2cf02c5ecf`, UID
`24f5b359-e14d-4180-86e0-da0f1ae1315b`, for responsible maintainer
Lattice and FormalFrontier/incubator issue #182. Its sole accepted-in-isolation
parent is `d9d7b61aa08b4ee7130f00da7f557baecac71a64`, originally authored
by worker-a Task `hive-request-25386fd8e578f7a1fd1a391d0547e995d3944f25`
and independently reviewed in commit `617d1b523d141b89e345545bf68284c59397d5be`
by worker-b Task `hive-request-f4f1a4daca8dc87de87ce04b24ea6217f64c8fb3`.
The original route followed the **uncompiled** planning report
`1f8fe9a4b2ac23e8a62b9c9bfcacf1b54e2e33dc` by worker-a Task
`hive-request-f042ef433de4358c121e9732cf70474ca451415e`. Product donor
`1172eddaa0f416c11b7f118d68a1ab74af6cd6d9` was independently reviewed
by worker-b Task `hive-request-898d867f547ca4b701b12773b4c51c94231975cb`
(UID `5be2102f-b518-49ad-93e8-95474aa48bb6`), review
`91d600d99ea9d70195b32697a0518ccbc03a8e0e`, and accepted in isolation
by Lattice at issue #182/comment 61645. The original evidence checkout
`1174100793ec42be33a3e9c00445918ba1857506` contains its collector,
matching-cache focused build logs and private/generated-inclusive 42-origin
standard-three axiom audit; six IR-only extras are inventoried separately.
The later selected destination map is
`24ecc28b8e106df8237532c996c0ba4363c0a76e` by worker-a Task
`hive-request-51140fa5920c4d93115eb0da62f20bd36c2266bc`
(UID `5d1ab42e-5c0a-4618-b3b9-a6ae72cf5ce4`).

This **static unchecked, unreviewed** native transfer from published AG
`cb9fec27155722c2749aa03471ed40c73d3e1276` (matching official release
`6c7f4a5a38881573fd2bb735fc3dab1de53b83bf`) is by worker-a Task
`hive-request-77855aa4697d890d8d4aaed8292f047886da599b`, UID
`9f032fe9-7431-43bc-b798-a6f1f5668416`. Earlier donor evidence and review
do **not** check this changed 13-package destination graph. PR #235 has its
separate checks and review; after its own accepted reviewed release, Lattice
must renew this product on the then-accepted parent, arrange destination
both-target build and complete standard-three transitive axiom audit including
private/generated declarations, fresh author-distinct review, separate code
acceptance/integration and reviewed official release/GitHub verification.
No source-specific Milne correspondence or coverage is asserted here.
