# Building algebraic-groups

The default Lake targets are `AlgebraicGroups` and `AlgebraicGroupsTest`; the
second includes the explicitly rooted represented-product ordinary-import
client. The pinned toolchain is Lean `leanprover/lean4:v4.34.0-rc2`. The
resolved manifest has 13 packages and six total root fields; direct GitHub
requirements are mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and scheme-properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`.
From this project root, install the pinned toolchain and **successfully fetch
the matching precompiled mathlib cache before building both default targets**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups AlgebraicGroupsTest
```

For optional focused producer/client builds in the same checkout, first
successfully fetch the matching cache as well:

```sh
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSchemeProduct
```

See the [represented-product guide](../AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md),
[split guide](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md)
and [diagonal-product guide](../AlgebraicGroups/GroupScheme/DiagonalProduct/README.md).
Private research, evidence collectors and dated isolated-donor imports are
not needed for ordinary use or either default build. These are reproduction
instructions, not a claim about a particular check run.

## Historical preceding BUILDING.md (complete P snapshot, 2026-09-29)

The entire preceding document follows byte-for-byte. Its older status and
donor commands belong to their dated checkouts; the shipping commands are above.

# Building the represented U-first product and its prerequisites

Install the repository-pinned toolchain and, from this project's root, fetch
the matching precompiled mathlib cache **successfully before** either build.
Build both default targets, which include the represented-product producer and
its explicitly rooted ordinary-import client:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

After a successful matching cache fetch, optional focused targets are:

```sh
LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSchemeProduct
```

These are reproduction instructions, **not executed for this static transfer**.
The isolated donor's earlier focused build/private-inclusive standard-three
audit and the earlier split/product results apply only to their original inputs;
none establishes a destination check or review of this transferred union.
The pinned 13-package graph and three official direct dependencies remain fixed.

## Historical preceding build guide (complete W snapshot, 2026-09-29)

The entire preceding guide follows unchanged; historical commands and status
descriptions refer to their dated predecessors, not to a new union pass.

# Building algebraic-groups

The two Lake default targets are `AlgebraicGroups` and `AlgebraicGroupsTest`.
Use the repository-pinned Lean toolchain and resolved 13-package manifest.
The direct dependencies are mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, general-linear-groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`, at their declared GitHub
URLs. The manifest has six total root fields, including `packages`.

From the project root, successfully fetch the **matching precompiled mathlib
cache before building** both default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

After that successful matching-cache fetch, optional focused builds for the
[split-kernel producer](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean)
and [ordinary-import client](../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean)
are:

```sh
LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel
```

The [split-kernel guide](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md)
and [diagonal-product guide](../AlgebraicGroups/GroupScheme/DiagonalProduct/README.md)
describe their hypotheses and public APIs. The isolated donor's old
evidence collector is neither a shipping dependency nor a build step.

## Dated frozen-W BUILDING.md (complete 2026-09-29 historical snapshot)

The complete preceding build guide follows unchanged. Its nested “current”
and lifecycle wording describes dated earlier candidate stages; old C1063
and donor103-origin commands do not establish checks of this shipping tree.

---

# Building the diagonal product and upper-triangular split kernel

The diagonal-product producer/client and upper-triangular split-kernel
producer/client are in this pinned Lake project. Install its Lean toolchain,
successfully fetch the matching precompiled mathlib cache from the project
root **before** building both default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The direct GitHub dependencies remain mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, general-linear-groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc`, and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`, with the resolved
13-package manifest. Only after a successful matching cache fetch, optional
focused builds may target the two split-kernel modules:

```sh
LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel
```

These are reproduction instructions, not commands this 2026-09-29 static
renewal executed. Original split native run 1063 and independent review 4917
apply to original C; original product native 1058 and review 4912 apply to
integrated product code. Neither prior result verifies this combined shipping
tree or settles its later owner decisions. The isolated donor's 103-origin
collector is evidence-only and is not a shipping module or build step. The
13-package manifest has **six total** root fields, including `packages`.
Static renewer: worker-a Hive Task
`hive-request-4858ca079644447900997ac218698753e3e37f5b` (UID
`9dafa64c-e479-4135-a48e-c670d90d0eaa`).

## Dated frozen-B build preparation (N's complete unique introduction, 2026-09-29)

The following entire N preparation introduction is historical. Its “current”
and pending-status language refers to frozen B and N at that date, not the
later state of this combined tree. Its promise of B as the next whole guide
reflects N's old layout: the sole complete B body is nested inside D below.

---

# Building the prospective triangular split kernel and diagonal product

## Current prospective-union reproduction (2026-09-29; no new checks run)

This static candidate adds the original, byte-identical
`AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` producer and
`AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel` ordinary-import
client to the frozen product-release-readiness snapshot
`9b2a5db2a4bceb6c7146d9cb2ba8e0eb36ed1411`. The product *code* at
protected main `ad5bff948f563bb9df49825f55dfcc8fcace8130` is accepted,
but the frozen documentary parent remains **unaccepted and unreleased**.
The new union is **static, unchecked, unreviewed and unaccepted**. The
original split candidate's native run 1063, complete private/generated-inclusive
standard-three axiom audit and independent review 4917 verify its **different
tree**, not this union; product native 1058 verifies its own exact inputs.
Neither donor evidence nor historical product-readiness language is a union
check. Future changes to B can require reassembly.

For a later **authorized** check using the pinned Lean toolchain and unchanged
13-package/six-total-root-field manifest, first successfully fetch the matching
precompiled mathlib cache, then build **both default targets** from the project
root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

Only after the matching cache fetch, optionally reproduce the new focused
producer and client:

```sh
LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel
```

These are instructions, **not** commands executed on this combination.
The original isolated donor's focused 103-origin collector lives only in its
separate evidence, not in this shipping tree or the donor's shipping code.
A complete private/generated-inclusive transitive standard-three audit and
fresh independent review of the **final union** remain distinct required
steps before any maintainer acceptance, integration and own reviewed release;
the pending product release has its own independent chain. No source coverage
or represented semidirect conclusion follows.

## Dated frozen-B BUILDING.md (complete release-readiness history, 2026-09-29)

The entire previous guide follows unchanged. Its leading reproduction and
pending-product statements describe B's original preparation, not a new
union computation, union acceptance or product publication.

---

## Dated repaired-product build guide (complete D body, 2026-09-29)

The entire repaired-product build guide follows unchanged. Its snapshot and
nested “current” lifecycle statements are historical; its full B suffix
appears exactly once after D's original added introduction.

---

# Building the finite diagonal-group-scheme product

This project includes the literal finite categorical product of `Gₘ` for
every commutative ring and same-universe finite decidable index, with genuine
Hopf projections and an arbitrary-test-scheme universal property. The
producer is `AlgebraicGroups.GroupScheme.DiagonalProduct`; the ordinary-import
client is `AlgebraicGroupsTest.DiagonalProduct`. These instructions apply to
the pinned project checkout, regardless of its publication stage.

Install the pinned Lean toolchain, then successfully fetch the matching
precompiled mathlib cache from the project root **before** building both
default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The unchanged official GitHub dependency pins are mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, general-linear-groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc`, and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`. After the cache fetch,
the producer and ordinary-import client may also be built as focused targets.
These commands are reproduction instructions, **not** execution performed
for this documentary repair. Original native run 1058 successfully built
both default targets and audited the integrated code at
`ad5bff948f563bb9df49825f55dfcc8fcace8130`, with independent code
review 4912; its original whole-file input fingerprint does not identify
this four-document snapshot. No new required native result, whole-snapshot
review or publication outcome is asserted here.

## Dated preparation snapshot — 2026-09-29, before publication-status repair; all lifecycle statements below are historical

The complete preceding build guide follows unchanged. Its nested “current”
instructions and release/check-status assertions record earlier preparation
stages, not the present publication status.

---

# Building the accepted diagonal product (2026-09-29; own release pending)

The literal finite diagonal-group-scheme product at protected main
`ad5bff948f563bb9df49825f55dfcc8fcace8130` is accepted and integrated,
not yet released. Original native run 1058 on that exact code and pinned
13-package graph fetched the matching mathlib cache, built both default
targets (3,890 jobs; 160 Lean modules) and completed a transitive
private/generated-inclusive standard-three axiom audit (4,079 origin pairs,
including 1,297 private origins). Fresh independent exact-code review 4912
approved it; the maintainer separately accepted and integrated it. The
original whole-file input fingerprint does **not** identify this four-document
preparation. All 185 non-documentary blobs, all 141 ordered metadata result
objects, 101 production aggregate imports, 44 explicit test roots, both
default targets, all 13 resolved packages and six manifest root fields,
toolchain and checker inputs remain unchanged. The original isolated donor's
different graph and the published upper-triangular run 1031 are not product
destination checks.

For reproduction on an authorized matching checkout, install the pinned Lean
toolchain and successfully fetch the matching precompiled mathlib cache from
the project root **before** building both default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The optional focused targets, after that cache fetch, are
`AlgebraicGroups.GroupScheme.DiagonalProduct` and
`AlgebraicGroupsTest.DiagonalProduct`. These are reproduction instructions,
not a new build, axiom audit or test run on the documentary candidate. Its
required native context, consolidated independent final release review,
owner release acceptance, protected release stages and verified private
GitHub publication remain pending. The prior native/represented
upper-triangular release is complete; no source-coverage decision follows.

## Dated predecessor BUILDING.md (complete pre-1058/pre-integration C history, 2026-09-29)

The complete earlier guide follows unchanged. Its static unchecked product
labels and pending destination checks describe the earlier C snapshot,
not the accepted code or this unreleased documentary preparation.

---

# Diagonal-product destination guidance (2026-09-29; static unchecked candidate)

Released AG R `14cd731a7a934709e28945ba1f22cedac59c3438`, tree
`86d5e92730279411b7dd3d7b60f3f49c4c5320fe`, matches verified official
Q `7ea3256fedfc2baeb1e36590c1293aafbaede682` in shipping tree. Its
native and represented upper-triangular contribution completed its own
reviewed publication. This **new product transfer** only adds the
`AlgebraicGroups.GroupScheme.DiagonalProduct` aggregate import and explicit
`AlgebraicGroupsTest.DiagonalProduct` ordinary-import root alongside Diagonal.
It adds three leaves (189 total), two Lean files (160 total), one aggregate
import (101 total), one test root (44 total) and 14 selected result pairs
(141 total). All 181 outside-scope R blobs, both default targets, the entire
13-package/six-root-field manifest, pinned Lean 4.34.0-rc2, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official general-linear-groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` stay unchanged.

For a **later authorized destination check**, install the pinned toolchain and
successfully fetch the matching precompiled mathlib cache from this project
root **before** building both default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

Optional focused targets *after* that cache fetch are
`AlgebraicGroups.GroupScheme.DiagonalProduct` and
`AlgebraicGroupsTest.DiagonalProduct`. This is not a report of a product
destination elaboration/build, private/generated-inclusive transitive
standard-three axiom audit, independent exact-candidate mathematical/API/
provenance review, Lattice's acceptance/integration, or reviewed official
product publication. The original isolated donor's 26-package evidence is
scoped to its original inputs; R's native run 1031 checks R's unchanged
upper-triangular code, not the added product. No source correspondence or
coverage is claimed.

## Dated predecessor BUILDING.md (complete released-R history, 2026-09-29)

The entire R building guide follows without alteration. Its pending
upper-triangular publication and absence of product targets are historical;
the current scope and lifecycle are stated above.

---

# Building the accepted upper-triangular code and preceding results

## Current destination instructions and evidence (2026-09-29; accepted code)

The aggregate `AlgebraicGroups` imports both the native upper-triangular
producer and the represented upper-triangular closed-group-scheme producer.
The `AlgebraicGroupsTest` default target includes their separate
ordinary-import clients. With the repository-pinned Lean toolchain, first
fetch the matching precompiled mathlib cache; only **after it succeeds** build
both default targets from the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

Optional focused targets, after the same cache fetch, are
`AlgebraicGroups.GroupTheory.UpperTriangular`,
`AlgebraicGroupsTest.UpperTriangular`,
`AlgebraicGroups.Algebra.UpperTriangularCoordinateRing`,
`AlgebraicGroups.GroupScheme.UpperTriangular` and
`AlgebraicGroupsTest.UpperTriangularScheme`. The resolved 13-package graph
retains mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`, official
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and scheme-properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`.

These commands are reproduction instructions, **not a new check on this
documentation-only release candidate**. Original native run 1031 on exact
protected main `8640f487fa1296f0ce34fb29fdf86f146fe6f1ba` fetched the
matching mathlib cache and successfully built both default targets (3,888
jobs). Its complete transitive private/generated-inclusive standard-three
audit covered all 158 Lean modules (115 production and 43 tests), 4,037 actual
origin pairs (4,018 distinct names, including 1,288 private-named origins),
and admitted only `propext`, `Classical.choice` and `Quot.sound`. Fresh
author-distinct destination code review 4881 approved exact H; Lattice
separately accepted it and integrated it into protected main. The five
documentary changes here preserve every Lean, build, toolchain, dependency,
default target and checker input, so that original computation remains
applicable; its **whole-file input digest does not** describe these new docs.
The isolated native and represented donors had separate focused builds and
private/generated-inclusive standard-three audits on a different 26-package
graph (137 and 97 origins); those are historical and not destination checks.
The represented collector remains with its separate evidence child. Common-zero
publication has its own applicable checks, not substitutes for run 1031. Final
consolidated release review, applicable required native context, owner release
acceptance, protected stages and verified private GitHub publication remain
separate and pending. No new build or audit is asserted for this preparation.

## Dated predecessor building guide (complete historical text)

The complete pre-assembly guide follows unchanged. Its older common-zero
release-pending statements describe earlier checkpoints rather than the
separately completed official publication; no older run checks these additions.

---

# Common-zero build guidance

## Accepted-code readiness (2026-09-29; own release pending)

Protected-integrated main V `021cbd4ed92bc55704f401533846731a73079a8f`
(tree `0e9dcaf625161287c6423a76808a2ee741da195c`) contains the common-zero
producer and ordinary-import client. Original H native run 993 fetched and
verified the matching mathlib cache before both default targets (3,881 jobs),
then audited all 3,803 declaration origins across 153 Lean modules, including
1,197 private origins and generated declarations, with only `propext`,
`Classical.choice` and `Quot.sound`. The H-to-V differences are the root README,
common-zero guide, this build guide and metadata prose. The 153 Lean files, both
default roots, 98 aggregate imports, 41 test roots, 13 whole resolved package
objects, pins and checker inputs remain fixed. This is reuse of applicable
computational evidence, **not** equality of documentary whole-file digests.
Exact-V native run 1004 (job 1005) and its required Lean CI context also
succeeded. Fresh exact-V independent review 4851 and separate maintainer code
acceptance preceded protected main integration; this dated readiness snapshot
does not assert separate release acceptance, publication or source coverage.
The commands and all earlier stage-specific guidance below remain historical
or reproducibility guidance, not observations of a new build here.

## Post-review correction snapshot (2026-09-29, before final-V approval)

At the 2026-09-29 post-review correction, original common-zero destination H
`94172e62b759894bd8d821a253aa3f08f68f58c2` had passed native run 993:
matching cache fetched and verified before both-default-target build (3,881 jobs),
153 modules and 3,803 actual declaration origins including 1,197 private origins
audited transitively with only `propext`, `Classical.choice` and `Quot.sound`.
That evidence applies to unchanged computational inputs, not the changed
documentary whole-file digest. Reviews 4837 (H) and 4843 (README-corrected U)
requested documentary corrections; final-revision approval, native required
checks, maintainer acceptance/integration and separate verified release are not
inferred here. The commands below remain reproduction instructions.

## Original preparation snapshot (2026-09-29, before run 993 and review 4837)

The initial preparation and pending-check wording below is historical. Later
build/review evidence is described above; no original check or finding is erased.

### Common-zero candidate on published diagonal: build guidance (2026-09-29)

Accepted main I11 `e794bded47a4e36f830edc163f7b62892314f4cf`
(tree `5cd4fbd40aea2297eaef40c75354896d107686d1`) matches the verified
official diagonal P11 `56c759fc12152a447e36249ee50218ce473d93ca` by
tree; the separately published exponent P10 remains its predecessor. I11 has
176 shipping leaves, 151 Lean files, 97 aggregate imports, 40 explicit test
roots, 87 selected metadata results and 13 resolved packages. This proposed
common-zero contribution adds one producer, one ordinary-import client and
one guide: 179 leaves, 153 Lean files, 98 imports, 41 test roots and 90
selected results, retaining all 13 whole package objects and all pins.

The isolated common-zero producer and nine-check client had a cache-first
scoped build and a transitive standard-three axiom audit covering all three
public and three private/generated producer origins and all nine named
private client origins. That evidence and original diagonal job 972 do not
certify this new combined graph. No destination Lean/Lake/cache/build or axiom
check was run to prepare this candidate. Its ordinary PR must obtain a
successful both-default-target build and complete private/generated-inclusive
transitive standard-three axiom audit on its actual graph; independent review,
maintainer acceptance/integration and separate official release follow.

For an authorized destination build, first install the pinned Lean toolchain
and **successfully fetch** the matching mathlib cache before any build:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The unchanged pins are Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` and official
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`.
The two new focused targets, if needed **after** that cache fetch, are
`AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero` and
`AlgebraicGroupsTest.AlgebraicallyClosedCommonZero`. These are reproduction
instructions, not observations of a new run. See the [common-zero API guide](../AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md).

## Dated pre-P11 diagonal release-preparation guidance (historical)

The following accepted-code record predates diagonal P11 publication. Its
pending diagonal release statements are history; job 972 checked its original
I10-to-diagonal graph, not the proposed common-zero addition.

### Accepted diagonal code on published exponent: build guidance (2026-09-29)

The diagonal code at accepted and protected-integrated main
`a41c1bc85ed06b0901ab50e86ccc438caff3adf9` (tree
`93646af0eb43065216ef70178946effebcc0830d`) is the sole child of
accepted exponent release-preparation I10
`fe7a86c8ab5484ea60d4baaf0e5deae7cf12986e` (tree
`8f6957f508f70e9042704eb2d1e9f5c6921feb99`). Original native job 972
successfully fetched the matching mathlib cache, built **both** default
targets (3,878 jobs), and audited all 3,788 unique module-origin pairs
(3,769 names, 1,185 private-named origins, including generated declarations)
across all 151 Lean modules; transitive axioms are limited to `propext`,
`Classical.choice` and `Quot.sound`. Fresh author-distinct exact-code review,
separate maintainer acceptance and protected integration are complete. The
exponent's own verified official private P10
`34c5772fb8f00ca6012c0683091a0f93116ea618` remains official. The
isolated diagonal donor's focused 26-package checks and I10's earlier evidence
are not substitutes for this current 13-package native run.

The accepted union has 176 leaves, 151 Lean files (111 production including
aggregate, 40 tests), 97 public aggregate imports, 40 explicit test roots,
87 selected results and unchanged 13 whole manifest packages. Lean is pinned
to `v4.34.0-rc2`, mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, scheme-properties to
`6b204a3e49f022e51d78a9f93e77513b99a87e00` and the published
general-linear-groups dependency to
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc`. The commands below are
reproduction instructions, not a new check. For an authorized build, install
the pinned toolchain and **successfully** fetch its matching mathlib cache
before building both default targets from the project root:

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

The original native job 972 supplies the full current-graph audit, including
private/generated transitive origins; this documentary successor preserves its
Lean/build/dependency/checker inputs but changes the whole-shipping digest.
Optional focused targets after the same cache fetch are
`AlgebraicGroups.GroupScheme.Diagonal` and `AlgebraicGroupsTest.Diagonal`.
Neither these instructions nor earlier donor, exponent or pre-exponent jobs
constitute a new run. The [diagonal guide](../AlgebraicGroups/GroupScheme/Diagonal/README.md)
records its mathematical scope; final independent release review, separate
release acceptance, protected promotions and verified private publication
remain pending, distinct from completed destination code review and acceptance.

## Dated pre-native972 diagonal build snapshot (2026-09-29)

The following initial status was written before original job 972, fresh
destination review and separate code acceptance. It is historical, not current
build guidance or evidence; the commands and pin history remain applicable.

This sole-I10-child diagonal candidate is **not built or audited**. Its parent
`fe7a86c8ab5484ea60d4baaf0e5deae7cf12986e` (tree
`8f6957f508f70e9042704eb2d1e9f5c6921feb99`) is accepted, integrated
exponent release-preparation, with reviewed and verified official private P10
`34c5772fb8f00ca6012c0683091a0f93116ea618` already published. Existing
exponent I10 evidence and the diagonal donor's focused 26-package checks do
not certify this changed diagonal graph. Its own checks and review are next.

## Dated pre-P10 exponent build snapshot (2026-09-29)

The complete I10 guidance follows unchanged. Its 147-Lean count and
exponent-release-pending statements describe the pre-P10 exponent graph,
not the accepted 151-Lean diagonal graph or current publication state.

# Native unitriangular exponent transfer: build guidance (2026-09-29)

The parent I9 `771a5ab485be5aaa0f5f2c553f8b7b2cc3766605` has 168
shipping leaves, 145 total Lean files (107 production including the aggregate,
38 tests), 38 literal test roots, 95 aggregate imports, 70 selected result
objects and 13 whole ordered manifest packages. This candidate has 171 leaves,
147 Lean files (108 production, 39 tests), 39 literal roots, 96 aggregate
imports and 75 selected objects, with the **same** 13 whole packages and pins.
The new module/client are accepted and protected-integrated at development
main `45d4c5ddfcd491f298c4c968561d2e2eccf82e06`.

Original native runs 895 and 912 certify the preceding generation/derived
contribution on its unchanged computational inputs; its own reviewed release
completed at internal I9 and verified official P9
`8fdf180d3b56c6bfb4a5fe8c63204ad9a7abf827`. The accepted isolated
exponent donor has separate focused checks; they are not substitutes for
this destination graph. Original native job 932 on the exact accepted main
fetched 8,892 matching mathlib cache files, verified readiness without a build,
then built both default targets (3,873 jobs). Its complete private/generated-
inclusive transitive audit covered all 3,700 module-origin pairs (3,681 names;
1,181 private-named origins), including the exponent producer's 19 and
ordinary-import client's 2; only `propext`, `Classical.choice` and `Quot.sound`
occurred, with zero rejects. Fresh author-distinct destination review and
Lattice's separate code acceptance/protected integration completed. This
contribution's own independent release review, acceptance, protected
promotions and verified private GitHub publication remain outstanding;
official P9 does not contain exponent. The commands below are reproduction
instructions, not a new build:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupTheory.UnitriangularExponent
lake build AlgebraicGroupsTest.UnitriangularExponent
LAKE_JOBS=2 lake build
```

Lean remains `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and scheme-properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`.
See the [exponent guide](../AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
for the mathematical API and edge cases.

## Dated 2026-09-28 pre-P9 generation/derived snapshot (historical)

The preserved text below describes the prior release-readiness state. Its
“pending” statements were true for that dated snapshot and were superseded
by the completed I9/P9 release; its job counts remain scoped to their old
inputs, not this new 147-module graph.

### Generation and derived-series transfer: build guidance (2026-09-28)

The separately accepted lower-central series L is on main and internal
release I8 `164f0310a4f641cc1d698a14b333082bbfcfe474`, and at verified
official published P8 `441817ab159b20bb7c9c855b05d49abfa3d85c92`.
Original native jobs 865 and 885 checked its unchanged 143 **total** Lean
files (106 production including the aggregate, 37 tests/registered roots)
and 13 whole resolved packages, with a matching cache fetched before builds
and complete transitive standard-three axioms including private/generated
origins. Those are dated **old L** checks, not evidence for the changed
generation producer/client or new derived-series producer/client.

The accepted destination has 145 **total** Lean files (107 production including
the aggregate, 38 tests and 38 literal test roots), 95 aggregate public imports,
70 selected main-result objects, and the same 13 complete ordered manifest
packages. Original native run 895 on exact accepted/protected-integrated main
`a77d4e4d19f6dc366eb9a40f16503f5855421cf3` fetched the matching cache,
built both default targets (3,871 jobs), and completed the current-input
transitive standard-axiom audit: 3,679 module-origin pairs, 3,661 distinct
names, 1,168 private-named origins, all generated origins and zero rejects.
Only `propext`, `Classical.choice` and `Quot.sound` occurred. The changed L
producer/client contributed 37/24 audited origins and derived 13/20. Fresh
author-distinct destination review and maintainer code acceptance are complete;
separate fresh release review/acceptance, protected promotion and verified
publication remain pending. Old jobs 865/885 and isolated donor checks 61/33
do not certify this 145-module destination. The original static plan counted
143 as production; the dated correction was 143 total → 145 total (107
production/38 tests). Documentary changes preserve checked Lean, build,
dependency and checker inputs, not the whole-shipping-file digest.

The toolchain remains Lean `v4.34.0-rc2` with pinned mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, published
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and scheme-properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`.
For authorized reproduction, fetch the matching cache before either default
target; these commands are instructions, not a claim of a new run for this
documentary successor:

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

See the [generation guide](../AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md)
and [derived guide](../AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
for focused imports. The prior release-readiness snapshot and earlier resource
history below are preserved as dated evidence, not current checks.

## Dated lower-central I8 release-readiness snapshot (before P8 publication)

# Lower-central-series transfer: current build guidance (2026-09-28)

The native lower-central-series producer and ordinary-import client were
accepted on development main `d3c455d9adac06b5a873828ea7de57d5501c42f4`
with sole released I7 parent
`28a4dd05b2f2f2c1aae5e2161338b953b454b762`.
I7's sharpness result is published at verified official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8`; the L result is **not yet
separately released or published**. Its actual graph has 143 Lean modules, 37
persistent regression roots and 13 resolved whole packages.
Original native job 865 (2026-09-28) fetched the matching mathlib cache,
verified readiness, built both default targets (3,869 jobs) and completed the
actual-graph transitive audit: 3,634 module-origin pairs, 3,616 distinct name
strings, 1,128 private-named origins, all generated origins and zero rejects.
Only `propext`, `Classical.choice` and `Quot.sound` occurred. Its 35 producer
and 14 client origins are included. Fresh independent exact-H destination
review and Lattice's code acceptance/protected main integration are complete.
The project retains the official `general-linear-groups` GitHub dependency at
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` to pinned mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` and Lean `v4.34.0-rc2`.
To check the changed graph, successfully fetch the matching mathlib cache
before building both default targets (`AlgebraicGroups` and `AlgebraicGroupsTest`):

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

If cache retrieval fails, diagnose it rather than rebuilding mathlib from
source. This documentary L release candidate reuses the original successful
native job 865: its Lean sources, both default targets, toolchain, resolved
dependencies and checker inputs are unchanged. The whole-165-file input digest
changes with the documents and is not reused. Separate fresh exact-release
review, maintainer release acceptance, protected promotion and verified GitHub
publication remain pending. The
[lower-central-series guide](../AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md)
gives the focused import and regression client. At the original L transfer's
pre-check preparation on 2026-09-28, its projected counts were not successful
checks, and destination build, audit, review and acceptance were still pending;
native 865 and the subsequent acceptance supersede that candidate-time status.

Native job 843 succeeded on predecessor C
`172234b1ae20be037a781f0a105ae88dfbe3e856`: the matching cache was
fetched before both default targets were built. All 141 local modules and 36
test roots were checked. The complete transitive audit
enumerated 3585 module-origin declarations, including 1082 private-named origins
and all generated origins, and rejected none: only `propext`, `Classical.choice`
and `Quot.sound` occurred. Different modules can reuse a declaration name;
there were 3567 distinct name strings, not 3567 audited module-origin pairs.
Fresh independent destination review and maintainer acceptance followed.
The documentation-only I7 release preparation preserved all C computational
inputs, and the sharpness result reached official P7. The present L producer,
client, aggregate import and explicit test root change those inputs: neither
job 843 nor its 141-module scope certifies the projected 143-module L union.

G/Q are already published at official commit
`38b7ebdcb38bd0d1b3c9a72e266162718f4647c2`; their native job 811
certifies its earlier **139-module, 35-root, 12-package** graph only.
The [sharpness guide](../AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md)
and ordinary-import `AlgebraicGroupsTest.UnitriangularNilpotencyClass` client
describe the additions. The remainder of this guide is the unmodified dated
I6 build/resource snapshot: its then-pending G/Q publication, counts,
measurements and job references are historical, not the L graph's checks.

---

# Build and resource guidance

This guide describes the checked-in library and its build inputs. Use the
repository's `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` together.
The current Lean version is `v4.34.0-rc2`, with mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The project dependencies use
official published GitHub release commits listed in the README and manifest.
The GitHub repositories are currently private and require authorized access.
The checked-in tree includes 139 modules with 35 regression roots selected by the
no-target default build. Build and audit requirements are described below;
exact-version checks and release decisions are recorded separately.

## Build the declared targets

From the project root, fetch the matching precompiled mathlib cache successfully
before building:

```sh
lake exe cache get && lake build
```

If cache retrieval fails, diagnose that failure before continuing. Do not replace
it with an accidental full mathlib source rebuild. Fetch again after changing
Lean/mathlib pins or replacing `.lake`. Dependency caches do not substitute for
compiling the selected library sources. An existing successful build may be
reused when Lean, source and build/dependency inputs are unchanged; a
documentation-only change does not require another build.

The default targets are the production aggregate and all 35 registered regression
roots, reaching all 139 local Lean modules: 104 production files including the
aggregate, and 35 test files. Every checked-in Lean file declares the module system;
the default build checks all regression examples, including anonymous examples.
The axiom audit covers every retained named, private and generated compiled
declaration; a module may contain checked examples without retaining constants.
An applicable ordinary Lean build checks proofs. Native job 530 covers the
separately accepted 125-module, 29-root semidirect predecessor; native job 533
successfully built both default targets of the accepted 130-module, 31-root
snapshot (3,468 jobs). The earlier native job 477 applies only to its
121-module predecessor, not either successor. The additional computational
release check is a transitive
axiom audit covering repository declarations, including private declarations and
dependencies reached from them, using ordinary `#print axioms` or
`Lean.collectAxioms`. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed; `sorryAx` and every additional axiom fail. A source grep is insufficient.
Native job 533 completed this private-inclusive audit for its 130 modules and
3,268 module-origin declarations (944 private-prefix), using only those allowed
axioms. Its exact checked Lean, build, dependency and checker inputs were
unchanged in the predecessor's documentation-only release preparation. The
additional producers, aggregate imports and test root changed the graph.
Native job 682 (2026-09-28) successfully built both configured default targets
(3,471 jobs) and audited all 133 modules: 3,404 module-origin declarations,
including 955 private-named declarations, with only the three allowed axioms.
Independent destination review and maintainer code acceptance cover exact
snapshot `7ad131de3c5a7696df678e944aaa20c1defbb397`. Its documentation-only
preparation changed four of its 150 recorded file tuples, all documentation or
metadata. All Lean, toolchain, build, dependency and checker inputs and all
twelve resolved packages remained unchanged; that predecessor subsequently received
separate release acceptance and verified private GitHub publication. The later
geometry transfer added a producer, client, aggregate import and 33rd test root.
Neither job 682 nor the isolated geometry check certifies those changed inputs.
Native job 718 (2026-09-28, exact accepted main
`31492d5a182c21f40af029121718ceca8085568a`) successfully fetched the
matching mathlib cache, built both configured default targets (3,473 jobs),
and audited all 135 modules and 3,419 actual-origin declarations, including
956 private-named declarations, with only the three allowed axioms. The fifteen
actual geometry declarations include generated and private names; the twelve
selected metadata rows are not its complete audit. Independent non-author
transfer review and maintainer code acceptance/protected main integration are
complete. Geometry subsequently received independent release acceptance and
verified official publication at
`183bbbcebf0693df849ad6f5781df4c97d33364f`. That geometry-release preparation
preserved its checked Lean, build, dependency and checker inputs; the original
whole-153-file input digest describes that earlier destination, not this tree.

The later central-filtration and successive-quotient transfer added four Lean
modules, including two regression roots. Native job 811 (2026-09-28, exact
accepted main `535d623443808796af231ed5761f837c13934cdd`) fetched and verified
the matching mathlib cache, built both default targets (3,480 jobs), and audited
all 139 project modules and 3,542 actual-origin declarations, including 1,048
private-named origins and all generated origins. Only the three permitted
axioms occurred. Neither job 718 nor isolated donor checks certify the added
G/Q graph; job 811 is its complete destination pass. Fresh independent
destination review and maintainer acceptance/protected integration are complete.
This documentation-only release preparation preserves all checked computational
inputs, but not the original whole-file input digest. Independent G/Q release
acceptance and verified publication remain separate, still-pending steps; the
published geometry release named above does not contain G/Q.

Start a downstream client with `import AlgebraicGroups`, or use a focused import
such as `AlgebraicGroups.GroupScheme.Additive` or
`AlgebraicGroups.GroupScheme.Vector` or
`AlgebraicGroups.GroupScheme.Unitriangular`. Its ordinary-import client
`AlgebraicGroupsTest.Unitriangular` is one of the original 32 test roots;
the [group guide](../AlgebraicGroups/GroupScheme/Unitriangular/README.md)
describes its precise hypotheses and boundaries. The new focused import
`AlgebraicGroups.GroupScheme.UnitriangularGeometry` and its ordinary-import
21-example client `AlgebraicGroupsTest.UnitriangularGeometry` expose the
underlying affine-space iso, relative smoothness/integrality and field-only
numeric dimensions; see the [geometry guide](../AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md).
For the point-group central series and positive-stage successive quotients, use
`AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration` and
`AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients`; their two
ordinary-import clients are included in the 35 regression roots. The
[filtration guide](../AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
and [quotient guide](../AlgebraicGroups/GroupTheory/UnitriangularSuperdiagonalQuotients/README.md)
state the exact hypotheses and distinguish these APIs from scheme quotients.
After a successful matching cache fetch, reproduce the focused clients and
both default targets with:

```sh
lake exe cache get
lake build AlgebraicGroupsTest.Unitriangular
lake build AlgebraicGroupsTest.UnitriangularGeometry
lake build
```

These commands are reproduction guidance; native job 811 supplies applicable
destination build and audit evidence for the unchanged computational inputs.
That evidence does not by itself accept or publish the G/Q release. Job 718 is
retained above as evidence for the earlier, now-published geometry destination.
Representative clients are in `AlgebraicGroupsTest/`. Some generated auxiliary
names have changed during the native-module migration; use the authored APIs
described in the README.

## Measured development baseline

The following observations are from the independently reviewed development
revision `dde1583ebf4ad6df11b53fcbad526f7d1d9ff6e4` on 2026-09-26. It precedes
the infinitesimal-additive test changes and final official dependency
selection. It is useful planning context, **not** a cold full-release benchmark
or a measurement of the current final candidate.

| Workload | Observed wall time | Context |
| --- | ---: | --- |
| Successful matching mathlib cache retrieval | 51 s | 8,892 files decompressed; network/cache-dependent. An earlier thread-creation failure is not counted as a success. |
| 53 staged/root/default build invocations plus two ordinary clients | 593 s total | Pinned development graph, dependency cache available, serial compiler dispatch; longest invocation 100 s. This total includes the warm default below. |
| Final warning-fatal default build | 4 s | 3,402 Lake jobs after the staged work; most outputs already existed. Not a clean-build time. |
| Existing MatrixEndAdditive / MatrixEndScheme ordinary clients | 6 s / 5 s | Included in the 593 s total, after their dependencies were built. |

That Linux worker had a 15 GiB aggregate memory cap, a 12 GiB virtual-address limit
per compiler process, and actual serial Lean dispatch (`-j1`, runtime thread
count 1). These are execution limits, **not measured peak resident memory** or a
portable minimum-RAM promise. Memory-limit pressure events were recorded; do not
infer an absence of pressure from successful completion. CPU model, disk and
network throughput are not standardized by this baseline. Two earlier author
default attempts on different preparation states timed out after 240 s each.

Plan for dependency/cache preparation and several minutes of source compilation
on a comparable warm-dependency, serial setup, with additional time for all
shipped tests and the complete transitive axiom audit. This is an
estimate based on the development observations, not a bound. A cold or changed
dependency graph can take substantially longer. The final official-pin build
on 2026-09-26 used matching cached dependencies and retained warm outputs through
three diagnosed source corrections. Its final successful stage took 18.351 s,
including the remaining affected chain and no-target default. This is not the
total compilation time or a cold-build benchmark; all 102 applicable module
builds and all 19 regression roots were covered across that sequence.

A separate successful pinned native run on 2026-09-27 (job 533) measured
42.817 s for its matching mathlib cache retrieval and 290.620 s for its
both-default-target build of 3,468 jobs. These are stages of that actual run,
not a cold total-time benchmark, a peak-memory measurement or a resource
guarantee; they do not replace the dated development baselines above.

## What a build does not establish

Neither a build nor an axiom audit establishes the accuracy of documentation,
API and source-correspondence claims, metadata, licensing and attribution, file
hygiene, official dependency identities or release history. These require
lightweight inspection and independent substantive review. Existing documentation
and applicable evidence are reused, with concrete inaccuracies corrected.

Separate exhaustive stored-proof replay, fresh expensive API-documentation
generation, runtime/cache-equivalence reconstruction and repeated compilation as
both an internal and a GitHub consumer are not release prerequisites. Actual
publication still requires the accepted artifact and independent public history,
the intended private destination and exact mirrored commit/ref verification.
