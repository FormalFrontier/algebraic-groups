# Upper-triangular diagonal split kernel

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` directly or
through `AlgebraicGroups`. For an arbitrary commutative ring `K` and finite
linearly ordered index type `n`, the diagonal projection `T ⟶ D` has a
section, and the closed unitriangular group scheme `U` is the *genuine
scheme-theoretic identity fiber*, not just a kernel on selected points.
The [producer](../UpperTriangularSplitKernel.lean) proves a `CommRingCat`
coordinate pushout and pullbacks of schemes, schemes over `Spec K` and group
schemes; it identifies both comparisons inside GL and the projection,
section and inclusion formulas on points over **every** commutative
`K`-algebra. See the [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean)
and [build guide](../../../docs/BUILDING.md).

No field, nonempty-index, reducedness, flatness or injectivity assumption
is needed. This interface does not provide a represented semidirect law,
normality of `U` in GL, arbitrary-base scheme change, dimension/smoothness
or source-specific correspondence. The finite [diagonal product](../DiagonalProduct/README.md)
and earlier [triangular group scheme](../UpperTriangular/README.md) remain
separate, reusable interfaces.

## Dated frozen-W split-kernel guide (complete 2026-09-29 historical snapshot)

The entire preceding guide follows unchanged. Its nested “current”,
“unchecked” and lifecycle labels are dated candidate history, not the
status of a later release; its original donor, mapper, transfer and review
credit remains intact.

---

# Upper-triangular diagonal split kernel

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` directly or
through `AlgebraicGroups`. For any commutative base ring `K` and finite linearly
ordered index `n`, the projection from the upper-triangular group scheme `T` to
the diagonal group scheme `D` has a section (section then projection is `𝟙 D`).
The unitriangular group scheme `U` is its scheme-theoretic identity fiber:
the coordinate square is a genuine `CommRingCat` pushout, inducing pullbacks
of schemes, schemes over `Spec K`, and group schemes. Its inclusion into `T`
is closed, both inclusions into GL agree with the established maps, and the
projection, section and inclusion formulas hold on every commutative
`K`-algebra's points. See the [producer](../UpperTriangularSplitKernel.lean)
and [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean).
There is no field, nonempty-index, reducedness, flatness or injectivity
requirement. This API does not provide a represented semidirect law,
normality of `U` in GL, arbitrary-base scheme change, smoothness/dimension
or source-specific correspondence.

**Scoped earlier evidence.** The same complete producer and client bytes in
original split candidate `fd4b61f91e94c2608875d606fb69e80d1c247d3d`
passed original cache-first native 1063 (both default targets and transitive
private-inclusive standard-three axiom audit) and independent exact-C review
4917. Integrated diagonal-product code at
`ad5bff948f563bb9df49825f55dfcc8fcace8130` has separate original native
1058 and code review 4912. None of those different-tree results verifies
this combined shipping tree or supplies its fresh final review, acceptance or
publication. Dated 2026-09-29 static repaired-parent renewal credit:
worker-a Hive Task `hive-request-4858ca079644447900997ac218698753e3e37f5b`
(UID `9dafa64c-e479-4135-a48e-c670d90d0eaa`), not a mathematical author,
independent reviewer or accepting maintainer. Original donor, mapper,
transfer, reviewer and frozen-parent renewer credits remain below.

## Dated frozen-B split-kernel guide (complete prior N history, 2026-09-29)

The entire earlier N guide follows unchanged. Its “current” frozen-B labels
and pending decisions describe N's preparation stage, not the status of this
repaired-parent assembly or a later publication. N itself embeds the complete
original C guide, including its historical donor and review statements.

---

# Upper-triangular diagonal split kernel on the prospective product parent

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` (also publicly
imported by `AlgebraicGroups`). Over any commutative base ring `K` and finite
linearly ordered index `n`, the existing upper-triangular group scheme `T`
splits over its diagonal group scheme `D`: the diagonal projection has a
section, and the unitriangular group scheme `U` is its **scheme-theoretic
identity fiber**. This uses a genuine coordinate-ring `CommRingCat` pushout
and genuine pullbacks in schemes, schemes over `Spec K`, and group schemes.
The closed inclusion `U ⟶ T` and both comparisons inside GL are exposed, with
formulas for all commutative `K`-algebra points, including zero rings and
noninjective coefficient maps. See the [producer](../UpperTriangularSplitKernel.lean)
and [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean).
No field, nonempty-index, reducedness, flatness or injectivity hypothesis is
added; this does not assert a represented semidirect product, normality in GL,
arbitrary-base scheme change, dimension/smoothness, or source coverage.

## Current prospective-union lifecycle (2026-09-29)

This **static, unchecked, unreviewed and unaccepted** combination takes the
**exact unchanged** producer and client bytes from original split candidate
`fd4b61f91e94c2608875d606fb69e80d1c247d3d` and adds them to the
**frozen, unaccepted and unreleased** diagonal-product release-readiness
snapshot `9b2a5db2a4bceb6c7146d9cb2ba8e0eb36ed1411`. The product *code*
at protected main `ad5bff948f563bb9df49825f55dfcc8fcace8130` was
accepted, but the later four-document readiness snapshot is **not** accepted
or released. Its independent release review, required native context and
publication are separate; changing that snapshot requires reworking this
prospective union. The already published native and represented upper-triangular
predecessor remains distinct from the pending product release.

The original split candidate passed its own cache-first both-default-target
native run 1063 and complete private/generated-inclusive transitive
standard-three axiom audit, and received fresh independent exact-candidate
review 4917. Those results apply to its **original** 13-package tree, not
this combined candidate. They do not establish a union build, union axiom
audit, fresh union review, maintainer acceptance, integration or publication.
A later authorized check must fetch the matching pinned mathlib cache before
building both default targets; this static author did not run Lean, Lake,
cache fetches, a checker or CI. The donor's separate 103-origin result likewise
belongs only to the earlier isolated graph.

Static union-renewal author: worker-b Hive Task
`hive-request-e99d1ea83bdaf0ed69b40e167a4e6b8bf8cec52f` (UID
`e8aa361b-0375-4638-b258-2168f3a2fb73`). The entire dated original
candidate guide follows byte-for-byte below, retaining donor, planner,
transfer and reviewer credit; its “STATIC UNCHECKED” label and the donor's
older “five-field” language are historical, not current evidence. The
current 13-package manifest has **six total** root fields, including
`packages`, plus `version`, `packagesDir`, `name`, `lakeDir`, and
`fixedToolchain`.

## Dated original split-candidate guide (complete C history, 2026-09-29)

---

# Upper-triangular diagonal split kernel

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` (also publicly
imported by `AlgebraicGroups`). For a commutative base ring `K` and finite
linearly ordered index `n`, this module uses the existing closed
upper-triangular group scheme `T`, diagonal group scheme `D`, unitriangular
group scheme `U` and ambient general-linear scheme. There is no field,
nonzero-ring, nonempty-index, reducedness, flatness or injectivity assumption.
The [producer](../UpperTriangularSplitKernel.lean) and
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean)
are usable without the historical donor research.

## Mathematical API

* `AlgebraicGeometry.upperTriangularDiagonalProjection K n : T ⟶ D` and
  `AlgebraicGeometry.upperTriangularDiagonalSection K n : D ⟶ T` split in the
  order section followed by projection equals `𝟙 D`, by
  `upperTriangularDiagonal_section`. This does not assert that projection
  followed by section is the identity of `T`.
* `AlgebraicGeometry.unitriangularToUpperTriangular K n : U ⟶ T` is a closed
  immersion on underlying schemes. Its compatibility with the inclusion
  `T ⟶ GL` and that of the diagonal section are given by the separate
  `unitriangularToUpperTriangular_inclusion` and
  `upperTriangularDiagonalSection_inclusion` equalities.
* `upperTriangularDiagonalSquare_isPushout` proves a genuine coordinate
  `CommRingCat` pushout using arbitrary compatible ring maps, the entire
  existing U Hopf ideal and quotient surjectivity. The contravariant `Spec`
  square and connected-limit preservation/creation then give actual
  `upperTriangularDiagonalSquare_isPullback` (schemes),
  `upperTriangularDiagonalSquare_isPullback_over` (schemes over `Spec K`) and
  `upperTriangularDiagonalSquare_isPullback_group` (group schemes). Thus `U`
  is the identity-fiber kernel of `T ⟶ D`, not merely a field-point kernel.
* The three coordinate maps and `*_point` formulas identify the represented
  arrows with native matrix `diagonal`, `diagonalSection` and
  `inUpperTriangular` on every commutative `K`-algebra `R`. Existing native
  fixed-base naturality also covers noninjective coefficient maps.

The client checks typed maps and pullbacks, splitting, closedness, both GL
comparisons, all-algebra point formulas and fixed-base naturality. Its private
examples include `Fin 0`, `Fin 1`, an independent-diagonal-units `Fin 2` shear,
`ZMod 1`, a nonzero square-zero dual-number shear and noninjective reduction.
The native U-first point-group semidirect decomposition is a different result:
no group-scheme semidirect or direct-product theorem, normality in GL,
arbitrary-base-change theorem, smoothness/dimension or source coverage is
claimed here.

## Reproduction and provenance (2026-09-29)

This destination transfer is **STATIC UNCHECKED**: its new producer/client
and both default targets have no applicable destination build, transitive
axiom audit, fresh independent review, acceptance, integration or release yet.
In a checkout of this code branch using its pinned Lean and 13-package manifest,
fetch the matching precompiled mathlib cache before any build:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

After successful cache fetch, optionally run
`LAKE_JOBS=2 lake build AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel`
and `LAKE_JOBS=2 lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel`.
These are instructions, not this author's executed commands. The isolated
accepted donor S at `3a98326860b04ee59e5af8a1839aa2dbd8135920` had
separate focused builds and a 103-origin transitive standard-three audit on
its *different* dependency graph; its collector lives only in a separate
evidence commit `1b8fc7d19f8fd7e73a5568d2322f2242c63edcfa`.
The original guide's “five-field” manifest description below is a dated
mistake: both its 26-package graph and the current released predecessor's
13-package graph have **six** root fields (`version`, `packagesDir`,
`packages`, `name`, `lakeDir`, `fixedToolchain`). The donor's old
“independent review pending” language describes its pre-review stage; the
donor was subsequently independently reviewed and separately accepted, while
this destination candidate remains unchecked. The predecessor
`14cd731a7a934709e28945ba1f22cedac59c3438` is already officially
released and published; its checks do not certify this transfer.

This transport author is worker-b Hive Task
`hive-request-5430a7ea19bdaf4d587462ec39220e2577018798` (UID
`24b28e74-2a89-4f66-b3a4-9276fb2d4525`). Original mathematical and Lean
work is credited to donor worker-b Task
`hive-request-8a894f4ae8eb1e23cb2c2b0a446e015aaf0aa44f` (UID
`22e1595e-13f2-4d64-9e28-503288271bc8`), planner worker-a Task
`hive-request-390d93e25796c950b59e13f5efc0b34122383b09` and fresh
donor reviewer worker-a Task
`hive-request-51ab92c80330e9f0a5fa961d6322cb184d1cd3c3` (UID
`dc3a8b31-7303-481f-bcbb-e24e63d73c85`). The proof follows the published
`AlgebraicGroups.GroupScheme.SpecialLinearKernel` pushout/Spec/Over/Grp
pattern; the preexisting T/D/U/GL APIs and their credited contributors retain
their own licenses and provenance. This library and code use Apache-2.0;
no human author or source endorsement is invented.

## Dated isolated donor guide (entire original at S, 2026-09-29; historical)

# Diagonal split kernel of upper-triangular group schemes

Import `Incubator.GroupScheme.UpperTriangularSplitKernel`. For any commutative
ring `K` and finite linearly ordered type `n`, this module uses the existing
upper-triangular, diagonal, unitriangular and general-linear group schemes over
`Spec K`. The published unitriangular Hopf quotient is not redefined. No field,
nonzero-ring, flatness, reducedness, or nonempty-index hypothesis is required.

## Reusable API

* `upperTriangularDiagonalProjection K n : T ⟶ D` and
  `upperTriangularDiagonalSection K n : D ⟶ T` are group-scheme morphisms.
  `upperTriangularDiagonal_section` proves section followed by projection is
  the identity of `D`. This does **not** say projection followed by section is
  the identity of `T` or assert a direct-product law.
* `unitriangularToUpperTriangular K n : U ⟶ T` is a group-scheme morphism;
  `unitriangularToUpperTriangular_isClosedImmersion` proves its underlying
  scheme map is a closed immersion. The equations
  `unitriangularToUpperTriangular_inclusion` and
  `upperTriangularDiagonalSection_inclusion` compare the two inclusions in GL.
* `upperTriangularDiagonalSquare_isPushout` establishes the **CommRingCat**
  pushout of the diagonal-coordinate projection map along the diagonal Hopf
  counit, with apex the existing unitriangular coordinate ring. Its universal
  property accepts arbitrary commutative target rings and arbitrary compatible
  base-scalar maps. `upperTriangularDiagonalSquare_isPullback`,
  `upperTriangularDiagonalSquare_isPullback_over` and
  `upperTriangularDiagonalSquare_isPullback_group` give actual pullbacks in
  schemes, schemes over `Spec K`, and group schemes, respectively. The final
  theorem exhibits `U` as the genuine identity-fiber kernel of `T ⟶ D`.
* `upperTriangularDiagonalProjection_point`,
  `upperTriangularDiagonalSection_point`, and
  `unitriangularToUpperTriangular_point` identify every represented
  commutative `K`-algebra point with the existing native matrix operations
  `diagonal`, `diagonalSection`, and `inUpperTriangular`. The underlying
  coordinate equalities are also exposed as the three `*CoordinateMap_point`
  theorems. Fixed-base naturality follows from these formulas and the
  preexisting native matrix-map naturality, including noninjective algebra maps.

The proof works in the **localized GL coordinate ring**, using its determinant
inverse and quotient. On diagonal coproducts it eliminates off-diagonal tensor
summands *after* the upper-triangular quotient. The pushout factors a compatible
`T → B` through `U` by killing the lower entries and diagonal-minus-one
relations, and derives `K → B` compatibility from the given cocone rather than
postulating a `K`-algebra structure on `B`. Contravariant `Spec` and genuine
limit-creation/preservation instances lift that square to `Over` and `Grp`.
It is not an inference from field-valued points or faithfulness alone.

`IncubatorTest.GroupScheme.UpperTriangularSplitKernel` imports the producer
normally and checks the typed group, scheme and over pullbacks, splitting,
closed immersion, both GL inclusion compatibilities, all three all-algebra
point formulas, fixed-base naturality and a noninjective reduction map. Its
private cases include `Fin 0`, `Fin 1`, `Fin 2` with a shear and two independent
diagonal units, the zero ring `ZMod 1`, and a nonzero square-zero dual-number
shear in the unitriangular kernel.

## Reproduction and status

This isolated contribution retains its inherited 26-package/five-field Lake
manifest and toolchain: Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, published
algebraic-groups `f49141f0cd92a101d587a344eb3e2bd5bf4331d8`,
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
and scheme-properties `193d4fe284cf1de71b168c198ad7b24a6eb71d39`.
From a checkout at the corresponding isolated code revision, run:

```sh
lake exe cache get
lake build Incubator.GroupScheme.UpperTriangularSplitKernel IncubatorTest.GroupScheme.UpperTriangularSplitKernel
```

The collector is **not** a code-branch import or a source for clients. In a
separate checkout of the evidence branch
`worker-b/upper-triangular-split-kernel-evidence-20260929`, which includes
`research/UpperTriangularSplitKernelImplementation/Collector.lean`, use the
same pinned cache before running:

```sh
lake exe cache get
lake env lean research/UpperTriangularSplitKernelImplementation/Collector.lean
```

On **2026-09-29**, both focused builds exited 0 after the matching mathlib
cache fetched successfully; the complete `Lean.collectAxioms` inventory of
all **60 producer and 43 client module-origin declarations**, including
private and automatically generated declarations, exited 0 with no axioms
outside `propext`, `Classical.choice`, `Quot.sound`. The original commands,
logs, inventory and exact revisions are retained at the fixed evidence branch
path `research/UpperTriangularSplitKernelImplementation/REPORT.md` and its
companion artifacts. The accepted preexisting T, D and U evidence is reused,
not replayed. This status is *implementation and computation only*; independent
review, owner acceptance, shared-main integration and publication are separate.

## Provenance and limits

Author: worker-b Hive Task
`hive-request-8a894f4ae8eb1e23cb2c2b0a446e015aaf0aa44f`
(UID `22e1595e-13f2-4d64-9e28-503288271bc8`). This additive code has
the isolated represented upper-triangular commit
`f14e42727971533ce8319f80e17be7a9bc7e5a3f` as its sole parent.
It adapts the published `AlgebraicGroups.GroupScheme.SpecialLinearKernel`
pushout/Spec/Over/Grp proof pattern and uses already published U/GL APIs and
the preexisting local D/T coordinates and native matrix maps. The mathematical
route was outlined by a separate planner, worker-a Hive Task
`hive-request-390d93e25796c950b59e13f5efc0b34122383b09`.
Published dependency credits and license terms remain those of their respective
repositories; this implementation does not copy their definitions or proofs.

There is no claim here of U normality in GL, a semidirect/product decomposition,
arbitrary-base change, smoothness, dimension, a source-specific correspondence
or source-coverage acceptance. This file and the reusable Lean APIs require no
source-repository research record to interpret or use.
