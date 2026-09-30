# Algebraic groups

## Headline results

- **Unitriangular group-scheme identity and tower coherence.** The native
  one-step base-change map agrees with the canonical pullback identity unit
  and direct-to-iterated scalar-tower compositor. An ordinary-import `Fin 2`
  client checks the inverse coordinate through both routes. See the
  [standalone group-scheme coherence guide](docs/UnitriangularSchemeBaseChangeCoherence.md).
  This 2026-09-30 static transfer prepares an unaccepted donor, not a
  destination build, review, acceptance, release or source-coverage decision.
  Original proofs/client: worker-b Task `hive-request-060cf9c4f55345280f96724efb23b870529b5dd3`
  (UID `a59545aa-87cc-40a0-b35e-c980d68c912a`); official-import adaptation:
  worker-b Task `hive-request-3e98325c49b66caef94ea71d0ab8e154a9a23c51`
  (UID `c6a480de-e7b4-44f8-8106-17e6d759ecc7`); destination preparation:
  worker-b Task `hive-request-83e761635ef9fb7b8563c64cbaa53c61a6eced8b`
  (UID `51aa9bf0-39a7-45b6-9dbd-6cf8bdf19217`). Prior credits remain below.
- **Native unitriangular group-scheme base change.** Over arbitrary same-universe
  commutative rings and finite linearly ordered indices, the actual pulled-back
  unitriangular group object is isomorphic to the group scheme over the new
  base. The forward map and base projection have readbacks; an ordinary-import
  `Fin 3` client retains the group-product cross term. See the
  [standalone scheme base-change guide](docs/UnitriangularSchemeBaseChange.md).
  This 2026-09-30 transfer from an unaccepted contribution is **static
  preparation**, not a destination build, independent review, acceptance,
  integration, release or source-coverage decision. Original proofs/client:
  worker-b Task `hive-request-c40cd5bb6871cfc2115117cb21f9d78a5aee869d`
  (UID `28adbb76-eddd-457f-afde-a58666e8d21f`); destination preparation:
  worker-b Task `hive-request-26588c9f7acea2845592c20813ff60f338e95b0f`
  (UID `ffd35190-20bc-44bb-82ec-489771fac380`). Existing AG Hopf and mathlib
  contributors retain their prior credit. Prior results below are unchanged.
- **Unitriangular coordinate-algebra base change.** For arbitrary commutative
  rings `R`, `S` with `[Algebra R S]` and finite linearly ordered `ι`, scalar
  extension of the actual unitriangular GL quotient is `S`-algebra equivalent
  to its quotient over `S`, including the zero ring and empty indices. Its
  presentation, coefficient and all-entry laws are in the
  [base-change guide](AlgebraicGroups/Algebra/UnitriangularBaseChange/README.md).
- **Canonical unitriangular Hopf base change.** Over the same arbitrary
  commutative base rings and finite linearly ordered indices, the algebra
  comparison preserves the counit and coproduct of the independently given
  tensor-product and quotient Hopf structures, hence gives a bialgebra
  equivalence and intertwines their antipodes. The all-entry coproduct
  formula and nonprimitive `Fin 3` client are in the
  [Hopf base-change guide](AlgebraicGroups/Algebra/UnitriangularHopfBaseChange/README.md).
- **Unitriangular base-change coherence.** The actual quotient comparison
  agrees with the tensor unit along the identity and with tensor cancellation
  along a commutative scalar tower, as equalities of algebra equivalences.
  See the [coherence guide](AlgebraicGroups/Algebra/UnitriangularBaseChangeCoherence/README.md).
- **Finite triangular geometry and native dimension.** Over any commutative
  ring, the native multiplicative, finite diagonal and finite upper-triangular
  schemes are smooth with geometrically integral *fibers* over `Spec K`; their
  total underlying schemes are integral when `K` is a domain. Empty index
  types and zero rings are allowed for the relative assertions. Independently
  importable diagonal/strict/retained-index equivalences split weakly ordered
  pairs without finiteness and count finite pairs as `card ι + (card ι).choose 2`.
  For the **actual native** upper-triangular GL quotient, both ideal inclusions
  and the localized coordinate equivalence identify native retained entries
  and polynomial variables in both directions over *any* commutative ring.
  Its identity-determinant point gives native ring and affine `Spec` dimension
  `card ι + (card ι).choose 2` over every field, including finite fields and
  empty indices; no arbitrary-base or general product-dimension formula follows.
  See the [geometry guide](AlgebraicGroups/GroupScheme/FiniteTriangularGeometry/README.md),
  [indices guide](AlgebraicGroups/LinearAlgebra/Matrix/UpperTriangularIndices/README.md)
  and [native dimension guide](AlgebraicGroups/GroupScheme/UpperTriangularDimension/README.md),
  each linking its focused producer and ordinary-import client.
- **Coordinate elimination and finite diagonal dimension.** For any commutative
  ring, `MvPolynomial.localizedCoordinateQuotientEquiv` identifies a polynomial
  localization modulo eliminated coordinates with localization at the erased
  polynomial, even if that polynomial erases to zero or the base ring is trivial.
  Over any field and finite variable type, the independent theorem
  `MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero` gives dimension
  `Fintype.card σ` when a *supplied* field-valued point does not annihilate the
  denominator; a nonzero denominator alone need not supply that nonvanishing
  field-valued point over a finite field. This limitation concerns the supplied-point
  hypothesis, not the general full-dimension formula for a nonzero denominator.
  Applying both APIs to the **actual** finite diagonal Hopf quotient,
  `DiagonalCoordinateRing.localizedPolynomialEquiv` identifies both directions
  of its retained coordinates, and
  `AlgebraicGeometry.diagonalGroupUnderlyingScheme_topologicalKrullDim` gives
  dimension `Fintype.card ι` for every field and finite decidable `ι`, including
  empty indices. Use the independent [elimination guide](AlgebraicGroups/Algebra/LocalizedCoordinateQuotient/README.md),
  [localization-dimension guide](AlgebraicGroups/Algebra/FinitePolynomialLocalizationDimension/README.md)
  and [native diagonal guide](AlgebraicGroups/GroupScheme/DiagonalDimension/README.md),
  with their focused producer modules and `AlgebraicGroupsTest` ordinary clients.
- **Represented U-first upper-triangular coordinates.** For any commutative
  ring `K` and same-universe finite linearly ordered index type `n`, the
  unitriangular scheme `U`, diagonal scheme `D` and upper-triangular scheme
  `T` over `Spec K` admit a categorical isomorphism of underlying schemes
  `U ⊗ D ≅ T` in `Over (Spec K)`. Its forward arrow is `i(u)e(d)`; its inverse
  recovers the diagonal by projection and the unitriangular factor by right
  (column) normalization. The represented diagonal action on the actual
  scheme-theoretic identity fiber sends the `(i,j)` entry of `u` to
  `d_i * u_ij * d_j⁻¹`. For arbitrary test schemes, multiplication in these
  coordinates is `(u,d)*(u',d') = (u*α(d,u'), d*d')`: the categorical product
  does **not** carry the canonical direct-product group law under this iso.
  Point readbacks hold over every commutative `K`-algebra, including zero and
  nonreduced rings; empty indices and noninjective coefficient maps need no
  exception. Import
  `AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`; see its
  [producer](AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct.lean),
  [ordinary-import client](AlgebraicGroupsTest/GroupScheme/UpperTriangularSchemeProduct.lean)
  and [mathematical guide](AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md).
- **Split identity fiber and finite diagonal product.** The diagonal
  projection `T ⟶ D` has a section, and the closed unitriangular subgroup
  identifies with its *scheme-theoretic* identity fiber. See the
  [split producer](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean)
  and [split guide](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md).
  For finite decidable same-universe `n`, `D` is the categorical product of
  copies of `Gₘ` over `Spec K`, including the empty-index terminal case;
  see the [diagonal-product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md).
  Earlier [native triangular](AlgebraicGroups/GroupTheory/UpperTriangular/README.md),
  [represented triangular](AlgebraicGroups/GroupScheme/UpperTriangular/README.md),
  [unitriangular](AlgebraicGroups/GroupScheme/Unitriangular/README.md) and
  [common-zero](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md)
  interfaces remain available under their documented hypotheses.

The represented-product assertions are over the fixed base `Spec K`; they assert
neither a global transported group-object instance, arbitrary-base change,
normality of `U` in `GL`, nor source-specific coverage. The finite triangular
geometry and dimension above are separately scoped results.

## Use and build

Import `AlgebraicGroups` or the focused producer above. From the project root,
install the repository-pinned Lean toolchain, successfully fetch the matching
precompiled mathlib cache and build **both** default targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups AlgebraicGroupsTest
```

The [building guide](docs/BUILDING.md) lists the exact declared dependencies
and optional focused targets. Private research and evidence are not library-use
dependencies. This documentation introduction is by worker-a Hive Task
`hive-request-5b09e086919b2a86fb5230d5fd2ee02ac1f4e585` (UID
`e8705205-8984-46ec-9e40-00d34c8821b3`), **not** a new mathematical
author or reviewer; the dated original credit and complete preceding README
follow unchanged.

## Historical preceding README (complete P snapshot, 2026-09-29)

The entire preceding document follows byte-for-byte. Its descriptions of
earlier candidate stages and their lifecycle are dated historical evidence;
the current import and reproduction instructions are above.

# Algebraic groups: represented upper-triangular U-first products and diagonal actions

## Headline results

For any commutative ring `K` and finite linearly ordered `n`, the represented
unitriangular kernel `U`, diagonal group scheme `D`, and upper-triangular group
scheme `T` over fixed `Spec K` admit an underlying-scheme U-first isomorphism
`U ⊗ D ≅ T`, with forward arrow `i(u)e(d)`. The diagonal section acts on
the actual scheme-theoretic kernel by represented conjugation; an arbitrary-test
diagram realizes the twisted multiplication, not a direct-product group law.
Zero and nonreduced rings, empty indices and noninjective coefficient maps
remain within the stated hypotheses. See the [U-first guide](AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md),
[producer](AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct.lean),
[ordinary-import client](AlgebraicGroupsTest/GroupScheme/UpperTriangularSchemeProduct.lean),
[split-kernel guide](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md),
and [diagonal-product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md).

## Historical preceding README (complete W snapshot, 2026-09-29)

The entire preceding document follows unchanged; its dated candidate and
publication-status descriptions belong to their respective earlier snapshots.

# Algebraic groups

Reusable algebraic-group and group-scheme APIs over commutative bases include
upper-triangular groups and their diagonal/unitriangular structures, finite
diagonal products, and earlier unitriangular and common-zero results. The
mathematical interfaces stand independently of any particular source.

## Headline results

- **Diagonal splitting and its scheme-theoretic kernel.** For every commutative
  ring `K` and finite linearly ordered index type `n`, the projection of the
  upper-triangular group scheme `T` to the diagonal group scheme `D` has a
  section. The closed unitriangular subgroup scheme `U` is the *actual identity
  fiber*: a coordinate-ring pushout induces pullbacks of schemes, schemes over
  `Spec K`, and group schemes. Projection, section and inclusion agree with
  native formulas on points over every commutative `K`-algebra. See the
  [producer](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean),
  [ordinary-import client](AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean)
  and [split-kernel guide](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md).
- **Finite diagonal group-scheme product.** For any commutative `K` and
  same-universe finite decidable index `n`, `D` is the literal categorical
  product of copies of `Gₘ` in group schemes over `Spec K`. Its Hopf
  projections and universal property work for arbitrary test schemes, and
  the empty-index case is terminal. This result already has its own published
  release. See the [producer](AlgebraicGroups/GroupScheme/DiagonalProduct.lean),
  [ordinary-import client](AlgebraicGroupsTest/DiagonalProduct.lean) and
  [product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md).
- **Earlier APIs.** The [native upper-triangular groups](AlgebraicGroups/GroupTheory/UpperTriangular/README.md),
  [represented upper-triangular subgroup](AlgebraicGroups/GroupScheme/UpperTriangular/README.md),
  [diagonal group scheme](AlgebraicGroups/GroupScheme/Diagonal/README.md),
  [unitriangular series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md),
  [unitriangular exponent bounds](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
  and [common-zero theorem](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md)
  remain available under the hypotheses in their respective guides.

The split-kernel construction requires no field, nonempty-index,
reducedness, flatness or injectivity hypothesis. It does **not** assert a
represented semidirect law, normality of `U` in GL, arbitrary-base scheme
change, dimension/smoothness or source-specific coverage.

## Use and build

Import `AlgebraicGroups` or the focused producer module above. From the
project root, install the pinned Lean toolchain and **successfully fetch the
matching mathlib cache before building both default targets**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build
```

The [build guide](docs/BUILDING.md) gives the exact dependencies and optional
focused producer/client commands. Build-checked ordinary-import examples live
in `AlgebraicGroupsTest`. The project uses Apache-2.0; retain distinct
third-party attributions and licenses from the pinned dependencies.

## Dated frozen-W README (complete 2026-09-29 historical snapshot)

The entire preceding README follows unchanged. All nested “current”,
“pending”, “unchecked” and publication-status wording belongs to its dated
pre-release preparation, not to the current headline or a later publication.

---

# Algebraic groups: upper-triangular split kernels and diagonal products

This library offers a source-independent upper-triangular diagonal splitting,
a finite categorical diagonal-group-scheme product, and the previously
published common-zero, native and represented upper-triangular, diagonal and
unitriangular results. Follow each linked module's hypotheses for reuse.

## Mathematical results

- **Upper-triangular diagonal split kernel.** For any commutative ring `K` and
  finite linearly ordered index `n`, the diagonal projection from the
  upper-triangular group scheme `T` to the diagonal group scheme `D` has a
  section, and the closed unitriangular group scheme `U` is its genuine
  scheme-theoretic identity fiber. A coordinate-ring pushout and pullbacks
  in schemes, schemes over `Spec K`, and group schemes give the splitting;
  the projection, section, closed inclusion and GL-compatibility maps agree
  with native formulas on all commutative `K`-algebras. See the
  [split-kernel guide](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md),
  [producer](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean) and
  [ordinary-import client](AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean).
- **Finite diagonal product.** For any commutative ring `K` and same-universe
  finite decidable index `n`, the diagonal group scheme is the literal finite
  categorical product of `Gₘ`, with genuine Hopf projections, arbitrary-test-
  scheme universality and empty-index terminality, including zero and
  nonreduced rings. See the [product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md),
  [producer](AlgebraicGroups/GroupScheme/DiagonalProduct.lean) and
  [ordinary-import client](AlgebraicGroupsTest/DiagonalProduct.lean).
- **Previously published mathematics.** See the [native triangular](AlgebraicGroups/GroupTheory/UpperTriangular/README.md),
  [represented triangular](AlgebraicGroups/GroupScheme/UpperTriangular/README.md),
  [diagonal](AlgebraicGroups/GroupScheme/Diagonal/README.md),
  [common-zero](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md),
  [derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
  and [exponent](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
  guides.

**Past evidence and limits.** Original split candidate
`fd4b61f91e94c2608875d606fb69e80d1c247d3d` passed native 1063's
cache-first both-default-target build and transitive private-inclusive
standard-three axiom audit and independent exact-C review 4917. The unchanged
integrated diagonal-product code `ad5bff948f563bb9df49825f55dfcc8fcace8130`
has original native 1058 and independent code review 4912. Those different-
tree checks do not establish a combined-tree build, axiom audit, fresh final
review, owner acceptance or publication. No represented semidirect law,
normality of `U` in GL, arbitrary-base scheme change, dimension/smoothness
or source-specific correspondence is asserted. The 2026-09-29 static renewal
performed no new computation. Its renewer is worker-a Hive Task
`hive-request-4858ca079644447900997ac218698753e3e37f5b` (UID
`9dafa64c-e479-4135-a48e-c670d90d0eaa`), distinct from the original
mathematical authors, reviewers and accepting maintainer.

## Dated frozen-B union preparation (N's complete unique introduction, 2026-09-29)

The following entire introduction was added by N on frozen B. Its “current”
labels and prospective decisions are dated history, not present lifecycle
claims. N's marker promising B as the next whole body records N's earlier
layout; in this combined history B appears exactly once, nested inside the
complete repaired-product D body after its own added introduction.

---

# Algebraic groups: diagonal products and upper-triangular split kernels

## Current prospective union (2026-09-29)

- **Upper-triangular diagonal split kernel — static, unchecked union.** Over
  any commutative base ring and finite linearly ordered index, the diagonal
  group-scheme projection `T ⟶ D` admits a section, while the closed
  unitriangular group scheme `U` is its genuine scheme-theoretic identity
  fiber. A coordinate-ring pushout and pullbacks in schemes, over `Spec K`,
  and in group schemes establish this beyond field-valued points; the
  every-algebra point formulas agree with the native diagonal, section and
  inclusion. See the [split-kernel guide](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md),
  [producer](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean) and
  [ordinary-import client](AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean).
- **Accepted diagonal product code; its later release preparation pending.**
  The protected-main product code `ad5bff948f563bb9df49825f55dfcc8fcace8130`
  is accepted and integrated, not officially published. The four-document
  readiness snapshot `9b2a5db2a4bceb6c7146d9cb2ba8e0eb36ed1411` used
  here as a frozen *prospective* parent is itself **unaccepted and unreleased**;
  its independent release review, native context and publication remain
  separate. Its product API represents the literal finite categorical product
  of `Gₘ`, including arbitrary test schemes and the empty index. See the
  [product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md).
- **Published predecessors remain published.** The native U-first triangular
  splitting, represented triangular and diagonal group schemes, common-zero
  results and earlier unitriangular results remain discoverable in the complete
  dated predecessor README below and their linked guides.

The original split candidate `fd4b61f91e94c2608875d606fb69e80d1c247d3d`
passed native run 1063 and independent review 4917 **on its original tree**.
This newly assembled combined tree has **no** applicable both-default-target
build, complete transitive axiom audit or fresh exact-union review, and is
**not accepted, integrated or released**. It inherits neither old split checks
nor readiness acceptance; a changed or rejected prospective product parent
requires rework. No represented semidirect product, arbitrary-base scheme
change, dimension/smoothness or source-coverage decision is asserted.

Static renewal author: worker-b Hive Task
`hive-request-e99d1ea83bdaf0ed69b40e167a4e6b8bf8cec52f` (UID
`e8aa361b-0375-4638-b258-2168f3a2fb73`); the original mathematical,
transfer and review credits remain in the split-kernel guide and the complete
dated predecessor history below.

## Dated frozen-B README (complete release-readiness history, 2026-09-29)

The entire previous README follows unchanged. Its leading “current” product
and lifecycle labels describe the earlier frozen readiness document; they do
not approve this prospective union, settle B's pending review, or publish the
product. The earlier dated predecessor sections within B remain intact.

---

## Dated repaired-product README (complete D body, 2026-09-29)

The entire repaired-product README follows unchanged. Its 2026-09-29
snapshot and nested “current” preparation labels are historical; its full B
suffix is retained once, preserving every earlier attribution and correction.

---

# Algebraic groups: common zeros, diagonal products and upper-triangular groups

This snapshot provides source-independent finite diagonal-group-scheme products
alongside previously published common-zero, native and represented
upper-triangular, diagonal, and unitriangular results. The mathematical APIs
and hypotheses, not a changing publication status, determine its scope.

## Headline results in this snapshot

- **Finite categorical product of diagonal group schemes.** For every
  commutative ring `K` and same-universe finite decidable index `n`,
  `diagonalGroupScheme K n` is isomorphic to the literal product of copies of
  `Gₘ` in `Grp (Over (Spec (.of K)))`. Genuine Hopf projections and
  global-sections universality for arbitrary test schemes establish both
  projection triangles and empty-index terminality, including zero and
  nonreduced rings. See the [product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md),
  [producer](AlgebraicGroups/GroupScheme/DiagonalProduct.lean) and
  [ordinary-import client](AlgebraicGroupsTest/DiagonalProduct.lean).
- **Previously published native and represented upper-triangular results.**
  Native upper-triangular matrices split U-first over any commutative ring
  with finite linearly ordered index; the represented closed finite-type
  upper-triangular subgroup of GL and the native diagonal subgroup scheme
  have fixed-base natural native points. See the [native](AlgebraicGroups/GroupTheory/UpperTriangular/README.md),
  [represented](AlgebraicGroups/GroupScheme/UpperTriangular/README.md) and
  [diagonal](AlgebraicGroups/GroupScheme/Diagonal/README.md) guides.
- **Previously published common-zero and unitriangular results.** Under the
  hypotheses in their guides: [common zeros](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md),
  [derived series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
  and [exponents](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md).

**Evidence and limits (2026-09-29).** The unchanged product code integrated at
`ad5bff948f563bb9df49825f55dfcc8fcace8130` has original native run 1058's
matching-cache build and transitive standard-axiom evidence, independent
code review 4912, and separate maintainer code acceptance and integration.
Those are past code-level facts, not a new whole-document fingerprint or a
claim of review, required native success, owner acceptance or publication
for this repaired snapshot. No represented split-kernel or semidirect product,
smoothness/dimension theorem, arbitrary-base scheme change or source-specific
correspondence/coverage follows from the product result. Publication events
and decisions are tracked separately by the responsible maintainer.

## Dated preparation snapshot — 2026-09-29, before publication-status repair; all lifecycle statements below are historical

The complete preceding README follows unchanged. Every nested “current” label,
release-pending statement and then-current review/check status below describes
its dated preparation stage, not the present scope or publication status.

---

# Algebraic groups: common zeros, diagonal products and upper-triangular groups

## Headline results

- **Accepted finite product of diagonal group schemes (release pending).** For
  every commutative ring `K` and same-universe finite decidable index `n`,
  `diagonalGroupScheme K n` is isomorphic to the **literal categorical product**
  of copies of `Gₘ` in `Grp (Over (Spec (.of K)))`. Genuine Hopf projections
  and the global-sections universal property work for arbitrary test schemes;
  both projection triangles and empty-index terminality hold, including over
  zero and nonreduced rings. See the [product guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md),
  [producer](AlgebraicGroups/GroupScheme/DiagonalProduct.lean) and
  [ordinary-import client](AlgebraicGroupsTest/DiagonalProduct.lean).
- **Published native upper-triangular splitting.** For a finite linearly
  ordered index and any commutative ring, native upper-triangular matrices
  split U-first into their unitriangular kernel and diagonal units, naturally
  under coefficient ring maps. See the [native guide](AlgebraicGroups/GroupTheory/UpperTriangular/README.md).
- **Published represented upper-triangular group and diagonal scheme.** The
  closed finite-type upper-triangular subgroup scheme of GL has fixed-base
  natural native points; the native diagonal subgroup also has a closed
  finite-type group scheme with fixed-base natural points. See the
  [upper-triangular scheme guide](AlgebraicGroups/GroupScheme/UpperTriangular/README.md)
  and [diagonal scheme guide](AlgebraicGroups/GroupScheme/Diagonal/README.md).
- **Published common-zero and unitriangular results.** Over algebraically
  closed fields, a finite polynomial family with fewer equations than
  variables cannot isolate a unique common zero, with a nonzero common zero
  for positive-degree homogeneous families under that bound. Native finite
  unitriangular groups have sharp nilpotency-class, lower/derived-series and
  prime-power exponent results under the hypotheses in the
  [common-zero](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md),
  [derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
  and [exponent](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md) guides.

**Current lifecycle (2026-09-29).** The diagonal-product code at protected main
`ad5bff948f563bb9df49825f55dfcc8fcace8130` passed original native run 1058's
cache-first both-default-target build and complete private/generated-inclusive
standard-three axiom audit on its exact computational inputs. Fresh independent
destination review 4912 approved it; the maintainer separately accepted and
integrated the code. This four-document preparation changes whole-file digests,
not those checked Lean, dependency or checker inputs. The product is **not yet
released**: required native context for the prepared candidate, consolidated
independent final release review, owner release acceptance, protected release
stages and verified private GitHub publication remain separate and pending.
The native/represented upper-triangular predecessor is already published at
official `7ea3256fedfc2baeb1e36590c1293aafbaede682`; it is not the product
release. No represented split-kernel or semidirect product, dimension/smoothness,
arbitrary-base scheme change or source-specific correspondence/coverage is claimed.

## Dated predecessor README (complete pre-1058/pre-integration C history, 2026-09-29)

The complete earlier README follows unchanged. Its then-current unchecked,
unreviewed and unaccepted product labels are historical; the current lifecycle
and published predecessor results are stated above.

---

# Algebraic groups: common zeros and upper-triangular groups

## Headline results

- **Finite diagonal-group-scheme product — static unchecked candidate.** For
  every commutative ring `K` and same-universe finite decidable index `n`,
  `diagonalGroupScheme K n` is isomorphic to the **literal categorical product**
  of copies of `Gₘ` in `Grp (Over (Spec (.of K)))`. Genuine Hopf-algebra
  projections and a universal fan work for *arbitrary* test schemes, not only
  affine points. See the [producer](AlgebraicGroups/GroupScheme/DiagonalProduct.lean),
  [ordinary-import client](AlgebraicGroupsTest/DiagonalProduct.lean) and
  [guide](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md). This exact-R
  candidate has **no destination build, axiom audit, fresh review, acceptance,
  integration or product release**; the isolated donor's checks apply to its
  different graph. No source-specific Milne correspondence or coverage follows.
- **Published native and represented upper-triangular results.** The native
  upper-triangular group splits U-first over any commutative ring; the closed
  upper-triangular subgroup scheme of GL has fixed-base natural native points.
  Accepted AG main/release-prep R `14cd731a7a934709e28945ba1f22cedac59c3438`
  matches verified official Q `7ea3256fedfc2baeb1e36590c1293aafbaede682`
  in shipping tree. Its own native run 1031, independent reviews, acceptance
  and publication are **complete**, not outstanding product prerequisites.
  See the [native guide](AlgebraicGroups/GroupTheory/UpperTriangular/README.md)
  and [scheme guide](AlgebraicGroups/GroupScheme/UpperTriangular/README.md).

## Dated predecessor README (complete R history, 2026-09-29)

The entire released-R README below is preserved without alteration. Its then-
current headline excludes the finite product and its upper-triangular release
status says publication is pending; both statements are **historical** and do
not describe the current candidate or the subsequently verified publication.

---

# Algebraic groups: common zeros and upper-triangular groups

## Headline results

- **Native upper-triangular groups and their split diagonal.** For finite
  linearly ordered `ι` and any commutative ring `R`, the subgroup
  `Matrix.UpperTriangularGroup ι R` of native matrix GL projects onto its
  diagonal units. Its actual unitriangular kernel supplies the **U-first**
  multiplicative equivalence `U ⋊[diagonalAction] D ≃* T`, natural under all
  coefficient ring maps; the U coordinate normalizes columns, not rows. See
  the [native guide](AlgebraicGroups/GroupTheory/UpperTriangular/README.md)
  and [ordinary-import client](AlgebraicGroupsTest/UpperTriangular.lean).
- **Closed upper-triangular subgroup scheme.** The determinant-localized GL
  coordinate Hopf algebra modulo entries strictly below the diagonal gives
  a finite-type closed affine group subscheme of GL. Its group-valued points
  are naturally equivalent to native upper-triangular matrices over every
  commutative algebra at a fixed base. See the
  [scheme guide](AlgebraicGroups/GroupScheme/UpperTriangular/README.md),
  [coordinate producer](AlgebraicGroups/Algebra/UpperTriangularCoordinateRing.lean)
  and [ordinary-import client](AlgebraicGroupsTest/UpperTriangularScheme.lean).
- **Published finite-family common-zero bounds.** Over algebraically closed
  fields, fewer polynomial equations than variables cannot isolate a unique
  common zero; positive-degree homogeneous families under that bound have
  nonzero common zeros. See the
  [common-zero guide](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md).
- **Published diagonal and unitriangular results.** The native diagonal GL
  subgroup has a closed finite-type group scheme with fixed-base natural
  points; finite native unitriangular groups have sharp nilpotency-class,
  lower/derived-series and prime-power exponent results under their stated
  hypotheses. See the [diagonal](AlgebraicGroups/GroupScheme/Diagonal/README.md),
  [derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
  and [exponent](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
  guides for the exact statements and ordinary-import clients.

The two new upper-triangular APIs include empty indices, zero and nonreduced
rings and noninjective coefficient maps. Only the **native** group has the
diagonal/kernel/semidirect splitting here; no represented splitting, finite
product-of-`Gₘ` scheme equivalence or arbitrary-base scheme-change theorem is
claimed. The exact new code at protected main `8640f487fa1296f0ce34fb29fdf86f146fe6f1ba`
passed original native run 1031 (both default targets; all 158 modules and
4,037 private/generated-inclusive transitive standard-three origins), fresh
independent code review 4881, separate maintainer acceptance and integration
on 2026-09-29. This documentary release candidate retains those checked
computational inputs but changes the whole-shipping digest. **Final independent
release review, release acceptance, protected promotions and verified private
GitHub publication remain pending**; the preceding common-zero official release
is not replaced by a proposed candidate. No source coverage is inferred.

## Dated predecessor README (complete historical text)

The entire README preceding this assembly follows unchanged, including its
then-current common-zero headline and dated pending-release statements. Those
statements describe their earlier checkpoints, before the separately verified
common-zero publication; they are not a claim that this new candidate passed
the predecessor's checks.

---

# Algebraic groups: common zeros, diagonal schemes and native exponent bounds

## Headline results

This source-independent library provides three finite-family common-zero
results for multivariate polynomials over algebraically closed fields. A unique
common zero requires at least as many equations as variables; fewer equations
give a second zero beside any known one. With positive-degree homogeneous
equations, a nonzero common zero exists under the same strict bound, even for
mixed degree labels and zero equations. Import the producer
`AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero` or the aggregate
`AlgebraicGroups`; see its [guide](AlgebraicGroups/Algebra/AlgebraicallyClosedCommonZero/README.md)
and [ordinary-import client](AlgebraicGroupsTest/AlgebraicallyClosedCommonZero.lean).
The existing point-height helper is reused, not copied or reproved.

The following predecessor results are already published and remain available:

- **Finite diagonal subgroups and their closed group schemes.** For a finite
  decidable index type and a commutative base ring, the diagonal subgroup of
  native matrix GL over each commutative test algebra is multiplicatively
  equivalent to tuples of units. Its off-diagonal Hopf quotient represents a
  finite-type affine group scheme with closed inclusion in GL and a fixed-base
  natural point equivalence. Empty indices, zero rings and nonreduced algebras
  are included. This is not a finite-product multiplicative-group scheme
  isomorphism or a smoothness, dimension or arbitrary-base-change theorem.
  See the [producer](AlgebraicGroups/GroupScheme/Diagonal.lean),
  [guide](AlgebraicGroups/GroupScheme/Diagonal/README.md) and
  [ordinary-import client](AlgebraicGroupsTest/Diagonal.lean).
- **Sharp prime-power bounds for unitriangular point groups.** Over a
  commutative ring `R`, if `p` is prime, `(p : R) = 0` and `n ≤ p ^ t`,
  every `g : Matrix.UnitriangularGroup (Fin n) R` satisfies
  `g ^ (p ^ t) = 1`, including empty indices and the zero ring. If `R` is
  also nontrivial, both that uniform-power assertion and the assertion that
  the group exponent divides `p ^ t` hold exactly when `n ≤ p ^ t`. These are point-group
  bounds, not a group-scheme exponent or a claim that every element has maximal
  order. The same API proves nilpotence of strictly upper-triangular matrices
  over any commutative ring on a finite linearly ordered index type.
  See the [producer](AlgebraicGroups/GroupTheory/UnitriangularExponent.lean),
  [guide](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md) and
  [ordinary-import client](AlgebraicGroupsTest/UnitriangularExponent.lean).

For the already shipped series and underlying-scheme results, see the
[derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
and [geometry](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md) guides.

## Common-zero release readiness (2026-09-29, after code integration)

The common-zero producer, guide and ordinary-import client are implemented on
accepted, protected-integrated main `021cbd4ed92bc55704f401533846731a73079a8f`
(tree `0e9dcaf625161287c6423a76808a2ee741da195c`). Fresh independent
final-revision review 4851 approved this exact code/documentary candidate;
earlier reviews 4837 and 4843 requested documentary corrections and are not
approvals of later revisions. Original native run 993 established a matching-
cache both-default-target build and complete private/generated-inclusive
standard-three axiom audit on the same computational graph. The subsequent
exact-head native run 1004 (job 1005) and required Lean CI context succeeded;
only documentary files changed between the original checked graph and the
accepted candidate, not Lean, dependencies, build roots or checker inputs.
This is code acceptance, **not** this contribution's separate release acceptance
or verified official publication. As of this dated snapshot those release
steps and source-specific correspondence/coverage remain open. The previously
published diagonal P11 and exponent P10 are distinct predecessor releases.

## Dated common-zero transfer status (2026-09-29, before destination review)

The following is the original transfer's pre-review status, retained as history.
Later exact-revision review, computation, acceptance and publication decisions
are recorded separately; this snapshot does not assert that they have occurred.

**Original contribution status (2026-09-29).** This common-zero transfer is a
candidate on accepted main I11 `e794bded47a4e36f830edc163f7b62892314f4cf`
(tree `5cd4fbd40aea2297eaef40c75354896d107686d1`). The predecessor's
native finite diagonal GL subgroup, closed group scheme and natural point
equivalence are separately reviewed, accepted and **officially published** at
verified private P11 `56c759fc12152a447e36249ee50218ce473d93ca`,
with the same tree as I11. The unitriangular exponent predecessor was already
officially published at P10 `34c5772fb8f00ca6012c0683091a0f93116ea618`.
The common-zero proofs and nine-check client were reviewed and accepted only
in isolated development. Their original scoped cache-first build and complete
standard-three axiom audit do not certify this new destination graph. A new
both-default-target build and private/generated-inclusive transitive axiom
audit, fresh independent destination review, responsible-maintainer acceptance,
integration and separately reviewed verified official publication remain open.
This candidate has 179 leaves, 153 Lean files, 98 aggregate imports, 41
ordinary test roots, 90 selected results and the same 13 resolved packages.
The original common-zero code is by Formal Frontier Agents (worker-a); the
unchanged helper, static I10 packaging and this I11 transfer are credited to
distinct Formal Frontier Agents (worker-b) executions. Original proofs and
helper have separate independent reviews; this transfer has none yet. No
source coverage or redistribution clearance is inferred. See
[docs/BUILDING.md](docs/BUILDING.md) for reproducible commands and evidence
boundaries.

## Dated pre-P11 diagonal release-preparation snapshot (historical)

The following complete diagonal/exponent mathematics and dated history is
retained. Its diagonal-own-release-pending labels describe a state before the
verified P11 publication above, not the current status of that predecessor.

### Algebraic groups: native diagonal, exponent and group-scheme APIs

This source-independent library provides a native finite diagonal subgroup of
matrix GL, equivalence with tuples of units, an actual off-diagonal Hopf
quotient, a finite-type affine group scheme with closed GL inclusion, and a
fixed-base group-valued natural point equivalence over all commutative
algebras. Its index type may be empty; zero and nonreduced rings are covered.
Import `AlgebraicGroups.GroupScheme.Diagonal` or the public aggregate
`AlgebraicGroups`; the ordinary-import client is `AlgebraicGroupsTest.Diagonal`.
See the [diagonal API guide](AlgebraicGroups/GroupScheme/Diagonal/README.md)
for hypotheses, declarations, tests and limitations.

**Accepted development code; own release pending (2026-09-29).** The diagonal
contribution is independently reviewed, accepted and protected-integrated at
main `a41c1bc85ed06b0901ab50e86ccc438caff3adf9` (tree
`93646af0eb43065216ef70178946effebcc0830d`), the sole child of
accepted exponent release-preparation I10
`fe7a86c8ab5484ea60d4baaf0e5deae7cf12986e`. Original native job 972
fetched the matching mathlib cache, built both default targets (3,878 jobs)
and audited 3,788 module-origin pairs across all 151 Lean modules (111
production, 40 tests), including 1,185 private-named origins and all generated
origins; only `propext`, `Classical.choice` and `Quot.sound` occurred. Fresh
author-distinct destination review and separate maintainer code acceptance
followed. All 176 shipping leaves include 97 aggregate imports, 40 test roots,
87 selected results and the same 13 resolved packages. This documentation-only
release preparation retains those checked Lean/build/pin/checker inputs, not
the original whole-shipping digest. The exponent's own official private P10
`34c5772fb8f00ca6012c0683091a0f93116ea618` is verified and remains
official until the diagonal successor is separately reviewed, accepted,
protected-promoted and verified published. No diagonal release or source-coverage
decision is claimed. See [docs/BUILDING.md](docs/BUILDING.md) for reproduction.

### Headline results in the dated snapshot

- **Native finite diagonal subgroup and closed group scheme (accepted code;
  release pending).** For any finite decidable index type `ι` and commutative
  base ring `K`, the literal diagonal subgroup of native
  `Matrix.GeneralLinearGroup ι R` over each commutative `K`-algebra `R` is
  multiplicatively equivalent to `ι → Rˣ`. Its off-diagonal Hopf quotient
  gives a finite-type affine group scheme with closed inclusion in GL, whose
  group of points is naturally that diagonal subgroup for **all** test algebras
  at fixed base. Empty indices, zero rings and nonreduced test algebras are
  included; invertibility requires a unit determinant, not merely a nonzero
  one. See the [producer](AlgebraicGroups/GroupScheme/Diagonal.lean),
  [guide](AlgebraicGroups/GroupScheme/Diagonal/README.md) and
  [ordinary-import client](AlgebraicGroupsTest/Diagonal.lean). The unit-tuple
  equivalence is not a finite-product G_m/Laurent **scheme** isomorphism;
  triangular/semidirect schemes, smoothness, dimension, arbitrary base change
  and source-specific coverage remain outside this result. The exact
  development code is built, audited, independently reviewed, accepted and
  integrated; final release review, release acceptance, protected promotions
  and verified private publication remain pending.
- **Prime-power exponent bounds and sharpness for native unitriangular groups.**
  For `n, p, t : ℕ` and `[CommRing R]`, if `Nat.Prime p`, `(p : R) = 0`
  and `n ≤ p ^ t`, every `g : Matrix.UnitriangularGroup (Fin n) R`
  satisfies `g ^ (p ^ t) = 1`, including at `n = 0` and over the zero
  ring. With `[Nontrivial R]` as well, both the uniform-power assertion
  and `Monoid.exponent (Matrix.UnitriangularGroup (Fin n) R) ∣ p ^ t`
  hold **if and only if** `n ≤ p ^ t`. Over any nontrivial commutative
  ring, `0 < q < n` yields a characteristic-independent witness `g` with
  `g ^ q ≠ 1`. These are native point-group results, not claims that
  every element has maximal order, a separate numerical formula for the
  group exponent, or a group-scheme exponent. See the
  [producer](AlgebraicGroups/GroupTheory/UnitriangularExponent.lean) for
  `Matrix.UnitriangularGroup.pow_prime_pow_eq_one`,
  `Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff`,
  `Matrix.UnitriangularGroup.exponent_dvd_prime_pow_iff` and
  `Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt`, with the
  [exponent guide](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
  and [ordinary-import client](AlgebraicGroupsTest/UnitriangularExponent.lean).
- **Finite-index triangular nilpotence.** For a finite linearly ordered
  index type `ι` over `[CommRing R]`, any upper-triangular matrix `N`
  with zero diagonal satisfies `N ^ Fintype.card ι = 0`, even when `ι`
  is empty or `R` is the zero ring. See
  `Matrix.pow_card_eq_zero_of_upperTriangular_diag_zero` in the same
  [producer](AlgebraicGroups/GroupTheory/UnitriangularExponent.lean).

For the already shipped series and underlying-scheme results, see the
[derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
and [geometry](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md) guides.

## Dated pre-P10 exponent and pre-diagonal-acceptance snapshot (historical)

The complete earlier snapshot follows for attribution and status provenance.
Its exponent-release-pending and diagonal-candidate/unverified statements are
superseded by verified exponent P10 and accepted, native-checked diagonal main
above; its mathematical exponent headline remains valid. Earlier dated
snapshots within it refer only to their own recorded inputs and times.

### Dated pre-native972 diagonal packaging status

**Static diagonal candidate (2026-09-29).** This branch is the sole child of
accepted, integrated exponent release-preparation I10
`fe7a86c8ab5484ea60d4baaf0e5deae7cf12986e` (tree
`8f6957f508f70e9042704eb2d1e9f5c6921feb99`). The exponent contribution
has its own completed review, acceptance, integration and verified private
official P10 `34c5772fb8f00ca6012c0683091a0f93116ea618`. This candidate
preserves its complete producer/client, current headline, import, test root and
five selected results, adding only diagonal packaging. The 176-leaf project
has 151 Lean files (111 production including aggregate, 40 tests), 97 aggregate
imports, 40 test roots, 87 selected results and the same 13 resolved packages.
**No combined-graph build, transitive axiom audit, independent destination
review, diagonal code acceptance, integration, diagonal release or source-
coverage decision applies to this candidate.** The original diagonal donor's
checks and exponent's applicable I10 evidence apply only to their own exact
graphs, not this diagonal union. The responsible maintainer arranges fresh
cache-first destination checks, independent review, separate acceptance and
its own official release. A finite-product G_m/Laurent scheme equivalence,
triangular/semidirect scheme, smoothness, dimension and arbitrary base-change
are not claimed. Build prerequisites and commands are in
[docs/BUILDING.md](docs/BUILDING.md).

## Existing exponent headline and publication history (2026-09-29)

The existing exponent mathematics and current headline remain in force below.
The previous integration-status prose and older release-pending snapshots are
dated history superseded by the completed P10 release; none describes the new
diagonal candidate. All inherited I10 text is retained unchanged.

### Algebraic groups: native exponents, series and group-scheme APIs (historical)

The reusable native matrix point-group library now includes a **reviewed,
accepted and integrated**
prime-power exponent API for `Matrix.UnitriangularGroup (Fin n) R` alongside its
released generation and derived-series results. With prime `p`, `(p : R) = 0`
and `n ≤ p ^ t`, every native element satisfies `g ^ (p ^ t) = 1`. Over a
nontrivial commutative ring, the converse holds for the uniform assertion and
for divisibility of the group exponent; a characteristic-independent witness
shows `g ^ q ≠ 1` for some `g` when `0 < q < n`. The generic matrix theorem
also gives `N ^ Fintype.card ι = 0` for strictly upper-triangular `N`, even on
empty indices. See the
[exponent guide](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md),
focused `AlgebraicGroups.GroupTheory.UnitriangularExponent` import and
`AlgebraicGroupsTest.UnitriangularExponent` ordinary-import client.

**Current integration status (2026-09-29).** Accepted development main
`45d4c5ddfcd491f298c4c968561d2e2eccf82e06` includes the exponent
transfer. Its original native job 932 fetched the matching mathlib cache,
built both default targets (3,873 jobs) and audited all 3,700 module-origin
pairs across 147 **total** Lean modules (108 production, 39 tests), including
1,181 private-named and all generated origins; only `propext`,
`Classical.choice` and `Quot.sound` occurred, with zero rejects. Fresh
author-distinct worker-b destination review and Lattice's separate code
acceptance/protected integration are complete. This contribution's own
independent release review, acceptance, protected promotions and verified
private GitHub publication are **pending**. I9
`771a5ab485be5aaa0f5f2c553f8b7b2cc3766605` and verified official P9
`8fdf180d3b56c6bfb4a5fe8c63204ad9a7abf827` already publish the preceding
generation/derived contribution, **not** the new exponent transfer. The
transfer preserves the separately reviewed and maintainer-accepted isolated
donor's proof bytes and clients. Donor checks and old native runs 895/912
cover their original inputs, not the 147-module graph audited by job 932.
The destination pins remain Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and official
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`.
The original exponent proofs and client are by Formal Frontier Agents,
worker-a Task `hive-request-6697261957705b5abcfeb5a713d5eccb32862d84`
(UID `e8368f27-f82b-4b70-bace-14dcd33d9ac2`), independently reviewed
in isolation by worker-b Task `hive-request-385475f9c731526890b911886a758b3b8b1795ac`
(UID `e7141ac7-cc41-4165-9cdd-339d5b685836`); this static transfer is
by worker-a Task `hive-request-2d88e4cc16946512f4d88a8bb09e16456c4ff5c1`
(UID `2ec7daea-21c2-47e7-b328-a24a4956ab4e`). This is source-independent
mathematics, not a group-scheme theorem or a source-coverage claim. Fresh
destination review is by worker-b Task
`hive-request-cca37fd56496938e743a795f5e0c4437da7e1a46` (UID
`449865e3-164c-48fa-9984-3f66c772f898`); this documentary release
preparation is by worker-a Task
`hive-request-bba7de9a57c7bb5762f49449e85c53ea5bd9e370` (UID
`a61157f1-2a86-4729-a099-c70066ae2502`). Neither is the independent
review or acceptance of this proposed release.

### Headline results in the historical pre-acceptance snapshot

- **Native finite diagonal subgroup and closed group scheme (candidate).**
  For any finite decidable index type `ι` and commutative base ring `K`, the
  literal diagonal subgroup of native `Matrix.GeneralLinearGroup ι R` over
  each commutative `K`-algebra `R` is multiplicatively equivalent to `ι → Rˣ`.
  Its off-diagonal Hopf quotient gives a finite-type affine group scheme with
  closed inclusion in GL, whose group of points is naturally that diagonal
  subgroup for **all** test algebras at fixed base. Empty indices, zero rings
  and nonreduced test algebras are included; invertibility requires a unit
  determinant, not merely a nonzero one. See the
  [producer](AlgebraicGroups/GroupScheme/Diagonal.lean),
  [guide](AlgebraicGroups/GroupScheme/Diagonal/README.md) and
  [ordinary-import client](AlgebraicGroupsTest/Diagonal.lean). The unit-tuple
  equivalence is not a finite-product G_m/Laurent **scheme** isomorphism;
  triangular/semidirect schemes, smoothness, dimension, arbitrary base change
  and source-specific coverage remain outside this candidate. Destination
  verification, review, acceptance and official release remain pending.
- **Prime-power exponent bounds and sharpness for native unitriangular groups.**
  For `n, p, t : ℕ` and `[CommRing R]`, if `Nat.Prime p`, `(p : R) = 0`
  and `n ≤ p ^ t`, every `g : Matrix.UnitriangularGroup (Fin n) R`
  satisfies `g ^ (p ^ t) = 1`, including at `n = 0` and over the zero
  ring. With `[Nontrivial R]` as well, both the uniform-power assertion
  and `Monoid.exponent (Matrix.UnitriangularGroup (Fin n) R) ∣ p ^ t`
  hold **if and only if** `n ≤ p ^ t`. Over any nontrivial commutative
  ring, `0 < q < n` yields a characteristic-independent witness `g` with
  `g ^ q ≠ 1`. These are native point-group results, not claims that
  every element has maximal order, a separate numerical formula for the
  group exponent, or a group-scheme exponent. See the
  [producer](AlgebraicGroups/GroupTheory/UnitriangularExponent.lean) for
  `Matrix.UnitriangularGroup.pow_prime_pow_eq_one`,
  `Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff`,
  `Matrix.UnitriangularGroup.exponent_dvd_prime_pow_iff` and
  `Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt`, with the
  [exponent guide](AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md)
  and [ordinary-import client](AlgebraicGroupsTest/UnitriangularExponent.lean).
- **Finite-index triangular nilpotence.** For a finite linearly ordered
  index type `ι` over `[CommRing R]`, any upper-triangular matrix `N`
  with zero diagonal satisfies `N ^ Fintype.card ι = 0`, even when `ι`
  is empty or `R` is the zero ring. See
  `Matrix.pow_card_eq_zero_of_upperTriangular_diag_zero` in the same
  [producer](AlgebraicGroups/GroupTheory/UnitriangularExponent.lean).

For the already shipped series and underlying-scheme results, see the
[derived-series](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
and [geometry](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md) guides.

## Dated 2026-09-28 pre-P9 README snapshot (historical)

The preserved snapshot below describes the generation/derived contribution
before its own I9/P9 release; its “pending” wording is dated history and does
not override the current 2026-09-29 status above.

### Algebraic groups: native series and group-scheme APIs

Reusable source-independent Lean results for algebraic groups, group schemes
and native matrix point groups, licensed under [Apache-2.0](LICENSE). The library
includes the **exact nilpotency class** of native finite unitriangular point
groups alongside their central filtration, successive quotients and underlying
scheme geometry. Sharpness was published at verified official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8`. The separately
reviewed all-stage native lower-central result is now also published at
verified official P8 `441817ab159b20bb7c9c855b05d49abfa3d85c92`
(accepted internal I8 `164f0310a4f641cc1d698a14b333082bbfcfe474`).
Development main `a77d4e4d19f6dc366eb9a40f16503f5855421cf3` additionally
integrates positive-stage elementary generation, exact commutators and the
native derived series. Original native run 895 built both default targets and
completed the private/generated-inclusive transitive standard-three axiom
audit on this 145-module destination graph. Fresh independent destination
review and maintainer code acceptance/protected integration are complete.
Its **own release review, acceptance and verified publication are pending**;
official P8 does not contain these additions. Isolated donor checks and the
old L release were not substituted for run 895. Dependencies retain
their own authors, licenses and mathematical contributions. Source interpretation
and coverage remain separate from library acceptance.

## Headline results

- **Unitriangular groups as affine schemes.** For a finite ordered index type
  over an arbitrary commutative base ring, strict-upper coordinates identify
  the underlying unitriangular group scheme with affine space over the base.
  Its polynomial coordinate algebra gives relative smoothness and geometric
  integrality; over a domain the total scheme is integral, and over a field
  its dimension is the number of strict-upper positions. This is an isomorphism
  of underlying schemes over the base, not an additive group-scheme
  isomorphism. See the [geometry guide](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md).
- **Central filtration and successive point-group quotients.** For all
  `n : ℕ`, `R : Type`, `[CommRing R]`, the normal superdiagonal stages satisfy
  `F₀ = F₁ = ⊤`, `Fₙ = ⊥` and the mixed commutator bound
  `⁅Fᵣ, Fₛ⁆ ≤ Fᵣ₊ₛ`. This yields a nilpotent group with class at most `n - 1`,
  without assuming a nonzero ring. For `1 ≤ r`, the actual quotient of `Fᵣ`
  by `Fᵣ₊₁` viewed as a subgroup of `Fᵣ` is the additive group of its
  r-th-superdiagonal coordinates, naturally under unital coefficient-ring maps.
  This is a whole-stage point-group quotient, not a scheme quotient or a
  homomorphic splitting. See the [filtration](AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
  and [quotient](AlgebraicGroups/GroupTheory/UnitriangularSuperdiagonalQuotients/README.md) guides.
- **Sharp nilpotency class.** Over a nontrivial commutative ring, the native
  unitriangular group on `Fin n` has class exactly `n - 1`; over a subsingleton
  ring it has class zero. Native elementary units and their ordered commutator
  provide the lower bound, using the elementary commutator supplied by the
  separately maintained general-linear-groups dependency. The statement includes
  dimensions zero and one and imposes no field, domain or reducedness assumption.
- **Actual lower central series (accepted native point-group result).** For
  all `n,t : ℕ`, `R : Type` and `[CommRing R]`, the native series
  `γ_t = (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries t`
  equals the superdiagonal stage `F_(t+1)` in every dimension and at every
  stage, including the zero ring. Elementary-root membership is available
  both in the actual series and the filtration. This is a point-group equality,
  not a group-scheme quotient or an unconditional sharp-class statement. See
  the [lower-central-series guide](AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md).
- **Generation and derived series (accepted on development main).** A positive
  stage `F_d` lies in any subgroup containing every elementary root at distance
  at least `d`, without normality or ring nontriviality. For positive `r,s`,
  `⁅F_r,F_s⁆ = F_(r+s)`, and the native derived series is `F_(2^t)` for every
  `t`, over all commutative rings. Over nontrivial rings, `F_d = ⊥ ↔ n ≤ d`
  for positive `d`, and the derived series stops at `t` exactly when
  `n ≤ 2^t`. See the [derived-series guide](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md).

### Using the exact-class API

For `n : ℕ`, `R : Type`, `[CommRing R] [Nontrivial R]`, the library's
`Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial n R` identifies
the class with `n - 1`, including dimensions zero and one. Under
`[Subsingleton R]`, `nilpotencyClass_eq_zero_of_subsingleton n R` instead
gives class zero for all dimensions. `elementary` constructs native units
without inverting their coefficients; `elementary_gl` and `elementary_coe`
describe their images, and `elementary_commutator` gives the ordered
`x*y*x⁻¹*y⁻¹` relation with product coefficient `a*b`. These six public
declarations have a [focused guide](AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md)
and an ordinary-import regression client. They use the already-published
central-filtration upper bound and the *direct*, exact official
`general-linear-groups` dependency at `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`
for its elementary commutator; the project still pins mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and scheme-properties at
`6b204a3e49f022e51d78a9f93e77513b99a87e00`.

```lean
import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass

example (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 4) R) = 3 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial 4 R
```

The proofs and original client were authored in the incubator by Formal
Frontier Agents, with separate independent origin review. This transfer
retains their proofs and credits; the general-linear-groups library retains
its own authorship, mathematical contribution and license. Neither origin
review nor the earlier published 139-module graph's checks alone verify the
changed graph. The sharpness module alone does not identify all lower-central
stages; the new module below does. Neither asserts a subgroup-scheme quotient
or an unconditional nontrivial class.

### Using the new lower-central-series API

The accepted theorem
`Matrix.UnitriangularGroup.lowerCentralSeries_eq_superdiagonalSubgroup n R t`
identifies `γ_t = F_(t+1)` for every `n,t : ℕ`, `R : Type` and `[CommRing R]`,
with no nontriviality, field or dimension restriction. Its two elementary
membership theorems precede the equality in the
[focused guide](AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md).

```lean
import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries

example (R : Type) [CommRing R] :
    (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin 4) R)).lowerCentralSeries 1 =
      Matrix.UnitriangularGroup.superdiagonalSubgroup 4 R 2 :=
  Matrix.UnitriangularGroup.lowerCentralSeries_eq_superdiagonalSubgroup 4 R 1
```

The isolated incubator proof and ordinary-import client were reviewed and
accepted on their original inputs. Their producer's two public imports and
the client's ordinary import/namespace are retargeted without proof changes.
The actual 143-module, 37-test-root, 13-package destination passed both default
targets and a complete transitive standard-three audit including private and
generated declarations in original native job 865. Fresh independent review
and Lattice's acceptance cover the exact destination code. Isolated donor
evidence and the earlier 141-module sharpness checks alone did not certify it;
separate L release review, acceptance and publication were still pending
at this historical L-only readiness checkpoint; I8/P8 subsequently completed them.

### Using the generation and derived-series APIs

`Matrix.UnitriangularGroup.superdiagonalSubgroup_le_of_elementary_mem` handles
an arbitrary subgroup and **all** roots at distance at least a positive stage;
the derived-series module uses it rather than duplicating the elimination.
Import `AlgebraicGroups.GroupTheory.UnitriangularDerivedSeries` for the native
positive-stage commutator equality, all-stage derived-series equality and
the two `[Nontrivial R]` stopping criteria. The positive-stage hypotheses
and weak bounds `n ≤ d`, `n ≤ 2^t` cannot be omitted. The ordinary-import
clients include dimension zero/one, zero-ring and a genuine zero-index
commutator counterexample. The [lower-central guide](AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md)
and [derived guide](AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md)
document their independent hypotheses and imports. The accepted destination
has 145 **total** Lean files (107 production including the aggregate,
38 tests), 38 explicit test roots and the unchanged 13 whole packages;
original native run 895 checked this actual graph, not an estimated one.

### Verification and release context (2026-09-28)

Old L passed original native job 865 and later native job 885 on the unchanged
143-total-Lean/37-test/13-package I8 inputs, followed by separate reviewed
main, internal and official P8 publication. The generation/derived union
changed its producer, client, aggregate import and test roots. Original native
run 895 on exact accepted main `a77d4e4d19f6dc366eb9a40f16503f5855421cf3`
fetched the matching official cache, built both default targets (3,871 jobs)
and audited all 3,679 module-origin pairs (3,661 distinct names) across 145
total Lean modules, including 1,168 private-named and all generated origins.
Only `propext`, `Classical.choice` and `Quot.sound` occurred; zero origins were
rejected. Its current lower-central producer/client contributed 37/24 origins,
and the new derived producer/client 13/20. Fresh author-distinct destination
review and Lattice's acceptance/protected integration cover this exact commit;
this documentary successor preserves its Lean, build, dependency and checker
inputs but changes the whole-shipping-file digest. Separate fresh release
review, maintainer acceptance, protected promotion and verified private GitHub
publication remain pending. Old jobs 865/885 and isolated donor checks 61/33
apply only to their own inputs, not this native 145-module graph.
The original plan `903d2bb62568b92bafdb0d2bf0523499c952f0ef`
miscounted 143 old files as production; the dated correction is 143 total →
145 total (107 production/38 tests) on accepted main.
The unchanged plan and all dated predecessor evidence remain retained.

#### Dated pre-P8 L release-readiness snapshot

The transferred sharpness contribution passed independent destination review
and native job 843 on `172234b1ae20be037a781f0a105ae88dfbe3e856`, then
was accepted and integrated. That run checked both default targets, all 141
local Lean modules and 36 regression roots with the complete 13-package graph.
Its transitive audit covered 3585 module-origin declarations, including 1082
private-named origins and generated declarations, with only `propext`,
`Classical.choice` and `Quot.sound`. The documentation-only I7 preparation
kept those computational inputs unchanged; official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8` publishes that reviewed
sharpness result. The subsequent L addition changed the graph: original native
job 865 on accepted main `d3c455d9adac06b5a873828ea7de57d5501c42f4`
fetched the matching cache, built both default targets (3,869 jobs), and
audited 3,634 module-origin declarations across all 143 Lean modules and 37
registered test roots, including 1,128 private-named origins and all generated
origins. The 3,616 distinct name strings must not replace the 3,634 audited
module-origin pairs. Only `propext`, `Classical.choice` and `Quot.sound` occurred;
no origin was rejected. Fresh independent destination review and maintainer
code acceptance/protected main integration are complete. This documentation-only
preparation preserves the checked Lean, build, dependency and checker inputs,
not the prior whole-165-file digest. L's separate release review, acceptance,
protected promotion and exact private GitHub publication are still pending.
See [build guidance](docs/BUILDING.md) for reproduction and evidence scope.

Geometry and filtration/quotient APIs were already published in official
release `38b7ebdcb38bd0d1b3c9a72e266162718f4647c2`; that earlier release does
not contain sharpness, whereas P7 does. Neither release contains L.
Use `lake exe cache get` successfully before any build with the pinned
Lean `v4.34.0-rc2` toolchain, then `LAKE_JOBS=2 lake build` for both defaults.

---

## Dated history: complete I6 README (2026-09-28)

Everything from the original title onward is retained verbatim as a historical
snapshot. In particular, its G/Q-publication-pending prose describes I6
preparation, not the present status after official release P6.

# Algebraic groups and unitriangular point-group quotients

Reusable Lean APIs for algebraic groups, group schemes and their matrix points.
Original project contributions are licensed under [Apache-2.0](LICENSE).
The library is independent of any particular book; source interpretation and
coverage are separate from library acceptance. Dependencies retain their own
authors, licenses and mathematical contributions.

**Release preparation, 2026-09-28.** The upper-unitriangular coordinate, group-scheme
and affine-geometry results are already in the official geometry-bearing release
`183bbbcebf0693df849ad6f5781df4c97d33364f`. This branch additionally transfers
the central filtration and successive quotients of native unitriangular point
groups. Those additions passed fresh independent destination review, native
cache-first builds and the complete standard-axiom audit, and were accepted and
integrated at `535d623443808796af231ed5761f837c13934cdd`. This documentation-only
release preparation does not change checked Lean or dependency inputs. Separate
independent release acceptance and verified publication are still pending; the
geometry-bearing release named above does not contain these additions.
The historical README preserved below predates this transfer;
its former geometry-publication-pending wording is no longer current.

## Headline results

- **Unitriangular groups as affine schemes.** For a finite ordered matrix index
  type over an arbitrary commutative base ring, the strict-upper coordinates
  identify the underlying upper-unitriangular group scheme with affine space
  over the base. The coordinate ring is a polynomial algebra; the construction
  includes a closed inclusion into the general-linear group and a multiplicative
  natural equivalence with native unitriangular matrix points. The geometry API
  gives relative smoothness and geometric integrality, absolute integrality over
  domain bases, and ring/scheme dimensions over fields. Empty indices and the
  zero ring are allowed where the stated hypotheses permit them. The affine-space
  isomorphism is not an additive group-scheme isomorphism. See the
  [unitriangular module](AlgebraicGroups/GroupScheme/Unitriangular.lean) and
  [geometry guide](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md).
- **A central filtration and nilpotence of matrix point groups.** For every
  natural `n` and commutative ring `R : Type`, let `F_r` consist of the native
  unitriangular matrices whose difference from the identity vanishes below the
  `r`-th superdiagonal. The new
  [central-filtration API](AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
  proves normality, `F_0 = F_1 = top`, `F_n = bot` and
  `[F_r, F_s] <= F_(r+s)`. It supplies a descending central series, a native
  nilpotent-group instance and the upper bound `nilpotencyClass <= n-1`.
  No field, nonzero-ring, characteristic or reducedness assumption is needed.
  This is an upper bound, not an exact-class theorem or a subgroup-scheme
  filtration.
- **Successive quotients are additive coordinate groups.** For `1 <= r`, the
  new [quotient API](AlgebraicGroups/GroupTheory/UnitriangularSuperdiagonalQuotients/README.md)
  identifies the actual quotient of `F_r` by `(F_(r+1)).subgroupOf F_r` with
  the additive group of functions on the `r`-th superdiagonal positions. Every
  coordinate family has a lift, but no homomorphic section is asserted.
  Arbitrary unital coefficient-ring maps preserve the stages and commute with
  this equivalence on every quotient element; they need not be injective or
  surjective. Empty dimensions/superdiagonals and zero or nonreduced rings are
  included. The equivalence excludes `r=0` and is not a group-scheme or additive
  group-scheme quotient.

These are implemented, destination-accepted statements, with the new point-group
transfer still subject to its separate release gates above. They use mathlib's matrix,
subgroup, nilpotent-group and quotient interfaces together with this repository's
native unitriangular provider; no dependency supplies the two new point-group
modules. The remaining general-linear, special-linear, group-object, component,
quotient-sheaf and supporting algebra/scheme APIs are documented in the preserved
mathematical sections below. No exact nilpotency class, torus or Lie theory,
general quotient effectivity, or complete source coverage is claimed here.

## Using the new point-group APIs

```lean
import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients

example (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) R) ≤ 2 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 3 R
```

Both modules are also publicly imported by `AlgebraicGroups`. Their standalone
guides give precise declarations, quotient representatives and coefficient-map
examples. The existing native matrix provider ties index and coefficient
universes, hence `R : Type` here rather than an asserted unrestricted `Type*`.

This candidate has 139 project Lean modules and 35 persistent regression roots.
The two added clients retain ordinary imports and examples for `Fin 0/1`, empty
superdiagonals, `ZMod 1/2/4` and general coefficient maps. All twelve resolved
packages, toolchain, default targets and prior regression roots remain unchanged.
For the pinned environment, fetch the matching mathlib cache before building:

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

Native job 811 successfully fetched and verified the matching mathlib cache,
built both default targets (3,480 jobs), and audited all 139 project modules:
3,542 actual-origin declarations, including 1,048 private-named origins and all
generated origins, with complete transitive inspection allowing only `propext`,
`Classical.choice` and `Quot.sound`. No disallowed axiom was found. This is the
destination pass, not a substitution of isolated or predecessor evidence.
Fresh independent destination review and maintainer acceptance/protected
integration are complete. A separate reviewed official release and verified
publication follow; no local incubator implementation is removed beforehand.

Separate Worker A executions authored the original filtration and quotient Lean
modules and clients; distinct Worker B executions independently reviewed each
isolated implementation. Mathematical exposition authors and reviewers were
separate contributions. Another Worker A execution prepared the destination
import/client-namespace transfer and standalone guides without changing proofs;
Lattice assembled this bounded README update. Exact contribution and evidence
records remain with the responsible maintainer. None of these agent roles claims
human review or source-author endorsement. A fresh Worker B execution supplied
the exact destination review; Lattice accepted and integrated the contribution
and prepared these lifecycle-only updates. Release decisions remain separate.

## Dated history: complete preceding geometry-release README

The entire preceding README follows unchanged, preserving its mathematics,
contributor credit and dated verification history. Its module/root counts and
pending-publication statements describe that earlier snapshot, not the current
candidate or the already published geometry release identified above.

# algebraic-groups

Reusable Lean formalization for algebraic groups and group schemes.

Authors: Formal Frontier Agents

Original project contributions are licensed under [Apache-2.0](LICENSE).
This is AI-assisted formalization under human project direction; independent
agent development review is not human mathematical review or source-author
endorsement. Contributor roles and mathematical references are recorded below.

The repository is organized around reusable mathematics rather than any one
source. Source-specific interpretation, provenance, and coverage remain in the
corresponding source-metadata repositories.

## Scope and prerequisites

The results below describe the library's mathematical scope, with explicit
hypotheses and exclusions. They do not assert complete formalization of a book
or a general quotient-effectivity theorem. All 135 checked-in Lean files declare
the module system, and all 33 regression files are persistent default-build
roots. Release verification requires applicable pinned-graph module builds,
the actual no-target default build and a complete transitive
axiom audit, including private declarations, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Build success and metadata schema validity
alone do not establish independent release acceptance or publication.
The predecessor main snapshot `aa9e9326ac1673549825f0defaf32714120dd71c`
has an applicable successful native default build and complete standard-axiom
audit of its 130 modules (job 533, 2026-09-27). Its 125-module semidirect
predecessor has its own successful native job 530. That predecessor's
documentation-only release preparation preserved those checked inputs. The
upper-unitriangular destination snapshot
`7ad131de3c5a7696df678e944aaa20c1defbb397` has its own successful native job 682
(2026-09-28): both configured default targets, all 133 modules and a complete
transitive standard-axiom audit of 3,404 declarations, including 955 private-named
declarations. Independent non-author destination review and maintainer code
acceptance are complete for that predecessor. Its release preparation's pending
status is historical: the coordinate/group-only snapshot has since been
separately released and verified on the private official GitHub main. The
subsequently accepted geometry transfer adds two Lean modules, one aggregate
import and one explicit client root. Unlike job 682 or the isolated geometry
checks, native job 718 (2026-09-28, exact main commit
`31492d5a182c21f40af029121718ceca8085568a`) successfully built both
default targets (3,473 jobs) and audited all 135 modules: 3,419 actual-origin
declarations, including 956 private-named declarations, with only the three
allowed axioms. An independent non-author transfer review approved this exact
commit, and the responsible maintainer accepted and protected-integrated it
on 2026-09-28. This completes destination code acceptance, **not** independent
acceptance or publication of a geometry-bearing release. The preceding official
private GitHub release `20939506447f61a3f383cc67e76802fd4a2fbb75`
contains coordinate/group results but not this geometry.

The public mathematical interfaces retain their intended hypotheses and scope.
Compiler-generated proof and simplifier auxiliary names and types can change
under native module conversion. The ordinary-import regression clients are
registered on the pinned graph; their compilation, including the new promotion
clients, requires an applicable build. This does not promise compatibility for
arbitrary generated names. Clients should use the named mathematical APIs
rather than implementation auxiliaries.

The pinned toolchain is Lean `v4.34.0-rc2`; mathlib is
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The declared direct project dependency
is `scheme-properties`; its resolved closure also contains
`finite-etale-algebras` and `coherent-modules`. See [lakefile.toml](lakefile.toml)
and [lake-manifest.json](lake-manifest.json) for the exact twelve-package graph.
The project dependencies use official published GitHub release commits:
`scheme-properties` at `6b204a3e49f022e51d78a9f93e77513b99a87e00`, with
`finite-etale-algebras` at `79575f65c9edec560f27756917761eed78331a2a` and
`coherent-modules` at `fc30df937c7476f1c01f7cb39005f8cae37f8f34`.
These GitHub repositories are currently private, so authorized access is needed.
The upstream project dependencies are official releases; their acceptance is
separate from this library's verification and release records.

Begin with `import AlgebraicGroups` in a downstream Lean file using these
declared dependencies. For a smaller surface, import a focused module such as
`AlgebraicGroups.GroupScheme.Vector` or
`AlgebraicGroups.GroupScheme.GeneralLinear`. The standalone native
`AlgebraicGroups.GroupScheme.Additive` module publicly imports the native
`AlgebraicGroups.Algebra.SymmetricAlgebra` module. The native vector-group module
publicly imports native `AlgebraicGroups.Algebra.SymmetricAlgebraPoints`; its
convolution and tensor-point equivalences support ordinary coordinate evaluation,
contravariant coordinate pullback and covariant tensor maps. The current
[regression clients](AlgebraicGroupsTest) illustrate the intended APIs; the
build commands below explain their default and focused invocation.

`AlgebraicGroups.GroupScheme.ArtinSchreierTwistedLine` is also a native module.
It exposes the existing computational definitions `equation`, `equationIdeal`,
`x`, `y`, `SatisfiesEquation`, `lift`, `comul`, `counit`, `antipode`, `W`, and
`baseChangeNormalForm` to ordinary imports. The coordinate ring is the quotient
by `Y ^ p - Y = t * X ^ p`; in prime characteristic the coordinatewise Hopf
operations give an additive group scheme. A unit `u : Lˣ` satisfying
`(u : L) ^ p = algebraMap R L t` supplies the scalar-extension normal form.
Its four evaluation lemmas are simp lemmas; standard smoothness requires
`CharP R p`, and the field-domain/connectedness theorem requires a nonzero
twist and a prime `p`. Zero twist is disconnected under the stated prime-field
assumptions. Private computation helpers and proof steps are not public API.

The primitive-power Hopf ideal, additive-power quotient, and infinitesimal
additive group modules also use native module headers. Their authored names
and types remain available to ordinary imports, including the quotient
presentation at `N = 0` and `N = 1`, prime-characteristic nilpotent points at
`m = 0`, and zero base or target rings. Existing computational definitions are
exposed where needed for these ordinary-import reductions; the infinitesimal
quotient lift and its proof helpers remain private.

This migration does change generated auxiliary interfaces. In namespace
`AlgebraicGeometry`, `additivePowerCoordinateAlgEquiv._proof_4` is no longer
present, and
`infinitesimalAdditiveUnderlyingScheme_locallyOfFiniteType._simp_1` is now
private. Some other generated proof types also change. Code referring to
these compiler-generated names must migrate to the authored presentation,
evaluation, or finite-type APIs (or prove the needed intermediate statement).
The authored API and focused reduction checks are not a promise of compatibility
for every generated name; no replacement aliases are provided for them.

`AlgebraicGroups.Algebra.MatrixEndBaseChange` publicly imports only the mathlib
tensor-base-change and tensor-tower modules. It keeps `SourceOrderTensor` as the
canonical `R ⊗[K] V` module and `SourceOrderedTensor` as a separate wrapper for
literal `V ⊗[K] R`, without adding a scalar-module instance to the literal tensor
type. Endomorphism base change works for arbitrary modules over a commutative
base and arbitrary algebra maps, including non-flat maps and zero rings. Eight
existing named data definitions expose their ordinary reduction paths; the
transported additive and scalar instances remain public without `@[expose]`.
The MatrixEndAdditive and MatrixEndScheme production modules and their existing
regression clients also use the module system. Named matrix/endomorphism
comparison definitions expose the reduction paths required by the scheme APIs.
The authored public types, definition right-hand sides and tested ordinary
reductions remain the intended interface. Native compilation changes generated
implementation declarations: formerly visible `endBaseChange_comp._simp_1_1`
and `endBaseChange_comp._simp_1_2` become private, while
`endBaseChangeAddHom._proof_1` is replaced by `_proof_3`; other generated proof
types change. Those generated names are not
backward-compatible; use the named `endBaseChange_tmul`, `endBaseChange_id` and
`endBaseChange_comp` statements instead. This was a pre-release development
migration, not source-coverage acceptance. Earlier bounded default attempts
timed out; these historical failures are not reclassified as successes. The
combined final-graph build now includes these producer and regression modules;
its evidence is distinct from the earlier focused development checks.

The vector migration similarly makes the generated
`AlgebraicGeometry.vectorGroupUnderlyingScheme_locallyOfFiniteType._simp_1`
helper private. Its type and stored proof are unchanged, but its old ordinary
name is unavailable. Use the authored locally-of-finite-type instance/API
instead of this compiler-generated auxiliary; no compatibility alias is added.

## Upper-unitriangular group scheme

For a finite linearly ordered type `n` over a commutative ring `K`, the
`UnitriangularCoordinateRing` API gives the Hopf quotient of the localized GL
coordinate algebra and its free strict-upper-polynomial presentation. The
actual `AlgebraicGeometry.unitriangularGroupScheme K n` is affine of finite
type; `unitriangularInclusion K n` is a closed immersion into GL.
`unitriangularGroupMulEquivPoints K n R` identifies its points over a
commutative `K`-algebra `R` multiplicatively with
`Matrix.UnitriangularGroup n R`, including empty and singleton indices and
the zero ring. The `Fin 3` multiplication has a genuine cross term; this is
not a diagonal or arbitrary triangular group scheme, and no field or
positive-rank hypothesis is imposed.

Use `import AlgebraicGroups` or the focused
`import AlgebraicGroups.GroupScheme.Unitriangular`. The ordinary-import
ten-example client is `AlgebraicGroupsTest.Unitriangular`; see the
[upper-unitriangular guide](AlgebraicGroups/GroupScheme/Unitriangular/README.md)
for presentation maps, points, naturality and precise limits. Native job 682
and distinct independent destination review support maintainer code acceptance
of the already released coordinate/group predecessor; its checks were not
substituted for the changed geometry graph's own successful native job 718 and
independent transfer review. The geometry below is accepted on development
main but not yet independently accepted for release or published.

## Upper-unitriangular affine geometry

The underlying scheme of the unitriangular group is isomorphic **over `Spec K`**
to affine space on its strictly upper matrix entries for every commutative
coefficient ring and finite linear order. This is not an additive group-scheme
isomorphism: rank-three multiplication retains a cross term. The actual
structural morphism is smooth and geometrically integral even over the zero
ring (where the relative integrality condition is vacuous), while absolute
integrality of the underlying scheme needs `IsDomain K`. Numeric ring and
underlying-scheme Krull dimensions are `card ι` choose two **over fields**;
there is no unconditional absolute dimension formula over arbitrary bases.
The isomorphism's forward and inverse `Spec.preimage` readbacks, finite
presentation, smoothness and dimension theorems live in
`AlgebraicGroups.GroupScheme.UnitriangularGeometry`. Import that focused module
or `AlgebraicGroups`; see the [geometry guide](AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md)
and the 21-example `AlgebraicGroupsTest.UnitriangularGeometry` client for the
zero ring and ranks `0,1,2,3`. Beyond the independently agent-reviewed isolated
origin, exact destination commit `31492d5a182c21f40af029121718ceca8085568a`
has a successful both-target build and complete private/generated-inclusive
transitive standard-axiom audit (native job 718), independent transfer review
and maintainer code acceptance. Independent release review and protected
release acceptance/publication remain pending; no source-coverage decision follows.

## Current results

- `SymmetricAlgebra.linearMapMulEquivAlgHom` identifies linear maps into any
  commutative algebra with algebra maps out of a symmetric algebra under
  convolution. It works for arbitrary modules over a commutative ring; on
  primitive generators convolution is addition of linear maps.
- `AlgebraicGeometry.vectorGroupTensorDualEquiv` identifies `V ⊗[K] R` with
  the `K`-linear maps from `Module.Dual K V` to `R` when `V` is finite-dimensional
  over a field. `AlgebraicGeometry.vectorGroupScheme` is the affine group scheme
  represented by `SymmetricAlgebra K (Module.Dual K V)`; its structure map is
  locally of finite type and quasi-compact. The actual group-valued natural
  representation is `AlgebraicGeometry.vectorGroupPointsIso`, with pointwise
  `vectorGroupMulEquivAlgHom` and `vectorGroupMulEquivPoints`. The API includes
  pure-tensor evaluation, naturality in test algebras, and coordinate pullback
  for linear maps of vector spaces. It supports the zero-dimensional space and
  zero test algebra; `Multiplicative` tags addition, not scalar multiplication.
- `AlgebraicGeometry.vectorGroupSchemeFunctor` sends arbitrary vector spaces and
  linear maps to genuine group schemes and group-scheme morphisms. The associated
  bialgebra pullback and scheme-map readbacks expose the contravariant coordinate
  map. A finite basis yields `vectorGroupSchemeProductIso`, an isomorphism to the
  literal categorical product of copies of the additive group; its proof uses
  the universal property for maps from every scheme over the base, not only
  affine schemes. Basis-coordinate pullback and tensor-point formulas hold over
  every commutative test algebra, and the empty basis gives both the terminal
  group scheme and its underlying `Spec K` over itself. Finite dimensionality
  is needed for the tensor-point equivalence, not for the scheme functor.
- `AlgebraicGeometry.additiveMatrixFunctor` and `additiveEndFunctor` are
  additive group functors on commutative `K`-algebras. The former accepts finite
  rectangular indices (including empty ones); the latter accepts any
  `K`-vector space without a finiteness assumption and maps *every* algebra
  homomorphism using endomorphism base change and canonical tensor cancellation.
  `matrixVectorGroupIso` and, in finite dimension, `endVectorGroupIso` identify
  them naturally with the represented vector groups. `matrixGroupPointsIso`
  and `endGroupPointsIso` retain their existing finite-type affine group schemes.
  `SourceOrderedTensor` supplies the explicitly transported `R`-action on the
  literal source-order tensor `V ⊗[K] R`, with an `R`-linear comparison to
  `R ⊗[K] V`; `sourceOrderedEndEquiv` compares endomorphisms of those modules.
  Rectangular polynomial coordinates use `matrixCoordinateRingEquiv` and
  `matrixCoordinateEval_ι`; `endMatrixGroupIso`, `endMatrixCoordinateEval_ι`
  and `endMatrixBasisChangeIso` give chosen-basis endomorphism coordinates.
  The canonical End representation is independent of a basis, whereas its
  square-matrix coordinates depend on one. Polynomial evaluation is not an
  identification with all functions on finite-field-valued points.
- `sourceOrderedAdditiveEndFunctor` uses the explicitly transported module on
  literal `V ⊗[K] R`, without installing an ambiguous scalar-action instance on
  the raw tensor. `sourceOrderedEndBaseChange` works already over a commutative
  base ring, without finite dimension, flatness, or nonzero assumptions;
  `sourceOrderedEndGroupIso` is its natural comparison with the canonical End
  functor (whose public context has a field base). The pure-tensor action is
  `sourceOrderedEndBaseChange_tmul`. For finite-dimensional `V`,
  `sourceOrderedEndPointsIso` represents the literal-order End functor without
  choosing a basis. A finite basis `b` additionally gives the genuine native
  group-scheme isomorphism `endMatrixSchemeIso K V i b`. Its Spec/coordinate
  readbacks, `endMatrixSchemeIso_points` and `endMatrixSchemeIso_polynomial`
  identify the scheme action on every commutative test algebra with the accepted
  additive End/matrix point comparison and formal polynomial evaluation.
  `endMatrixSchemeBasisChangeIso` compares two bases as a native group-scheme
  isomorphism; its points agree with `endMatrixBasisChangeIso`. All finite-index
  APIs allow an empty basis and a zero test algebra. `Multiplicative` tags
  additive groups; none of these is the multiplicative End monoid or `GL(V)`.
- `GeneralLinearCoordinateRing.CoordinateRing K n` is the determinant
  localization of the polynomial algebra on square-matrix entries. It has a
  universal native `Matrix.GeneralLinearGroup` matrix and an explicit
  `quotientEquiv` with the inverse-adjoining polynomial quotient;
  `extraVariableEquiv` identifies the polynomial algebra with one additional
  indeterminate over the matrix-entry algebra. `homEquiv` classifies its algebra maps by
  invertible matrices over every commutative test algebra. The native Hopf
  structure has matrix-product comultiplication, identity counit and inverse
  antipode (without cocommutativity). `AlgebraicGeometry.generalLinearGroupScheme`
  is the corresponding finite-type affine group scheme, and
  `generalLinearGroupPointsIso` is its natural **multiplicative** comparison
  with the native matrix GL functor. All these constructions admit arbitrary
  commutative base and target rings, including zero rings and empty finite
  index types; finite indices need `Fintype` and `DecidableEq`. See
  `AlgebraicGroupsTest/GeneralLinear.lean` for direct examples. Arbitrary-module
  automorphisms and the finite determinant character are treated separately
  below; special linear group schemes are described separately below.
- `AlgebraicGeometry.generalLinearDeterminantSchemeHom K n` is the native
  group-scheme morphism from finite matrix GL to the multiplicative group over
  any commutative base ring. Its coordinate map sends the Laurent generator
  to the determinant of the universal matrix and its inverse to `detInverse`.
  The API proves the actual GL comultiplication, counit and antipode equations;
  `generalLinearDeterminantBialgHom` and `hopfSpec` construct the scheme map.
  `generalLinearDeterminant_point` identifies its action on every coefficient
  algebra with the unit-valued matrix determinant, and
  `generalLinearDeterminantFunctorHom` packages coefficient naturality.
  Empty finite indices, zero rings and non-flat coefficient maps are allowed;
  no field or nontriviality assumption is added. The section and determinant-one
  kernel are separate focused imports below; neither constructs a canonical
  determinant on arbitrary modules.
- `AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection` constructs
  `generalLinearDeterminantSectionSchemeHom K n pivot`, a multiplicative
  one-pivot diagonal section of finite GL's determinant character, natural in
  coefficient algebras over every commutative base. The explicit `pivot : n`
  is necessary: a rank-zero determinant need not have a section. The coordinate
  entries, inverse coordinate, native matrix points, non-affine scheme tests and
  `generalLinearDeterminantSplitEpi` give the section law. Its focused client is
  `AlgebraicGroupsTest.GeneralLinearDeterminantSection`.
- `AlgebraicGroups.Algebra.SpecialLinearCoordinateRing` defines the quotient
  of the finite GL coordinate algebra by the Hopf ideal generated by determinant
  minus one, with a polynomial quotient equivalence. The `SpecialLinear` module
  constructs its native Hopf/group scheme, closed immersion into finite GL and
  natural native `Matrix.SpecialLinearGroup` points. `SpecialLinearKernel` proves
  this closed subgroup is the actual determinant kernel by pushout of coordinate
  rings and pullback in schemes over `Spec K` and group schemes, with universal
  properties for arbitrary scheme and group-scheme tests. All of this allows
  arbitrary commutative bases, empty finite indices and zero rings; it asserts
  neither a basis-free SL(V) nor determinant-map smoothness or flatness by itself.
  Finite GL/SL smoothness and determinant-map smoothness are separate focused
  modules below. The client is
  `AlgebraicGroupsTest.SpecialLinear`.
- `endBaseChangeRingHom` packages scalar extension of endomorphisms of an
  arbitrary module as a composition-preserving ring map. For any commutative
  base `K`, `generalLinearModuleFunctor` uses native invertible endomorphisms
  and `MonCat.units` to obtain a group functor on all commutative coefficient
  algebras and algebra maps. `generalLinearModuleAutomorphisms` compares it
  with linear equivalences; `sourceOrderedGeneralLinearIso` compares it
  naturally with the transported literal-order tensor `V ⊗[K] R`. The
  pure-tensor formulas require neither finite generation nor flatness.
- A chosen finite basis, including an empty one, gives the natural matrix
  comparison `generalLinearModuleMatrixIso` and the pointwise representation
  `generalLinearModulePointsIso` by the existing finite-type affine GL group
  scheme. Both work over any commutative base ring, including zero rings.
  Entries, vector action, `Spec.map`, coordinate evaluation and inverse-
  determinant pullback have explicit equations. `generalLinearModuleChangeBasisIso`
  compares chosen presentations, with identity, composition, naturality and
  coordinate equations for the same underlying automorphism. There is no
  canonical basis-independent GL(V) scheme or arbitrary-module determinant
  scheme morphism, SL scheme or functoriality along noninvertible module maps
  asserted here. The finite matrix determinant character above is separate.
- `AlgebraicGroups.GroupScheme.SpecialLinearModule` defines the determinant-one
  automorphism functor of scalar extensions of a finite-free module and canonical
  coefficient reassociation compatible with GL(V). A *chosen* finite basis
  identifies it naturally with the native matrix SL group and the represented
  finite SL scheme's affine points; entry, action, determinant-inverse evaluation
  and change-of-basis laws are available. The basis can be empty; arbitrary
  commutative and zero rings are allowed. No canonical basis-free SL(V) scheme
  or construction for arbitrary/projective modules is asserted. Its focused
  client is `AlgebraicGroupsTest.SpecialLinearModule`.
- `AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth` proves finite matrix
  GL and SL coordinate algebras smooth over every commutative base and the actual
  `Spec` structure morphisms smooth, including empty indices and zero rings.
  For nonempty indices a chosen pivot normalizes the universal GL matrix to
  determinant one and splits the quotient **as an algebra map**, not as a
  group/Hopf map; empty rank uses the bottom-ideal quotient equivalence.
  These results alone do not assert smoothness of the determinant morphism,
  faithful flatness or a semidirect-product decomposition. The focused client is
  `AlgebraicGroupsTest.GeneralSpecialLinearSmooth`.
- `AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral` proves
  `IsDomain` for the actual finite GL and SL coordinate rings and `IsIntegral`
  for their underlying schemes when the commutative base `K` is a domain.
  Their *actual structure morphisms* are `GeometricallyIntegral` over every
  commutative `K`, including the zero ring (where field-valued fibers are
  vacuous). Finite decidable indices include ranks zero, one and two; no
  integral total space is claimed over an arbitrary non-domain base. The
  ordinary-import client is `AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral`;
  see its [guide](AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md).
- `AlgebraicGroups.Algebra.PolynomialRationalPointHeight` proves
  `MvPolynomial.height_ker_eval` over a field for any finite index type,
  including different field/index universes, without `DecidableEq`. The focused
  `AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension` import publicly
  exposes that helper and computes the actual GL/SL coordinate-ring Krull
  dimensions and underlying-scheme topological Krull dimensions over a field:
  `N ^ 2` for GL and `N ^ 2 - 1` for SL, with natural subtraction *before*
  casting to `WithBot ℕ∞` and rank zero handled separately. Its client
  `AlgebraicGroupsTest.GeneralSpecialLinearDimension` covers different
  universes, ranks zero/one/two and `ZMod 2`; see the
  [guide](AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md).
- `AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct` uses the
  section and actual determinant-one kernel pullback to construct
  `generalLinearDeterminantProductIso K n pivot : SL(n,K) ⊗ Gₘ,K ≅ GL(n,K)`
  as **underlying schemes over** `Spec K`. The forward map multiplies the
  diagonal section first, then the special-linear inclusion; its inverse
  normalizes with the inverse diagonal section. The `hom_comp_det` triangle
  and `inv_comp_snd` readback identify the actual determinant scheme morphism.
  `generalLinearDeterminantSchemeHom_smooth` proves that morphism is `Smooth`
  using the smooth special-linear structure map and base-change projection,
  without assuming flatness or circular smooth descent. Finite decidable `n`
  requires an explicit `pivot : n`; rank one and zero rings are allowed, but
  rank zero, a group-scheme product isomorphism and basis-free SL(V) are not
  claimed. See its [guide](AlgebraicGroups/GroupScheme/GeneralLinearDeterminantProduct/README.md)
  and `AlgebraicGroupsTest.GeneralLinearDeterminantProduct`.
- `AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation` restricts
  diagonal conjugation to the genuine determinant-one kernel, as an arrow over
  `Spec K`. Its affine point formula works over every commutative `K`-algebra;
  diagonal entries are units before coercion and inversion. A chosen pivot
  excludes rank zero, while rank one and zero rings are allowed. The underlying
  product iso has section-first twisted multiplication, not a canonical
  direct-product group-scheme law. See its
  [guide](AlgebraicGroups/GroupScheme/GeneralLinearDeterminantConjugation/README.md)
  and `AlgebraicGroupsTest.GeneralLinearDeterminantConjugation`.
- `RingHom.FaithfullyFlat.ofLocalizationSpan` proves that faithful flatness can
  be checked after localizing along a family of source elements that spans the
  unit ideal. It accepts arbitrary principal-open covers, including infinite
  families and the empty cover of the trivial ring.
- `RingHom.FaithfullyFlat.ofCompleteOrthogonalIdempotents` and its
  `ofIsLocalization` variant specialize this criterion to finite clopen
  decompositions, including arbitrary chosen models of the localized rings.
- `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`
  descends finite presentation of modules along faithfully flat base change.
- `LocalInfiniteResidueExtension.GenericLocalExtension` localizes `R[X]` at
  the extension of a local ring's maximal ideal. It is a faithfully flat local
  `R`-algebra whose residue field is the rational function field over the
  residue field of `R`, and is therefore infinite.
- `MaximalSpectrum.finite_of_finite_orbit` proves that a finite relation leg
  and transitivity on maximal points make the object ring semilocal. Its
  `finite_of_isIntegral_of_isLocalRing` variant reduces transitivity to fibres
  over an integral local base. Consequently,
  `Module.nonempty_basis_of_finrank_eq_of_integral_local_orbit` turns constant
  fibre rank of the finite flat leg into a global basis. The finite-orbit
  theorem includes the empty-maximal-spectrum case; the local corollaries use
  mathlib's explicit `IsLocalRing`/`Nontrivial` boundary. None of these results
  asserts that an equivalence relation is effective.
  `Ideal.map_maximalIdeal_le_jacobson_of_isIntegral` supplies the accompanying
  Jacobson-radical input for an integral algebra over a local ring.
- `AlgHom.isIntegral_equalizer_of_idempotent_polynomial_patches` patches
  finitely many monic equations supported on a complete family of idempotents
  into a single monic equation over the equalizer of two algebra maps.
  Orthogonality is not required.
- `AlgHom.equalizerMapOfCommuting` maps equalizers along a commuting square of
  pairs. Its `equalizerMapOfCommuting_isLocalizationAway` theorem identifies
  this map as localization away from an invariant idempotent when both ambient
  maps are the corresponding idempotent localizations.
- `CategoryTheory.EquivalenceRelation.isLimit_composition_fst` gives the
  cartesian composition square of an internal equivalence relation. For a
  finite flat relation in schemes, `AlgebraicGeometry.EquivalenceRelation`
  proves that the two projections have the same rank, that rank is invariant
  along relation arrows, and its locally finitely presented rank strata are
  clopen invariant opens. The rank is positive and has finite range on a
  compact target. This is rank-stratum infrastructure only; it does not assert
  quotient effectivity.
- `AlgebraicGeometry.Scheme.Opens.exists_isIdempotent_isLocalization` realizes
  a clopen subset of an affine scheme as a basic open cut out by an idempotent
  and identifies its coordinate ring as the corresponding away localization.
  `AlgebraicGeometry.Scheme.Hom.exists_isIdempotent_isLocalization_and_preimage`
  does this simultaneously for its preimage under an affine morphism; the same
  module records the natural restriction squares on global sections.
- `AlgebraicGeometry.EquivalenceRelation.exists_finrankOpen_localizations_and_squares`
  specializes that interface to the invariant rank strata of a finite flat
  equivalence relation: one idempotent localizes both the affine object and
  relation rings, has equal images under the two relation maps, and makes both
  restriction squares commute. On an affine target,
  `exists_completeOrthogonalIdempotents_finrankOpen` packages the finitely many
  nonempty rank fibres as one complete orthogonal family of invariant
  idempotents.
- `AlgebraicGeometry.EquivalenceRelation.exists_finrankOpen_equalizer_isLocalizationAway`
  identifies the resulting restriction map from the global invariant-ring
  equalizer to the rank-stratum equalizer as localization away from the induced
  invariant idempotent.
  `finrankOpen_equalizer_isLocalizationAway_of_basicOpen_eq` makes that
  localization independent of the chosen idempotent presentation, while
  `exists_completeOrthogonalIdempotents_equalizer_finrankOpen` lifts the rank
  family to the global equalizer. This does not prove faithful flatness,
  identify a tensor comparison, construct a quotient, or prove quotient
  effectivity.
- `Module.FiniteProjective.finiteProjectiveCharpoly` defines the canonical
  characteristic polynomial of an endomorphism of a finite projective module
  of constant local rank, with base-change, monicity, and Cayley--Hamilton
  theorems. Its reusable core is the presentation-independent Fredholm
  polynomial in `AlgebraicGroups.LinearAlgebra.FiniteProjective.Fredholm`,
  whose independence proof uses the rectangular Weinstein--Aronszajn matrix
  identity. It does not construct or specialize fixed-degree exterior-power
  base change: that API remains an upstream mathlib responsibility, while the
  accepted `projective-modules` exterior-algebra, projectivity, determinant,
  and invertible-line APIs remain separate reusable results.
  `AlgebraicGeometry.EquivalenceRelation.isIntegral_appTop_equalizer_of_equivalenceRelation`
  applies it rank-stratum by rank-stratum to prove that the coordinate ring of
  an affine finite locally free internal equivalence relation over a compact
  affine object is integral over the equalizer of its two coordinate maps.
  This result does not assert faithful flatness, tensor-comparison
  bijectivity, quotient representability, or effectivity.
- `LinearMap.exists_mem_isUnit_apply_of_le_jacobson` finds, inside a base
  submodule spanning over a semilocal algebra, a vector on which a surjective
  linear functional is a unit when the local base has infinite residue field
  and its maximal ideal extends into the Jacobson radical.
  `Module.Basis.exists_basis_subset_of_le_jacobson` iterates this to select a
  finite module basis entirely inside the generating base submodule.
- `Algebra.Etale.isReduced_of_isDomain`,
  `Algebra.IsStandardSmooth.isReduced_of_isDomain`, and
  `Algebra.Smooth.isReduced_of_isDomain`: étale, standard smooth, and smooth
  algebras over an integral domain are reduced. At scheme level,
  `AlgebraicGeometry.Smooth.isReduced_of_isDomain` gives the corresponding
  statement over the spectrum of a domain, and every smooth morphism is
  geometrically reduced via
  `AlgebraicGeometry.Smooth.geometricallyReduced`.
- `TensorProduct.piScalarRightHom_injective_of_free` and
  `Algebra.TensorProduct.pi_baseChangeEvaluation_injective_of_free`: tensoring
  into an arbitrary product is injective for a free tensor factor, and hence an
  arbitrary jointly injective family of scalar-valued algebra maps stays
  jointly injective after a free scalar extension.
- `Algebra.IsGeometricallyReduced.of_joint_evaluations` and
  `Algebra.IsGeometricallyReduced.of_iInf_eval_ker_eq_bot`: a jointly injective
  family of rational-point evaluations, equivalently one whose kernels have
  zero intersection, makes a commutative algebra over a field geometrically
  reduced.
- `Algebra.IsSeparablyGenerated.of_isGeometricallyReduced` and
  `Algebra.FormallySmooth.of_isGeometricallyReduced`: a geometrically reduced
  field extension of finite type is separably generated and formally smooth.
  At scheme level,
  `AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_geometricallyReduced`
  shows that a geometrically reduced scheme locally of finite presentation over
  an arbitrary field has dense smooth locus. Over a separably closed field,
  `AlgebraicGeometry.RationalPointSet.dense_underlyingPoints_of_isSepClosed`
  then makes all rational points dense, and
  `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_of_geometricallyReduced_of_isSepClosed`
  packages schematic density after extension to a separably closed field.
- `CategoryTheory.Over.effectiveEpi_of_effectiveEpi_left`: a morphism in an
  over-category is an effective epimorphism when its underlying morphism is.
- `AlgebraicGeometry.AffineRelationQuotient`: for a pair of affine-scheme
  morphisms `R ⇉ X`, constructs the affine coequalizer, its universal map and
  the canonical comparison with the kernel pair. The nested coordinate-ring
  API defines the invariant ring and tensor comparison in independent
  universes. If the object ring is faithfully flat over the invariant ring and
  the tensor comparison is bijective,
  `hasExpectedGeometry_of_hasExpectedAlgebra` proves that the quotient map is
  flat and surjective and that the relation is its kernel pair. This is the
  reusable algebra-to-geometry seam. If the relation ring is finitely presented
  over the object ring via the first relation map, the same package also proves
  that the object ring is finitely presented and projective over the invariant
  ring. It does not derive
  the algebra hypotheses
  from finite locally free equivalence-relation assumptions.
- `CategoryTheory.FinitaryExtensive.isPullback_sigmaMap_ι`: in a finitary
  extensive category, the square formed by one component of a map between two
  finite coproducts and the corresponding coproduct inclusions is a pullback.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`: a target-local property
  of scheme morphisms that holds on every summand is preserved by the induced
  map between finite coproducts.
- `CategoryTheory.GrpObj.ofEffectiveEpi`: multiplication and inversion that
  restrict to an effective-epimorphic subobject of a group object induce its
  group-object structure.
- `AlgebraicGeometry.effectiveEpi_toUnit_of_nonempty`: a nonempty
  quasi-compact scheme over a field effectively covers the terminal object in
  the over-category.
- `CategoryTheory.isMonHom_of_mul_hom`: a morphism from a monoid object to a
  group object that preserves multiplication also preserves the unit and hence
  is a monoid morphism.
- `AlgebraicGeometry.isSeparated_of_isClosedImmersion_unit`: a group scheme is
  separated when its unit section is a closed immersion.
- `AlgebraicGeometry.isSeparated_of_grpObj`: every group scheme over a field is
  separated.
- `AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver`: finitely generated algebras
  over a field, oppositely, are equivalent to affine locally-finite-type
  schemes over that field.
- `AlgebraicGeometry.algebraicOverPointsFullyFaithful` and
  `AlgebraicGeometry.algebraicGroupPointsFullyFaithful`: evaluation on
  finitely generated algebras is fully faithful for finite-type schemes and
  finite-type group schemes.
- `AlgebraicGeometry.algebraicGroupPoints_essImage_iff`: a group-valued functor
  on finitely generated algebras comes from a finite-type group scheme exactly
  when its underlying set-valued functor comes from a finite-type scheme.
- `CategoryTheory.NatTrans.IsPointwiseSubgroup.grpObj` and
  `AlgebraicGeometry.algebraicGroupOfPointwiseSubgroup`: an injective represented
  finite-type subfunctor whose component ranges are subgroups inherits a
  finite-type group-scheme structure, and its original map to the group scheme
  is a group-object homomorphism.
- `AlgebraicGeometry.rootsOfUnityGroupScheme` and
  `AlgebraicGeometry.rootsOfUnityPointsIso`: the affine finite-type group scheme
  represented by `K[ZMod n]` has the natural group-valued functor of `n`-th
  roots of unity; `AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv` identifies
  its coordinate ring with `K[T]/(T^n - 1)` for positive `n`.
- `FrobeniusTwistedLine.groupScheme`: the characteristic-`p` affine group
  scheme cut out by `Y^p - tX^p`. When `t` is not a `p`-th power, its
  coordinate ring is a reduced domain, while an explicit nonzero nilpotent
  after adjoining a `p`-th root proves that it is not geometrically reduced.
- `FrobeniusTwistedLine.baseChangeNormalForm`: after adjoining `α` with
  `α^p = t`, its scalar-extended coordinate ring is explicitly equivalent to
  `L[W,X]/(W^p)`. The equivalence sends `X` to the free line coordinate and
  `Y - αX` to `W`; forward and inverse coordinate equations expose the
  order-`p` thickening directly.
- `CategoryTheory.GrpObj.mulLeft`: left translation by a point is an
  isomorphism of a group object; its point action, unit image, and composition
  laws are exposed directly, with generated additive forms.
- `CategoryTheory.GrpObj.isPullback_kernel_mul`: when `N` is the kernel of a
  group-object homomorphism `G ⟶ Q`, multiplication identifies `N × G`
  with the self-pullback `G ×_Q G`.
- `CategoryTheory.splitKernelProductIso` accepts a multiplicative group-object
  quotient `q : G ⟶ Q`, its actual kernel square with `i : N ⟶ G`, and an
  **underlying-object** section `e : Q ⟶ G`. It gives `N ⊗ Q ≅ G` with
  section-first multiplication and quotient projection `snd`; neither a group
  structure on `N` nor a multiplicative section is needed. This is **not** a
  direct-product group-object isomorphism. See its
  [guide](AlgebraicGroups/GroupObject/SplitKernelProduct/README.md) and
  `AlgebraicGroupsTest.SplitKernelProduct`, which includes a concrete
  nonmultiplicative-section example.
- `CategoryTheory.splitKernelConj` is the pullback-defined conjugation of an
  actual group-object kernel by an arbitrary underlying-object section. A
  multiplicative section additionally gives the internal left-action laws and
  the explicit section-first twisted multiplication for the underlying-object
  product iso; no direct-product group-object isomorphism is asserted. See its
  [guide](AlgebraicGroups/GroupObject/SplitKernelSemidirect/README.md) and the
  nonabelian client `AlgebraicGroupsTest.SplitKernelSemidirect`.
- `CategoryTheory.NatTrans.IsPointwiseNormal.quotient` constructs the
  pointwise quotient of a group-valued functor by a transformation with normal
  component ranges. Its canonical map is pointwise surjective with the expected
  kernels and is the categorical coequalizer of the original and trivial
  transformations. `CategoryTheory.IsMonHom.Normal.yonedaQuotient` specializes
  this to the presheaf `X ↦ G(X) / H(X)` of a normal subgroup object, without
  asserting a sheaf condition or representability.
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotient` sheafifies this
  pointwise quotient on the relative fppf site of a base scheme, with group
  values lifted to the universe in which sheafification exists. The canonical
  projection `relativeFppfQuotientMk` is locally surjective and hence an
  epimorphism of sheaves, and maps which kill the normal subgroup descend
  uniquely through it. If the normal subgroup is the kernel of a flat,
  surjective, locally finitely presented group-scheme morphism `G ⟶ Q`,
  `relativeFppfQuotientIso` identifies the quotient sheaf with the sheaf
  represented by `Q`. No componentwise surjectivity after sheafification is
  asserted.
- `CategoryTheory.IsMonHom.yonedaCoset` constructs the type-valued presheaf
  of pointwise left cosets for an arbitrary group-object morphism, without
  normality. `CategoryTheory.IsMonHom.relativeFppfCoset` sheafifies it on the
  relative fppf site. If an fppf map `G ⟶ Q` has self-pullback presented by
  the right subgroup action, `relativeFppfCosetIso` identifies this coset
  sheaf with the type-valued sheaf represented by `Q`; the target need not be
  a group scheme.
- `AlgebraicGeometry.topologicalKrullDim_quotient_le_zero_of_isOpen_range`
  proves that an fppf coset quotient by a subgroup with open underlying range
  has topological Krull dimension at most zero over an algebraically closed
  field. In particular,
  `AlgebraicGeometry.reducedIdentityComponent_quotient_topologicalKrullDim_le_zero`
  applies this to any already constructed quotient by `(G_red)⁰`. These
  results do not construct the quotient target.
- `GrpCat.hasFilteredColimits` supplies same-universe filtered colimits of
  groups from Mathlib's explicit filtered-colimit cocone. In particular, the
  generic group-valued fppf sheafification instances are available; no
  representability is asserted.
- `AlgebraicGeometry.smooth_of_smooth_kernel` and
  `AlgebraicGeometry.smooth_of_smooth_kernel_quotient`: a faithfully flat,
  locally finitely presented morphism of group schemes with smooth kernel is
  smooth; if its quotient is smooth, then its middle group scheme is smooth.
- `AlgebraicGeometry.smooth_of_unit_mem_smoothLocus_of_isAlgClosed`: a group
  scheme locally of finite type over an algebraically closed field is smooth
  when its identity point belongs to the smooth locus.
- `AlgebraicGeometry.smooth_of_unit_mem_smoothLocus`: the same identity-point
  criterion over an arbitrary field, proved by transport to an algebraic
  closure and smooth descent.
- `AlgebraicGeometry.Scheme.Hom.appTop_injective_of_epi` and
  `appTop_injective_of_flat_of_surjective`: epimorphisms, in particular flat
  surjections, induce injective pullback maps on global sections.
  `AlgebraicGeometry.IsAffineHom.isIso_of_epi_of_isIso_comp_appTop` and its
  flat-surjective specialization show that an affine quotient with unchanged
  global sections is trivial.
- `AlgebraicGeometry.IsFinite.of_topologicalKrullDim_le_zero`: a
  quasi-compact, locally finite-type morphism to a locally Artinian scheme is
  finite when its source has topological Krull dimension at most zero.
- `AlgebraicGeometry.Scheme.nilradicalSubscheme_isReduced` and
  `AlgebraicGeometry.Scheme.Hom.existsUnique_liftNilradicalSubscheme`: the
  closed subscheme cut out by a scheme's nilradical ideal sheaf is reduced,
  and every morphism from a reduced scheme factors through it uniquely.
  `AlgebraicGeometry.Scheme.reduction` packages this construction as an
  endofunctor, with the canonical inclusions forming the natural transformation
  `AlgebraicGeometry.Scheme.reductionι` to the identity functor. Its naturality
  equation and reassociation are simp-facing through
  `AlgebraicGeometry.Scheme.reduction_map_comp_reductionι_app`. The inclusion is
  a homeomorphism on underlying spaces, so reduction preserves local
  connectedness and topological Krull dimension.
- `AlgebraicGeometry.Scheme.reductionOver_grpObj`: for a group scheme over a
  reduced base whose reduced underlying scheme has reduced Cartesian square,
  the scheme reduction inherits a group-scheme structure. The canonical
  inclusion `AlgebraicGeometry.Scheme.reductionOverι` is a monoid-object
  homomorphism. The Cartesian-square reducedness assumption is explicit; no
  general preservation of fibre products by reduction is asserted.
- `AlgebraicGeometry.Scheme.identityComponentOver`: over a nonempty one-point
  base, the identity component of a group scheme with locally connected
  underlying space is an open-and-closed connected subscheme, and it stays
  reduced when the ambient scheme is reduced. If the Cartesian square of this
  component is connected, it inherits a group-scheme structure and its inclusion is a
  monoid-object homomorphism. This applies conditionally to
  `Scheme.reductionOver`; no finite-type local-connectedness or fibre-product
  connectedness theorem is inferred. If its structure morphism is moreover
  geometrically connected, `Scheme.identityComponentConj` restricts ambient
  conjugation and the inclusion is `CategoryTheory.IsMonHom.Normal`. Geometric
  connectedness is an explicit extra assumption; it is not inferred from the
  component-square hypothesis.
- `AlgebraicGeometry.Scheme.identityComponentLift`: a monoid-object morphism
  from a connected monoid scheme factors canonically through the target's
  identity component. In particular,
  `AlgebraicGeometry.Scheme.reducedIdentityComponentToIdentityComponent`
  gives the closed monoid-subgroup comparison `(G_red)⁰ ⟶ G⁰` under the
  explicit hypotheses needed by the existing reduction and identity-component
  constructions. This names the subgroup in the residual quotient
  `G⁰/(G_red)⁰`; it does not construct or represent that quotient, prove the
  comparison normal, or prove the quotient finite.
- `topologicalKrullDim_eq_iSup_of_isOpen_cover` makes topological Krull
  dimension local on arbitrary open covers. Consequently,
  `AlgebraicGeometry.identityComponent_topologicalKrullDim` identifies the
  dimension of a locally finite-type group scheme over an algebraically closed
  field with that of its identity component, and
  `AlgebraicGeometry.reducedIdentityComponent_topologicalKrullDim` gives the
  same equality for `(G_red)⁰` under the explicit reduced-square hypothesis
  needed to construct the reduced group scheme.
- `AlgebraicGeometry.groupSchemePointMulEquivClosedPoint`: over an
  algebraically closed field, the group of rational points of a finite-type
  group scheme is equivalent to its closed points with the transported group
  structure; inversion and left translation restrict to closed-point
  homeomorphisms, and any two closed points are related by a scheme
  automorphism over the base.
- `AlgebraicGeometry.finiteConstantLocallyConstantMulEquivPoints` identifies
  the points of a finite constant group scheme over any commutative algebra
  with locally constant labels on its prime spectrum, including for the zero
  algebra.  It is natural in the algebra and specializes, for nontrivial rings
  with only trivial idempotents, to the indexing finite group itself.
- `AlgebraicGeometry.rationalComponentGroupEquivConnectedComponents`: when the
  identity component has the explicitly required group-scheme structure, the
  quotient of the rational-point group by its point image is equivalent to the
  connected components of the underlying scheme over an algebraically closed
  field. For a finite-type group scheme this quotient is finite. Geometric
  connectedness of the identity component separately supplies normality and
  hence the quotient's group structure.
- `AlgebraicGeometry.componentSchemeMap`,
  `AlgebraicGeometry.componentSchemeMap_flat`,
  `AlgebraicGeometry.componentSchemeMap_surjective`, and
  `AlgebraicGeometry.componentSchemeMap_locallyOfFinitePresentation`: under
  those explicit
  hypotheses, the group scheme maps canonically to the finite constant group
  scheme indexed by its rational component group. The map sends each rational
  point to its quotient class and is a monoid-object homomorphism. Its
  multiplication proof is componentwise on the open cover by products of
  translated identity components. Under the source and target coproduct
  decompositions, it is the coproduct map induced by the component-open
  structure morphisms. The
  identity-component inclusion maps to the target unit, and its square over
  that unit is a pullback, identifying the identity component as the
  scheme-theoretic kernel. The component morphism is flat, surjective, locally
  of finite presentation and quasi-compact, hence an effective epimorphism;
  specializing
  `CategoryTheory.GrpObj.isPullback_kernel_mul` gives its kernel-multiplication
  torsor square.
- `AlgebraicGeometry.identityComponentRelativeFppfQuotientIso` identifies the
  relative fppf quotient by the identity component with the group-valued sheaf
  represented by the finite constant rational component group. This is a
  sheaf-level representability statement; no residual reduced-identity-
  component quotient is identified.
- `AlgebraicGeometry.JointlySchemeTheoreticallyDominant` and
  `AlgebraicGeometry.RationalPointSet.SchematicallyDense`: a family of scheme
  maps is jointly scheme-theoretically dominant exactly when it does not factor
  through a proper closed subscheme; for rational points of an affine scheme,
  this is equivalent to the intersection of their maximal evaluation ideals
  being zero. For arbitrary schemes, rational points are schematically dense
  exactly when the scheme is reduced and their underlying points are dense,
  equivalently when their evaluations are jointly injective on the sections of
  every open set. `AlgebraicGeometry.FieldValuedPoints.SchematicallyDense`
  similarly packages all points valued in an extension field and characterizes
  density both by closed-subscheme factorization and by reducedness plus
  topological density. On affine schemes it is equivalently detected by the
  zero intersection of the kernels of the direct evaluations into the
  extension field. Extension-field-valued points are equivalent to rational
  points after base change, and geometric reducedness plus density of those
  rational points implies schematic density. Schematically dense closed
  subschemes are determined by their extension-field-valued point subsets; in
  particular, this applies to geometrically reduced closed subschemes locally
  of finite type over a field after passing to a separably closed extension.
  Morphisms to a separated target, absolutely or over a base, are determined by
  their restriction to such a family.

## Build

The exact Lean toolchain is in `lean-toolchain`, and `lake-manifest.json` pins
the complete dependency graph. Run:

```sh
lake exe cache get
lake build
```

Require the matching cache command to succeed before starting a build. A failed
fetch is not a reason to compile all of mathlib from source. Fetch again after
changing Lean/mathlib pins or deleting/replacing `.lake`.

See [Build and resource guidance](docs/BUILDING.md) for a measured development
baseline, its cache and memory context, and the distinction between a warm
default build and checking every shipped file. These measurements are not a
timing guarantee or a cold-build benchmark for the final graph.

The default build selects the production aggregate and the `AlgebraicGroupsTest`
target. Its 33 explicit roots in [lakefile.toml](lakefile.toml) cover every
checked-in file under `AlgebraicGroupsTest/`. Additive's twenty original
examples are persistent private declarations: they are compiled but do not
extend the public API. The native Artin--Schreier test also uses named private
clients, exercising ordinary-import reductions, quotient evaluation, Hopf maps,
normal-form projections and the smoothness/domain/connectedness APIs. It is a
focused regression, not an audit of every generated declaration, a source
correspondence decision, or a release-acceptance check.

The checked-in tree contains 135 Lean source files: 102 production files,
including the aggregate, and 33 regression files. The aggregate and all 33
explicit test roots reach all 135 local modules. There are no shipped tests
outside the declared default targets. Source reachability alone establishes neither a
successful build, complete transitive axiom audit or release acceptance.
The predecessor accepted 130-module main graph has a successful actual both-default-target
build (native job 533, 3,468 jobs) and a complete private-inclusive transitive
axiom audit (3,268 module-origin declarations, including 944 private-prefix
declarations; only the three allowed axioms). These checks covered the
predecessor's unchanged Lean, build, dependency and checker inputs in its
documentation-only release preparation; they do not certify the later
133-module coordinate/group transfer. Native job 682 independently built that
133-module graph (3,471 jobs) and
audited all 3,404 module-origin declarations, including 955 private-named
declarations, with only the three allowed axioms. Of its 150 recorded file
tuples, only four documentation/metadata files changed in its preparation;
its Lean, toolchain, build, dependency and checker inputs remained unchanged.
That predecessor is now separately released. The accepted 135-module geometry
graph changes the Lean/import/root inputs; neither predecessor job nor the
isolated origin's focused check establishes its destination computation.
Native job 718 independently built both default targets (3,473 jobs) and
audited all 135 modules and 3,419 actual-origin declarations, including 956
private-named declarations, using only the three allowed axioms. Independent
exact-destination transfer review and maintainer code acceptance are complete;
separate independent release acceptance and publication remain open.
Documentation and metadata changes here do not alter the checked Lean, build,
dependency or checker inputs.

The new unitriangular geometry client checks 21 ordinary-import examples:
the affine-space isomorphism over the base and both actual pullbacks, inferred
regularity and relative integrality at the zero ring, absolute integrality only
over domains, and field dimensions at ranks `0`, `1`, `2`, `3`. It is the 33rd
persistent root. Its compilation is covered by native job 718; the selected
twelve geometry metadata rows are not the complete fifteen-declaration actual
geometry census, which includes generated and private declarations.

The GL(V) regression adds 25 named private clients for arbitrary-module
coefficient change, transported tensor order, finite-basis matrices and
coordinate points. It also checks the empty basis, zero base and target rings,
finite-field coefficients, and a nonidentity polynomial shear under evaluation.
These clients do not add public mathematical declarations.

The determinant regression imports its focused producer and uses named private
checks for the actual group-scheme morphism, both Laurent coordinates, the Hopf
equations and all-algebra points/naturality. It includes empty indices, a zero
ring, the non-flat coefficient map from integers to `ZMod 2`, and the explicit
nonidentity negative-one matrix over the integers. It adds no public API.

The determinant-section client tests one- and two-dimensional diagonal units,
zero coefficient rings, coefficient changes and arbitrary scheme tests. The SL
client checks the Hopf quotient, degenerate cases, nontrivial shear, affine
points and genuine scheme/group-scheme kernel pullbacks. Both remain default
roots; neither declares a new public mathematical API.

The SL(V) client checks empty, rank-one and rank-two bases, zero-ring targets,
an integer shear, scalar extension and nontrivial basis changes. The finite
GL/SL smoothness client checks finite presentation, coordinate and `Spec`
smoothness, empty indices and zero rings, and the quotient normalization and
retraction. Both focused clients are persistent default-build roots.

The split-kernel product client checks the underlying-object section formulas
and a provably nonmultiplicative section. The finite determinant-product client
checks the actual determinant triangle, normalized inverse and smoothness for
rank-one integers and a zero ring. Both are persistent ordinary-import roots;
their destination validation and review are recorded against exact revisions.

The split-kernel semidirect client checks the arbitrary-section conjugation
readback and the twisted product law, including a nonabelian `Fin 3`
permutation example. The determinant-conjugation client checks every-algebra
points and opposite row/column pivot scaling over `ZMod 5`. Both are
persistent ordinary-import roots. The original transfer has independent
source-only review. The separately accepted 125-module PR183 predecessor has
its own applicable native job 530 and independent affected review; the earlier
130-module union has applicable native job 533 and fresh affected review.
Native job 477 covered only the earlier 121-module predecessor at its inputs.
Those prior checks did not themselves establish release acceptance; that
predecessor was subsequently released separately. They do not replace native
job 718 or independent review of the accepted geometry transfer.

The finite GL/SL geometric-integrality client checks ranks zero, one and two,
including the zero base; the dimension client checks those ranks, `ZMod 2`
and distinct universes without a decidable-equality assumption on the index.
Both are persistent ordinary-import roots. Their original source-only transfer
has independent review; the accepted 130-module assembly has applicable native
job 533 and fresh affected review. That predecessor was separately released at
`28a1288c1eae8c7230f89c0b165415304fbd0f98`; this is not approval of the new release.

The native MatrixEndBaseChange test has named private ordinary-import clients
for tensor order, wrapper projections and addition, transported scalar action,
endomorphism conjugation, base-change evaluation, identity, composition and
arbitrary tensor sums. Its boundary cases include polynomial evaluation, an
empty module and a zero-ring target; it adds no public mathematical declarations.

Vector's thirty-four
original examples persist as named private checks, alongside nine private
reduction checks for the exposed data. Its existing named local
`zeroRingAlgebra` remains ordinary-visible; the clients also cover the zero
test algebra and zero-dimensional tensor points.

The native infinitesimal-additive test adds thirty-two named
private declarations corresponding by source command to the original anonymous
examples, alongside its two existing private coordinate tests. It exercises the
prime-characteristic Hopf quotient and nilpotent points, including a zero target,
first power, small characteristics and polynomial bases. The four data-valued
correspondence cases are expressed as ordinary equality regressions comparing
each complete value with its literal original right-hand side at the original
type and parameter context. These regressions do not establish identity with a
historical runtime elaboration, and such a reconstruction is not a release
prerequisite. An earlier injected-observer diagnostic
changed the original module and reported four unequal values despite thirty-two
matching types; it is not an acceptance result. Four private `_original` equality
theorems now express the direct whole-data checks beside their definitions;
they compile in the final-graph build. These private tests add no public API; the
producer's point,
coordinate and naturality APIs remain the ordinary-import interfaces. Prior
strict in-file and private-inclusive test lint reported two `unusedArguments`
findings on the original `[Subsingleton R]` binders. This candidate retains those
binders and the unchanged general-equivalence bodies, with two documented,
declaration-specific `nolint unusedArguments` exceptions. The stronger-context
regression statements are preserved without adding artificial dependencies.
These are explicit exceptions, not successful unused-argument checks or a global
lint pass; the historical failures remain part of the verification record.
The final build does not claim a fresh exhaustive private-inclusive lint pass.
The documented exceptions require a substantive convention disposition in
independent review rather than erasure of their original regression hypotheses.

Preserving the original full types of three vector examples retains unused
finite-dimensional class binders. A strict private-inclusive test lint reports
three `unusedArguments` findings on these newly persistent declarations; this is
an explicit lint nonpass, not a removed hypothesis or a blanket lint waiver.
Imported package-level lint also has documentation-origin findings distinct
from the passing in-file producer lint. These scopes must not be conflated with
a full repository lint pass.

The module assembly also includes the retained MatrixEndAdditive,
MatrixEndScheme and VectorProduct module conversions and the GeneralLinear,
MatrixEndAdditive and VectorProduct persistent tests, all compiled on the final
dependency graph. Six MatrixEndAdditive tests and six
VectorProduct tests retain intentionally redundant hypotheses from their original
regression contexts; explicit binders and documented declaration-specific
`nolint unusedArguments` exceptions preserve those contexts. GeneralLinear's
subsingleton-target regression uses the same narrowly scoped exception. These
are explicit convention exceptions for independent release review, not claims
that the earlier unused-argument diagnostics passed. MatrixEndAdditive's stored
expected-error wrappers have been removed; its ordinary `#lint` command remains.
The final build includes the ordinary-import clients, named original regression
statements and four whole-data equality checks. Prior partial native results
and failed comparisons are preserved separately, not promoted to passes.

The remaining test-module conversion retains 76 formerly anonymous examples as
private declarations and preserves 15 existing public names in the
InfinitesimalAdditiveNonisomorphism, MatrixEndScheme and MonoidAlgebraPrimitive
tests. Three MatrixEndScheme checks preserve their original finite-dimensional
context under explicit binders and documented `unusedArguments` exceptions;
seven private class-valued checks use `instance_reducible`. Their compilation
and independent convention assessment are distinct checks. Translation
and the first-power infinitesimal group expose their named coordinate and map
lemmas without exporting private construction helpers or their bodies.

The native additive-power test retains its twenty existing **public** theorem
names, statements and proofs. It checks quotient presentations and nonzero
coordinates, zero/first exponents, subsingleton and non-domain base rings, and
infinitesimal points including a zero target algebra. These existing public
test names are deliberately preserved, unlike the private examples above.

The focused ordinary-import TargetCopy test covers
the exposed definitions `TargetCopy.ringEquiv`, `TargetCopy.map`, and
`targetCopyMap`: their copy evaluation and transported scalar-action equations
reduce definitionally, including the `rfl` obligation used to construct the
copied algebra equivalence. It also checks rewriting, simplification and the
existing scalar-tower API. Exposing these existing public bodies is an explicit
reducibility commitment; no new public wrapper or global simp rule is added.

All regression modules are now selected by the default build; separate direct
invocations are unnecessary merely to include previously unregistered sources.
The selected configuration must pass the actual default build on the pinned
official dependency graph; exact-version results are recorded separately.
Generated, revision-bound API documentation for this 135-module candidate is not
supplied; earlier generated snapshots have not been regenerated. The README and
source docstrings provide the reader documentation. Their claims
require independent inspection; fresh expensive documentation generation is not
a release prerequisite.

The focused vector-group producer and persistent regression test build with
`lake build AlgebraicGroupsTest.Vector`; `lake build AlgebraicGroups` checks the
aggregate import.
Build the native matrix-base-change producer and its persistent client with
`lake build AlgebraicGroupsTest.MatrixEndBaseChange`. The matrix/endomorphism
and literal-order compatibility clients are selected with
`lake build AlgebraicGroupsTest.MatrixEndAdditive AlgebraicGroupsTest.MatrixEndScheme`.
Their production dependencies are built automatically. Build the aggregate
`AlgebraicGroups` before an external client that imports the root library.

For the finite general linear group, first run `lake exe cache get` in the
pinned project. The focused production build is
`lake build AlgebraicGroups.GroupScheme.GeneralLinear`. The
regression client imports that focused native module rather than the aggregate;
build both with `lake build AlgebraicGroupsTest.GeneralLinear`.

For general linear groups of modules, after the matching `lake exe cache get`,
build the focused producers with `lake build
AlgebraicGroups.Algebra.GeneralLinearBaseChange
AlgebraicGroups.GroupScheme.GeneralLinearModule`. Then build `AlgebraicGroups`
before running the aggregate-import client with `lake env lean
AlgebraicGroupsTest/GeneralLinearModule.lean`, or include that registered root
in the ordinary no-target `lake build`. Each producer also supports a direct
module import without first importing the aggregate.

For the finite determinant character, after the matching cache fetch, run
`lake build AlgebraicGroupsTest.GeneralLinearDeterminant`. Its direct import is
`AlgebraicGroups.GroupScheme.GeneralLinearDeterminant`; the public definitions
and theorems are also available through the aggregate `AlgebraicGroups` import.
For the generic split-kernel object and the finite determinant product and
conjugation, build the focused clients with
`lake build AlgebraicGroupsTest.SplitKernelProduct AlgebraicGroupsTest.SplitKernelSemidirect AlgebraicGroupsTest.GeneralLinearDeterminantProduct AlgebraicGroupsTest.GeneralLinearDeterminantConjugation`
after the matching cache fetch. Their producers also have direct imports and
are registered in the aggregate; a focused build is not the required complete
default build/audit.

## References, credit and license

Mathematical background includes James S. Milne, *Algebraic Groups* (2017),
especially its algebraic-group and group-scheme constructions. The reusable
algebra, category and scheme APIs also build on mathlib. These are mathematical
references, not claims to reproduce all results of those sources or permission
to redistribute their text. No source book or scan is bundled here.

The collective credit **Formal Frontier Agents** supplements, rather than
replaces, individual project contribution roles:

- An original Formalization Worker B execution implemented the upper-unitriangular
  coordinate algebra, group scheme and ordinary-import examples; a distinct
  Formalization Worker A execution independently reviewed the isolated proof
  bodies. A separate Formalization Worker B execution assembled the original
  modules with other library work, and a distinct Formalization Worker A
  execution reviewed that assembly's affected API. Another Formalization
  Worker B execution prepared this destination transfer. A further independent
  Formalization Worker A execution reviewed the exact destination candidate,
  followed by Lattice's code acceptance. Lattice prepared this documentation-only
  release-readiness update. These agent roles are not human review, and origin,
  destination and release review remain distinct.

- A later original Formalization Worker B execution authored the unitriangular
  affine-geometry producer and 21-example client; a distinct Formalization Worker
  A execution independently reviewed the isolated mathematical proof and API.
  A separate Worker B execution transferred the original bodies and examples
  with only their public imports changed. A fresh Worker A execution independently
  reviewed the exact destination transfer, followed by Lattice's code acceptance
  and protected integration. The present documentation-only release preparation
  is by a further Worker B execution; isolated, destination and release reviews
  are distinct. No human review or geometry-release acceptance is asserted.

- Lattice developed and integrated group-object, group-scheme and algebraic
  infrastructure, including earlier source-repository research later adapted
  into this library. For example, Lattice's clopen-rank localization research
  at `0d458dab6abd4471e73fce57c2be5765049f8b87` preceded the library's
  `AlgebraicGroups/Scheme/ClopenAffine.lean` introduction at
  `7ce1bb8bd8959570164eb99096596adca1e18aed`. Earlier proof development and
  later assembly are distinct contributions, even when made by the same agent.
- Separate Formalization Worker A and Worker B executions supplied mathematical
  implementations and independent non-author development reviews. One concrete
  original implementation is the monoid-algebra primitive theorem introduced
  at `53e53ec2a448afe4f935e6d4288193c46cfe8b09` by Worker A; these pooled
  identities do not denote one continuing author or imply self-review.
- Anchor supplied shared-maintainer integration for identity-component
  pullback, characteristic-morphism, Artin--Schreier and roots-of-unity
  compatibility contributions. Integration is not presented as authorship of
  the underlying Worker A/B implementations.
- Mathlib and the separately declared project libraries retain their own
  contributors, licenses and notices. Their imported results are not claimed
  as new proofs authored in this repository.
- Chris Birkbeck's 2021 mathlib diagonal determinant witness remains attributed
  in the determinant-section module with its Apache-2.0 notice. The section
  implementation was authored by Worker B Task
  `hive-request-9ffbaad315526c874f02794cd7703b651684de4b`
  (UID `d3cbeed7-b61a-4986-91cb-9d01e64e4166`); the finite SL implementation
  by Worker A Task `hive-request-99fde7b6c0eb62b8dd5dfc29ce25e565d111b50b`
  (UID `34333f62-8d3b-49c8-bd8e-13dbf969e1db`). Worker B Task
  `hive-request-0e7110fd5786b2d754dc8860768facd89f7ac80a`
  (UID `ae076404-5b1e-4cac-84a6-ab129a7c5337`) prepared this destination
  transfer. These are contribution roles, not source-author endorsement.
- Finite-free SL(V) module functor implementation and its client were authored by
  Worker B Task `hive-request-1ce56ef08640ec6a13b8bf1b2109825745c97ff2` (UID
  `60082129-cd44-4809-8b70-88f24a495825`) and independently reviewed by
  Worker A Task `hive-request-ced4ffe3612c04650bdc8fd5ea33c38281f94616` (UID
  `95f4ca5c-071f-437b-92a0-f434bfce7d05`). The module reuses Antoine
  Chambert-Loir's native special-linear-group API from mathlib.
- Finite GL/SL coordinate and `Spec` smoothness and its client were authored
  by Worker A Task `hive-request-a5e6c90d8ec39f1e9fa69dab1ca73e6f793e8dfd` (UID
  `9d7acf51-7653-4b52-a05e-c0cd9d9599e0`). Their origin acceptance and
  independent review are separate from this destination transfer. Worker B
  Task `hive-request-77410a8f9682982b27001cf7ada17cb054f4b479` (UID
  `512c720d-9ced-444e-ae00-adfd93ed9c63`) prepared the destination transfer;
  its completed destination review, integration and earlier release remain
  distinct from the origin acceptance and from this new release candidate.
- The earlier finite GL/SL geometric-integrality investigation was by Worker B
  Task `hive-request-4694e54904a86ba5cd23a09f174650df4ec77484` (UID
  `62aa584a-e574-4ca7-bf87-d5548e0cd712`). The geometric-integrality
  mathematics and client were authored by Worker B Task
  `hive-request-902e3e18b35d53eb4fd3b421954a339ef7741dd5` (UID
  `8c21821f-f9ac-4e4b-80b6-b1452edb4276`), reusing the earlier Worker A
  normalization section credited above. The finite GL/SL dimension research
  was by Worker B Task `hive-request-495409ddb864bb2a4c42d577e7ee9d2b19e474d5`
  (UID `b4c67a11-087b-42ac-bfa7-55dcc856c070`); its helper, dimensions
  and client were authored by Worker B Task
  `hive-request-020720d1eb5fc515621730cc4e303793d7178919` (UID
  `add4b4bc-9720-4317-9f70-308e77b22c36`). Both mathematical origins
  were accepted in the incubator. A distinct Worker B Task
  `hive-request-81805fb1290c8839628802cab794e0fdec6df0a4` (UID
  `26e301d0-dc56-4edc-8708-d41b7f543dbe`) prepared this source-only
  import/client-namespace transfer without changing the proofs. Independent
  Worker A Task `hive-request-2811b0c87b969db9f7708cfd5ac00e63ca785513`
  (UID `92620a93-8c41-477e-acff-c33eb2b4e642`) approved that original
  source-only transfer at `ca1a807ac2b00959fd9c6c496d48700c2f5a92c8`,
  not the combined assembly. Native job 533, fresh independent affected review
  and owner code acceptance now cover the exact combined destination snapshot;
  its separate independent release acceptance and publication completed at
  `28a1288c1eae8c7230f89c0b165415304fbd0f98`. That completed predecessor release
  did not itself accept the separately completed coordinate/group successor
  release, and neither release publishes the present geometry contribution.
- Separate Worker B executions authored the split-kernel product and finite
  determinant-product producers and their ordinary-import clients. A Worker B
  execution prepared their import/namespace normalization for this library;
  authorship of the two original proofs remains distinct from that transfer.
  Both origins have separate owner acceptance records. Independent destination
  mathematical and API review is distinct from the original proof reviews;
  destination integration, final release acceptance and publication remain
  separate exact-revision decisions.
- Distinct Worker B executions authored the original split-kernel conjugation
  and finite determinant-conjugation producers and clients. A further Worker B
  execution prepared their import/namespace normalization for this library;
  independent source-only review covers that original transfer. Their separately
  accepted 125-module destination predecessor has native job 530 and an
  independent affected review; the accepted 130-module union has native job 533
  and fresh affected review. Neither acceptance is release publication.

The full [LICENSE](LICENSE) supplies Apache-2.0 for original Formal Frontier
contributions, including verified earlier original project research adopted
here. Reused or adapted third-party expression retains its applicable terms
and notices. The collective author label does not identify a legal copyright
holder, and neither AI generation nor Git authorship establishes ownership or
clearance. The project-origin header correction replaces the unsupported holder
template with no-holder Apache-2.0 notices and credits Formal Frontier Agents;
it does not certify redistribution of the final artifact or its reachable history.
The detailed origin and review
records are maintained separately from this user-facing library documentation.

[formalization.yaml](formalization.yaml) records format-v0.4 scope, bibliography,
AI involvement and development-review status. Exact-candidate verification,
independent release/rights acceptance and publication are distinct lifecycle
records; no such status follows merely from that file or this README.
