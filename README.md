# Algebraic groups

Reusable Lean definitions and theorems about matrix groups, affine group
schemes and their coordinate algebras. This library is organized by mathematics,
not by any one source. Its finite triangular and classical-group constructions
build on mathlib and separately maintained project libraries. Results described
below are present in this tree; documentation alone does not certify the
independent review, complete proof audit or official publication of a successor
release. Source-specific coverage is tracked outside this library.

Authors: Formal Frontier Agents. Original project contributions use
[Apache-2.0](LICENSE); see [credits and references](CREDITS.md) for contributor,
third-party and AI involvement.

## Headline results

- **Native closed unitriangular stages.** The actual quotient by forbidden
  strict-upper entries is a Hopf algebra over any commutative base, with
  closed stage and successor group-scheme arrows and multiplicative point
  equivalences over every coefficient algebra. Its quotient is also a
  polynomial `K`-algebra on surviving entries; the underlying scheme is
  affine space *over* `Spec K`, without asserting an additive-group or Hopf
  isomorphism. Rank-three/stage-two retains `(0,2)`, and zero rings, empty
  ranks and exhausted stages are allowed. See the
  [closed-stage guide](AlgebraicGroups/GroupScheme/UnitriangularStages/README.md),
  [polynomial guide](AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md)
  and [underlying affine-space guide](AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace/README.md).
- **Unitriangular group-scheme identity and tower coherence.** The native
  one-step base-change map agrees with the canonical pullback identity unit
  and direct-to-iterated scalar-tower compositor. An ordinary-import `Fin 2`
  client checks the inverse coordinate through both routes. See the
  [standalone group-scheme coherence guide](docs/UnitriangularSchemeBaseChangeCoherence.md).
- **Native unitriangular group-scheme base change.** Over arbitrary same-universe
  commutative rings and finite linearly ordered indices, the actual pulled-back
  unitriangular group object is isomorphic to the group scheme over the new
  base. The forward map and base projection have readbacks; an ordinary-import
  `Fin 3` client retains the group-product cross term. See the
  [standalone scheme base-change guide](docs/UnitriangularSchemeBaseChange.md).
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

- **Unitriangular point-group series.** Over an arbitrary commutative ring,
  superdiagonal subgroups of native finite unitriangular matrix groups give
  central and lower-central series, successive additive quotients, a derived
  series and sharp nilpotency bounds under the guides' stated hypotheses. In
  prime characteristic the exponent results have their own coefficient and
  size conditions. See the [point-group guides](AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
  and [exact-class guide](AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md).
- **Finite general and special linear schemes.** Over any field, the actual
  coordinate rings and affine schemes have dimensions `N²` and `N² - 1`
  respectively, with subtraction in naturals before casting (rank zero has
  dimension zero in both cases). See [dimension](AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md)
  and [geometric-integrality](AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md)
  for exact assumptions and related geometry.

The represented-product assertions are over the fixed base `Spec K`; they assert
neither a global transported group-object instance, arbitrary-base change,
normality of `U` in `GL`, nor source-specific coverage. The finite triangular
geometry and dimension above are separately scoped results.

## Modules and examples

Import `AlgebraicGroups` for the aggregate or a focused producer linked above.
Ordinary-import clients under `AlgebraicGroupsTest` exercise representative
statements on generic rings and boundary cases. For a starting path, use
[unitriangular scheme base change](docs/UnitriangularSchemeBaseChange.md),
[its identity/tower laws](docs/UnitriangularSchemeBaseChangeCoherence.md),
[closed unitriangular stages](AlgebraicGroups/GroupScheme/UnitriangularStages/README.md),
[stage polynomial coordinates](AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md),
[stage underlying affine space](AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace/README.md),
[represented upper-triangular products](AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md),
[the split kernel](AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md),
[finite diagonal products](AlgebraicGroups/GroupScheme/DiagonalProduct/README.md)
and [native matrix groups](AlgebraicGroups/GroupTheory/UpperTriangular/README.md).
For a broader survey of additional algebra, component and quotient APIs, see
the [mathematical topic guide](docs/MATHEMATICS.md). These focused guides and
the topic guide give declarations, proofs and limitations without requiring
private preparation records.

## Use and build

The repository pins Lean `v4.34.0-rc2` and exact official GitHub dependencies in
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json). Access to separately maintained
private dependencies may be needed until they are made public. At the project
root, after installing the pinned toolchain, fetch the matching precompiled
mathlib cache successfully **before** building both targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

See [building and focused targets](docs/BUILDING.md) for dependency and
client details. This is a reproduction recipe, not a report of running it on
this documentation candidate. Mathematical background and rights notices are
in [credits](CREDITS.md); [formalization.yaml](formalization.yaml) lists the
metadata and result declarations for this tree.
