# Mathematical topic guide

This catalog describes selected reusable APIs, their hypotheses and limitations.
For a shorter entry point use the [headline results](../README.md#headline-results);
focused guides explain the most involved constructions. Source-specific
passage correspondence is maintained separately.


## Vector groups, matrix groups and functors

Milne, *Algebraic Groups* (2017), items 2.1 and 2.6–2.7, gives the additive,
chosen-basis vector and additive-matrix antecedents. The field/basis
`Gₐ^n ≃ Vₐ` of item 2.6 directly precedes the finite additive product;
the arbitrary-ring underlying over-scheme comparison does not identify
group schemes or Hopf algebras. Mathlib's symmetric-algebra, affine `Spec`
and categorical product APIs supply the formal foundations; see the
[vector product](../AlgebraicGroups/GroupScheme/VectorProduct.lean) and
[additive-product comparison](../AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace.lean).

- `AlgebraicGeometry.affineSpecHomOverEquiv` and
  `additiveGroupHomOverEquiv` classify affine-target maps and additive
  coordinates by global sections of *any* over-scheme over a commutative
  ring. `additiveGroupAffineProductFan_isLimit` identifies the polynomial
  affine scheme with the underlying *literal* categorical finite product of
  additive group schemes. `additiveGroupProductUnderlyingSpecIso` preserves
  actual projections and `additiveGroupProductUnderlyingAffineSpaceIso`
  compares the underlying product with affine space, even for empty indices
  and zero rings. These are underlying over-scheme, not group/Hopf, results;
  see the [finite-product guide](../AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace/README.md).
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
  identify the scheme action on every commutative test algebra with the
  additive End/matrix point comparison and formal polynomial evaluation.
  `endMatrixSchemeBasisChangeIso` compares two bases as a native group-scheme
  isomorphism; its points agree with `endMatrixBasisChangeIso`. All finite-index
  APIs allow an empty basis and a zero test algebra. `Multiplicative` tags
  additive groups; none of these is the multiplicative End monoid or `GL(V)`.

## Closed unitriangular stages

Milne, *Algebraic Groups* (2017), item 2.9 and Definition 6.34,
Remark 6.35, Example 6.36 and §6.49, supplies the field-base
unitriangular group and one-entry central-filtration antecedents. The
arbitrary-ring [closed stages](../AlgebraicGroups/GroupScheme/UnitriangularStages.lean)
and [whole-superdiagonal coordinate maps](../AlgebraicGroups/GroupScheme/UnitriangularStageCoordinates.lean)
use Mathlib's quotient Hopf algebras, affine group schemes and categorical
products; the underlying [affine-space comparison](../AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace.lean)
does not turn its coordinate algebra equivalence into a Hopf equivalence.

- At positive stage `hr : 1 ≤ r`,
  `unitriangularStageCoordinateMap_underlying_spec` equates the *whole*
  underlying arrow with the scheme projection from surviving-coordinate
  affine space onto the current superdiagonal. Its coordinate-ring pullback
  goes from current-variable polynomials into the stage ring;
  `stageProductCoordinatePullback_X` identifies the images of the generators.
  In the opposite direction, `stageProductSectionPullback_higher` describes
  the section's ring pullback, which sends higher variables to zero. The equality
  `unitriangularStageCoordinateSectionOver_comp` gives a section of the
  underlying arrow over `Spec K`, not a group-scheme section. Rank/empty
  index and zero-ring edges are allowed. See the
  [projection guide](../AlgebraicGroups/GroupScheme/UnitriangularStageProjectionBridge/README.md).
- `UnitriangularStageCoordinateRing.ideal K n r` kills exactly the strict-upper
  entries with `j.val < i.val + r`. Its genuine Hopf quotient
  `CoordinateRing K n r` represents the closed group scheme
  `AlgebraicGeometry.unitriangularStageScheme K n r` over `Spec K`.
  `unitriangularStageSuccessor` embeds stage `r + 1` into stage `r` as a
  group-object closed immersion, and `unitriangularStagePointsIso` compares
  native matrix stages with represented group-valued points for every
  commutative coefficient algebra. See the
  [closed-stage guide](../AlgebraicGroups/GroupScheme/UnitriangularStages/README.md).
- `UnitriangularStageCoordinateRing.polynomialEquiv K n r` presents that
  *actual* stage quotient as `MvPolynomial (SurvivingPair n r) K`. Surviving
  entries map to variables, forbidden entries to zero, and inverse variables
  map back to quotient entries. This is a `K`-algebra equivalence, not a Hopf
  equivalence; see the
  [polynomial guide](../AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md).
- `AlgebraicGeometry.unitriangularStageUnderlyingAffineSpaceIso K n r`
  identifies the underlying stage scheme with affine space on surviving
  indices *over* `Spec K`, with forward and inverse `Spec.preimage` readbacks.
  It is not an isomorphism with a product of additive group schemes. The
  [affine-space guide](../AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace/README.md)
  records the exact scope and boundary cases. Ordinary-import examples are
  registered under `AlgebraicGroupsTest/GroupScheme` and
  `AlgebraicGroupsTest/Algebra`.
- `AlgebraicGeometry.unitriangularStageInclusion_normal K n r` gives native
  normality of the closed stage for all `n,r` over any commutative ring.
  `unitriangularStageConjugation` is an actual over-scheme conjugation factor,
  with inclusion and all-algebra point equations; it is not a product-group
  homomorphism. See the [normality guide](../AlgebraicGroups/GroupScheme/UnitriangularStageNormality/README.md).
- For `1 ≤ r`, `AlgebraicGeometry.unitriangularStageCoordinateMap K n r hr`
  is the genuine group-scheme map from the stage to the categorical product of
  additive group schemes indexed by its `r`-th superdiagonal. Primitive
  bialgebra coordinates give all-algebra point and naturality equations and
  `unitriangularStageCoordinateMap_successor_zero`; there is no `r = 0` map.
  See the [coordinates guide](../AlgebraicGroups/GroupScheme/UnitriangularStageCoordinates/README.md).
- `AlgebraicGeometry.unitriangularStageCoordinateMap_isPullback K n r hr`
  identifies the positive-stage successor with the underlying over-scheme
  fiber above the product's unit, using an ideal equality and universal
  algebra/scheme factorization. It asserts neither a quotient nor a
  group-homomorphic section. See the [kernel guide](../AlgebraicGroups/GroupScheme/UnitriangularStageKernel/README.md).

## General and special linear geometry

Milne, *Algebraic Groups* (2017), items 2.8–2.9, describes finite matrix
groups over fields; §2.42 gives the field-base `SL` domain argument. His
*Basic Theory of Affine Group Schemes* (2012), XI §16, Example 16.3 gives
the positive-rank field-base dimension of `SL`,
and XIII §3, item 3.14 gives a field-base determinant splitting with the
diagonal factor on the right. The arbitrary-base
[determinant-product comparison](../AlgebraicGroups/GroupScheme/GeneralLinearDeterminantProduct.lean)
instead uses a chosen pivot and section-first left normalization as an
underlying over-scheme isomorphism, not a Hopf or direct-product group
isomorphism. Mathlib's matrix groups, affine Hopf `Spec` and Krull-dimension
results underpin the [finite GL construction](../AlgebraicGroups/GroupScheme/GeneralLinear.lean)
and [GL/SL dimension formulas](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension.lean).

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
  see its [guide](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md).
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
  [guide](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md).
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
  claimed. See its [guide](../AlgebraicGroups/GroupScheme/GeneralLinearDeterminantProduct/README.md)
  and `AlgebraicGroupsTest.GeneralLinearDeterminantProduct`.
- `AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation` restricts
  diagonal conjugation to the genuine determinant-one kernel, as an arrow over
  `Spec K`. Its affine point formula works over every commutative `K`-algebra;
  diagonal entries are units before coercion and inversion. A chosen pivot
  excludes rank zero, while rank one and zero rings are allowed. The underlying
  product iso has section-first twisted multiplication, not a canonical
  direct-product group-scheme law. See its
  [guide](../AlgebraicGroups/GroupScheme/GeneralLinearDeterminantConjugation/README.md)
  and `AlgebraicGroupsTest.GeneralLinearDeterminantConjugation`.

## Localization, descent and finite projective algebra

The Stacks Project, tags [03BH](https://stacks.math.columbia.edu/tag/03BH),
[03BI](https://stacks.math.columbia.edu/tag/03BI),
[03BJ](https://stacks.math.columbia.edu/tag/03BJ) and
[03BM](https://stacks.math.columbia.edu/tag/03BM), motivates the invariant
rank and integrality arguments for finite locally free relations; the
[rank-stratum](../AlgebraicGroups/Scheme/EquivalenceRelationRank.lean) and
[integrality](../AlgebraicGroups/Scheme/EquivalenceRelationIntegrality.lean)
modules record their exact scope. Mathlib supplies flatness, localization
and finite-free presentation interfaces; the conditional
[affine relation bridge](../AlgebraicGroups/Scheme/AffineRelationQuotient.lean)
does not establish quotient effectivity from finite locally free hypotheses.

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
  polynomial in [finite-projective Fredholm](../AlgebraicGroups/LinearAlgebra/FiniteProjective/Fredholm.lean):
  its independence proof uses Mathlib's rectangular Weinstein--Aronszajn
  identity `Matrix.det_one_sub_mul_comm`, `Matrix.charpolyRev` and a
  finite-free split presentation. The [characteristic-polynomial module](../AlgebraicGroups/LinearAlgebra/FiniteProjective/Charpoly.lean)
  credits Stacks [03BH](https://stacks.math.columbia.edu/tag/03BH) and
  [03BJ](https://stacks.math.columbia.edu/tag/03BJ) for the invariant-norm
  and Cayley--Hamilton context; its coefficient-invariance lemma is
  conditional, not a proof of general groupoid invariance. It does not
  construct or specialize fixed-degree exterior-power
  base change: that API remains an upstream mathlib responsibility, while the
  `projective-modules` exterior-algebra, projectivity, determinant,
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

## Representability, group schemes and quotient constructions

Milne, *Algebraic Groups* (2017), items 1.4–1.5 and Appendix A.33,
motivates functors of points and subgroup transport;
Definition 5.20, Propositions 5.24–5.25 and Theorem 5.28 / B.37 supply
field-base quotient antecedents. The
[finite-type point functor](../AlgebraicGroups/GroupScheme/FiniteTypePoints.lean)
reuses SchemeProperties' restricted Yoneda API, while the
[relative fppf quotient](../AlgebraicGroups/GroupScheme/QuotientSheaf.lean)
uses Mathlib's site and sheafification APIs. Its recognition of a *supplied*
fppf quotient target is not an existence proof; local fppf surjectivity
does not assert surjectivity at every test object.

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
- Generic finite-type point functors have their canonical home in
  `SchemeProperties.FiniteTypePoints`, publicly reexported by
  [`AlgebraicGroups.GroupScheme.FiniteTypePoints`](../AlgebraicGroups/GroupScheme/FiniteTypePoints.lean).
  The group-valued extension keeps its existing declaration names and hypotheses.
  Ordinary public imports of both libraries coexist in the
  [combined client](../AlgebraicGroupsTest/FiniteTypePointsCoexistence.lean).
  Its finite-type essential-image proof uses the public Scheme equations
  `AlgebraicGeometry.algebraicOverPoints_eq` and
  `AlgebraicGeometry.algebraicOverInclusion_obj` to identify the point functor
  on a finite-type scheme with restricted Yoneda on its underlying
  locally-finite-type scheme. No cross-package `import all` is needed;
  updating the Scheme pin still requires checking the group extension and
  its ordinary-import clients.
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
  [guide](../AlgebraicGroups/GroupObject/SplitKernelProduct/README.md) and
  `AlgebraicGroupsTest.SplitKernelProduct`, which includes a concrete
  nonmultiplicative-section example.
- `CategoryTheory.splitKernelConj` is the pullback-defined conjugation of an
  actual group-object kernel by an arbitrary underlying-object section. A
  multiplicative section additionally gives the internal left-action laws and
  the explicit section-first twisted multiplication for the underlying-object
  product iso; no direct-product group-object isomorphism is asserted. See its
  [guide](../AlgebraicGroups/GroupObject/SplitKernelSemidirect/README.md) and the
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

## Dimension, components and density

Milne, *Algebraic Groups* (2017), Propositions 1.34 and 1.52 and §2g,
Proposition 2.37, precedes the identity-component and component-map
constructions; item 2.3 concerns finite constant groups. Definition 1.15,
Proposition 1.16 and Corollary 1.18 precede schematic density of points.
The [identity component](../AlgebraicGroups/GroupScheme/IdentityComponent.lean)
and [component map](../AlgebraicGroups/GroupScheme/ComponentSchemeMap.lean)
reuse Mathlib's connectedness and group-object APIs and SchemeProperties'
connected-component coproducts; the
[density criterion](../AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean)
builds on Mathlib's scheme-theoretic dominance. These are conditional
group-scheme constructions and do not supply the residual quotient
`G⁰/(G_red)⁰`. The smooth-locus density argument uses Stacks
[056V](https://stacks.math.columbia.edu/tag/056V) and
[030W](https://stacks.math.columbia.edu/tag/030W) and Mathlib's
perfect-field dense-locus proof; see
[geometric reducedness](../AlgebraicGroups/Scheme/GeometricallyReduced.lean).

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
