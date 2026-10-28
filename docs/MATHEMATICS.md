# Mathematical topic guide

This catalog describes selected reusable APIs, their hypotheses and limitations.
For a shorter entry point use the [headline results](../README.md#headline-results);
focused guides explain the most involved constructions. Source-specific
passage correspondence is maintained separately.


## Guide directory

- [Coalgebras and comodules](COALGEBRAS.md): finite containment, intrinsic
  coefficients, counit ideals, group-like elements and API walkthroughs.
- [Roots of unity](#roots-of-unity-at-all-orders): all-order coordinates,
  finite properties and pointwise rank over commutative bases.
- [Vector groups](#vector-groups-matrix-groups-and-functors),
  [closed stages](#closed-unitriangular-stages),
  [unitriangular base change](#unitriangular-base-change),
  [triangular coordinates and geometry](#triangular-geometry-and-coordinates)
  and [GL/SL](#general-and-special-linear-geometry).
- [Antipodes](#antipode-involutivity),
  [localization and descent](#localization-descent-and-finite-projective-algebra),
  [quotients](#representability-group-schemes-and-quotient-constructions),
  [components and density](#dimension-components-and-density).
- [Building and focused targets](BUILDING.md); [credits and references](../CREDITS.md).

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
  ring. `additiveGroupAffineProductFanIsLimit` identifies the polynomial
  affine scheme with the underlying *literal* categorical finite product of
  additive group schemes. `additiveGroupProductUnderlyingSpecIso` preserves
  actual projections and `additiveGroupProductUnderlyingAffineSpaceIso`
  compares the underlying product with affine space, even for empty indices
  and zero rings. These are underlying over-scheme, not group/Hopf, results;
  see the [finite-product guide](../AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace/README.md).
- `(TauCeti.AdditiveGroup.pointsMulEquiv (R := K) (M := M) (A := A)).symm` identifies linear maps into any
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

The rank-three stage-two quotient retains the `(0,2)` entry; exhausted stages,
empty ranks and zero rings remain allowed. Its polynomial presentation is not
an additive-group or Hopf identification. The underlying projection and section
are in the [projection module](../AlgebraicGroups/GroupScheme/UnitriangularStageProjectionBridge.lean).

## Unitriangular base change

The comparisons use `TauCeti.UpperUnitriangular.coordinateHopfAlgebra` directly,
a polynomial algebra on strict upper pairs with its canonical Hopf structure.
There is no external GL-quotient model or old-to-new comparison.

- [Algebra base change](../AlgebraicGroups/Algebra/UnitriangularBaseChange/README.md)
  supplies the arbitrary-commutative-base tensor comparison and all-entry laws.
- [Hopf base change](../AlgebraicGroups/Algebra/UnitriangularHopfBaseChange/README.md)
  preserves coproduct, counit and antipode, including the rank-three cross term.
- [Algebra coherence](../AlgebraicGroups/Algebra/UnitriangularBaseChangeCoherence/README.md)
  and [scheme coherence](UnitriangularSchemeBaseChangeCoherence.md) identify
  identity and scalar-tower comparisons with canonical tensor and pullback maps.
- [Scheme base change](UnitriangularSchemeBaseChange.md) compares the actual
  pulled-back group object with the canonical group scheme over the new base.

Same-universe commutative bases, finite linearly ordered indices, empty ranks
and zero rings are allowed; no flatness or injectivity assumption is added.
The focused guides preserve the original method and contributor credits.

## Triangular geometry and coordinates

The group schemes are canonical Tau Ceti models: `SplitTorus.groupScheme`,
`GeneralLinear.UpperTriangular.groupScheme` and `UpperUnitriangular.groupScheme`.
Upper-triangular scheme results use numerical rank `N` and native `Fin N`
matrices, covering every finite rank including zero. Native arbitrary-index
matrix group mathematics uses `TauCeti.upperTriangularGroup` and
`TauCeti.upperUnitriangularGroup`; the diagonal projection takes values in
unit tuples. There are no parallel diagonal or triangular coordinate models.

- [Finite triangular geometry](../AlgebraicGroups/GroupScheme/FiniteTriangularGeometry/README.md)
  gives smooth structure morphisms and geometrically integral fibers over
  arbitrary commutative bases; total spaces are integral over domains.
- [Diagonal dimension](../AlgebraicGroups/GroupScheme/DiagonalDimension/README.md)
  presents the canonical group algebra on `Multiplicative (ι →₀ ℤ)` as a
  polynomial localization and computes field dimension `card ι`.
  [Upper-triangular dimension](../AlgebraicGroups/GroupScheme/UpperTriangularDimension/README.md)
  gives the canonical retained-coordinate presentation and field dimension
  `N + N.choose 2`. Empty ranks and zero-ring algebra presentations are included.
- [Coordinate elimination](../AlgebraicGroups/Algebra/LocalizedCoordinateQuotient/README.md)
  remains independent. Localization dimension uses canonical
  `TauCeti.ringKrullDim_localization_away`; a supplied nonvanishing point is
  sufficient, but need not exist over every finite field.
- [Split kernels](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md)
  identify the actual diagonal identity fiber with the unitriangular group.
  [U-first products](../AlgebraicGroups/GroupScheme/UpperTriangularSchemeProduct/README.md)
  give `U ⊗ D ≅ T` as underlying schemes. Forward multiplication is `i(u)e(d)`;
  conjugation scales `(i,j)` by `dᵢ dⱼ⁻¹`, and the product has the U-first
  semidirect law rather than the direct-product group law.
- [Diagonal products](../AlgebraicGroups/GroupScheme/DiagonalProduct/README.md)
  prove the categorical product of copies of canonical `Gₘ` against every
  test scheme, including the empty terminal case.
- [Point-group series](../AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
  and [exact class](../AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md)
  extend the canonical unitriangular carrier and filtration with stronger
  lower-central, derived, quotient and exponent results under their stated
  hypotheses.

These relative assertions allow arbitrary commutative and zero bases. Field
dimension is separate from arbitrary-base integrality; the represented product
assertions do not claim normality of `U` in all of `GL`.

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

The canonical GL and SL coordinate Hopf algebras and group schemes are
`TauCeti.GeneralLinear.coordinateHopfAlgebra/groupScheme` and
`TauCeti.SpecialLinear.coordinateHopfAlgebra/groupScheme`. The finite native
index extension uses rank `Fintype.card n` and existing matrix reindexing:
`TauCeti.GeneralLinear.reindexedGenericMatrix`, `reindexedPointsMulEquiv`,
and the corresponding special-linear point API. The represented indexed
functors are `generalLinearIndexedFunctor` and `specialLinearIndexedFunctor`.
All commutative bases and coefficient algebras, empty indices and zero rings
remain permitted; there is no duplicate localization or GL/SL scheme model.

`SpecialLinearCoordinateRing.polynomialEquiv` retains the independent
all-entry determinant-one polynomial presentation of the canonical SL algebra.
`generalLinearDeterminantSchemeCoordinateMap` defines the actual character
from the canonical lifted-integer Gm coordinate algebra, and
`generalLinearDeterminantSchemeHom` has the native unit-valued determinant
point formula. A chosen pivot gives `generalLinearDeterminantSectionSchemeHom`,
including explicit coordinate, affine-point and nonaffine-test formulas.
`SpecialLinearKernel` identifies the canonical SL inclusion as this determinant
kernel by a ring pushout, scheme and group-scheme pullbacks, and unique lifts
from arbitrary scheme or group-scheme tests. Rank zero is included in the
kernel statement; the section requires an actual pivot.

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
- [Smoothness](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearSmooth.lean)
  uses canonical GL/SL smooth coordinate algebras and retains the chosen-pivot
  normalization section and smooth structure morphisms. The normalization
  splits an algebra map, rather than a Hopf map.
- [Integral geometry](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md)
  retains the SL domain result over arbitrary integral bases, integral total
  spaces for GL and SL over domains, and geometrically integral structure
  morphisms over every commutative base, using canonical scalar extension.
- [Field dimensions](../AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md)
  are `N ^ 2` and `N ^ 2 - 1`, with natural subtraction before casting and
  rank zero explicit. Canonical Mathlib/Tau Ceti height and localization
  theorems replace the removed local rational-point-height helper.

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

- **Infinite vector-space dimension of general linear coordinates.** Over any
  field `K` and nonempty finite decidable index type `n`, the powers of any
  universal matrix entry are linearly independent. Thus the determinant-localized
  coordinate algebra `TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)`
  is not module-finite over `K`.
  This is vector-space nonfiniteness, not merely carrier infinitude or a
  ring/scheme Krull-dimension assertion; the empty-index coordinate algebra is
  the base field. See the [dimension API](../AlgebraicGroups/Algebra/GeneralLinearCoordinateRing/Dimension.lean)
  and [rational GL₂ example](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsGL2Infinite.lean).

## Antipode involutivity

For a full Hopf algebra over a commutative semiring, either commutative
multiplication or cocommutative comultiplication suffices for the all-element
identity `S² = id`. These are two sufficient alternatives, not a
characterization and not a requirement that both hold. The scalar and algebra
universes are independent. Neither branch needs a field, additive inverses,
finiteness, flatness or nontriviality; neither asserts involutivity for an
arbitrary noncommutative Hopf algebra without cocommutativity.

## Antipodes of commutative Hopf algebras

For a commutative semiring `R` and a commutative semiring Hopf algebra `A`
over `R`, `TauCeti.HopfAlgebra.antipode_antipode` states the pointwise
involutivity identity and removes two successive antipodes. Import the focused
[antipode module](../AlgebraicGroups/Algebra/HopfAlgebra/Antipode.lean).
The proof uses Mathlib's convolution group of algebra endomorphisms and
involutivity of group inversion; it requires neither cocommutativity nor
finiteness, additive inverses or nontriviality. Commutativity of `A` is a
hypothesis of this named theorem; the cocommutative alternative below uses a
different argument. The [ordinary-import examples](../AlgebraicGroupsTest/Algebra/HopfAlgebra/Antipode.lean)
include arbitrary finite sums in the infinite group algebra `ℕ[ℤ]`, a
basis element whose antipode differs from itself, zero-ring scalars and the
matrix coordinates of `GL₂` over `ℚ`.

## Antipodes of cocommutative Hopf algebras

For `R : Type u` and `A : Type v`, the hypotheses are exactly
`[CommSemiring R] [Semiring A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]`.
Thus multiplication in `A` may be noncommutative; cocommutativity is the
identity `τ ∘ Δ = Δ` for its comultiplication. In the same focused
[antipode module](../AlgebraicGroups/Algebra/HopfAlgebra/Antipode.lean),
`HopfAlgebra.antipode_involutive_of_isCocomm` proves
`Function.Involutive (HopfAlgebra.antipode R)`, and the pointwise simp lemma
`HopfAlgebra.antipode_antipode_of_isCocomm` gives `S(S(a)) = a` for every
`a : A`, not only group-like or basis elements. These are theorems for full
Hopf algebras, not structures specifying only a comultiplication and counit.

The proof uses convolution on linear endomorphisms, rather than the
commutative branch's convolution group of algebra endomorphisms.
Postcomposing `S ⋆ id = 1` by `S`, antipode antimultiplicativity together
with tensor symmetry and cocommutativity gives `S ⋆ S² = 1`. Comparing
this with `id ⋆ S = 1` by uniqueness of left and right inverses yields
`S² = id`. The formalization uses Mathlib's
[Hopf convolution API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/HopfAlgebra/Convolution.lean)
for antimultiplicativity and antipode inverse identities, its
[linear convolution API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Coalgebra/Convolution.lean)
for multiplication and the unit, and its coalgebra and tensor-map APIs for
cocommutativity and symmetry. The producer's References credit these
Mathlib providers and their contributors, as well as `WithConv` and
inverse uniqueness.

The [cocommutative clients](../AlgebraicGroupsTest/Algebra/HopfAlgebra/CocommutativeAntipode.lean)
apply the theorem to arbitrary elements of `ℕ[S₃]`, using Mathlib's canonical
group-algebra Hopf and cocommutative structures. The basis elements of the
adjacent transpositions `(0 1)` and `(1 2)` have unequal products, so this
algebra genuinely has noncommutative multiplication. Generic clients obtain
bijection and elementwise identities from involutivity; the same group
algebra over `ZMod 1` supplies a zero-ring boundary. The finite group is an
example, not a finiteness hypothesis, and the natural-number scalars show
that additive inverses are not needed.

## Bialgebra maps and antipodes

- **Antipode compatibility of bialgebra maps.** Every bialgebra homomorphism
  between Hopf algebras over a commutative semiring commutes with their
  antipodes; the algebras need not be commutative or have additive inverses.
  See the [homomorphism API](../AlgebraicGroups/Algebra/HopfAlgebra/Hom.lean)
  and [semiring group-algebra examples](../AlgebraicGroupsTest/Algebra/HopfAlgebra/Hom.lean).
  The [comultiplication API](../AlgebraicGroups/Algebra/HopfAlgebra/Comultiplication.lean)
  gives the complementary identity `Δ ∘ S = (S ⊗ S) ∘ τ ∘ Δ` for every Hopf
  algebra over a commutative semiring, without cocommutativity or commutative
  multiplication; [examples](../AlgebraicGroupsTest/Algebra/HopfAlgebra/Comultiplication.lean)
  use natural-number group algebras and `GL₂` coordinates.

## Antipodes and comultiplication

For a commutative semiring `R` and a possibly noncommutative semiring Hopf
algebra `A`, `TauCeti.HopfAlgebra.antipode_comul_antidistrib` states
`Δ ∘ S = (S ⊗ S) ∘ τ ∘ Δ`. The pointwise simp lemma
`TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply` rewrites `Δ(S(x))`. Import the focused
[comultiplication module](../AlgebraicGroups/Algebra/HopfAlgebra/Comultiplication.lean).
Neither cocommutativity nor additive inverses, finiteness or nontriviality is
assumed; the scalar and algebra universes are independent. The flip `τ` is
essential even for commutative algebras such as the coordinates of `GL₂`.
The proof compares left and right convolution inverses of `Δ`, contracting
balanced fourfold tensors by coassociativity, antipode and counit laws.
The [examples](../AlgebraicGroupsTest/Algebra/HopfAlgebra/Comultiplication.lean)
use arbitrary finite sums over `ℕ`, a noncommutative symmetric-group algebra,
and products of arbitrary `GL₂` coordinates over `ℚ`.

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
- `CategoryTheory.EquivalenceRelation.isLimitCompositionFst` gives the
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
- Canonical `LinearMap.projectiveCharpolyRev` is the presentation-independent
  Fredholm polynomial of a finite projective module endomorphism. The retained
  [characteristic-polynomial module](../AlgebraicGroups/LinearAlgebra/FiniteProjective/Charpoly.lean)
  proves ordinary characteristic-polynomial comparisons, monicity and
  Cayley–Hamilton after reflection under constant local-rank hypotheses, and
  supplies the conditional coefficient-invariance integrality argument.
  The original split-presentation independence method uses Mathlib's rectangular
  Weinstein–Aronszajn identity `Matrix.det_one_sub_mul_comm` and
  `Matrix.charpolyRev`; that foundation now comes from Tau Ceti.
  Stacks [03BH](https://stacks.math.columbia.edu/tag/03BH) and
  [03BJ](https://stacks.math.columbia.edu/tag/03BJ) retain the invariant-norm
  and Cayley–Hamilton credit. The coefficient-invariance lemma is conditional;
  it does not prove general groupoid invariance. Exterior-power base change
  remains canonical Mathlib mathematics, separate from this argument.
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
- `FrobeniusTwistedLine.groupScheme`: the characteristic-`p` affine group
  scheme cut out by `Y^p - tX^p`. When `t` is not a `p`-th power, its
  coordinate ring is a reduced domain, while an explicit nonzero nilpotent
  after adjoining a `p`-th root proves that it is not geometrically reduced.
- `FrobeniusTwistedLine.baseChangeNormalForm`: after adjoining `α` with
  `α^p = t`, its scalar-extended coordinate ring is explicitly equivalent to
  `L[W,X]/(W^p)`. The equivalence sends `X` to the free line coordinate and
  `Y - αX` to `W`; forward and inverse coordinate equations expose the
  order-`p` thickening directly.
- `TauCeti.leftTranslation`: left translation by a point is an
  isomorphism of a group object; its point action, unit image, and composition
  laws are exposed directly. The retained translation module adds the
  extra unit/composition formulas and additive translation API.
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

## Roots of unity at all orders

Import [RootsOfUnity](../AlgebraicGroups/GroupScheme/RootsOfUnity.lean). The
canonical scheme is `TauCeti.RootsOfUnityGroup.groupScheme K n`; its character
group is `ULift (Multiplicative (ZMod n))`, with coordinate algebra
`MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup n)`. The lift keeps
the group in the scheme universe. There is no second cyclic coordinate model.
`rootsOfUnityPointsIso` gives native roots of unity naturally in coefficient
algebras. Canonical `TauCeti.RootsOfUnityGroup.adjoinRootEquiv` describes the
positive-order polynomial presentation, and canonical character relabelling
handles its universe lift.

At zero, every unit is a root and the canonical scheme is the multiplicative
group. Its Laurent presentation differs from the degenerate polynomial
quotient by `T^0 - 1`. This zero-order extension goes beyond the positive-order
formulation in Milne's *Algebraic Groups* (2017), item 2.4.

### Finite properties and usage

`rootsOfUnityCoordinate_finitePresentation` gives algebra finite presentation
at every order. `rootsOfUnityScheme_flat` and
`rootsOfUnityScheme_locallyOfFinitePresentation` apply to the actual canonical
structure map at every order. At positive order, `rootsOfUnityScheme_isFinite`
and `rootsOfUnityScheme_finrank` give finiteness and pointwise rank `n`.
No field, Noetherian or invertibility-of-`n` hypothesis is added. The coordinate
basis is Mathlib’s canonical group-algebra basis on the lifted cyclic group.

The pointwise scheme rank is not a count of field-valued roots. Numerical
module finrank needs its usual nontriviality assumptions; over the zero ring
the indexed basis still exists but the spectrum has no points. At zero order,
algebra finite presentation and flatness remain, without a finiteness or
rank-zero assertion. No bundled finite-locally-free morphism class or general
finite-flat-to-finite-presentation implication is asserted.

### Standard examples and limits

The [root client](../AlgebraicGroupsTest/RootsOfUnity.lean) retains the
nonidentity order-zero rational unit `2`. The
[translation client](../AlgebraicGroupsTest/InfinitesimalAdditiveTranslation.lean)
uses the canonical coordinate algebra of `μ₂` over `𝔽₂`, with its nonzero
square-zero element `U - 1`, rank two and all five finite properties.
Translation `U = 1 + T` identifies underlying algebras and schemes with the
infinitesimal additive presentation, but not Hopf algebras or group schemes.
The [nonisomorphism theorem](../AlgebraicGroups/GroupScheme/InfinitesimalAdditiveNonisomorphism.lean)
retains the positive-height obstruction. These results make no claim about
Tate modules or torsion of abelian varieties.

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
