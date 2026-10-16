# Algebraic groups

Lean definitions and theorems about matrix groups, affine group schemes and their
coordinate algebras, and coalgebras. The library builds on Mathlib and separately
maintained project libraries; it does not claim to formalize an entire source.

## Headline results

### Coalgebras and Hopf algebras

- **Group-like elements and scalar extension.** The counit-one and tensor-square
  equations are preserved by extension of commutative semirings and reflected by
  faithfully flat extension of commutative rings, requiring only weak coalgebra
  data. The full group-like predicate has corresponding corollaries, with no
  flatness or finiteness assumption on the coalgebra module.
  [Module](AlgebraicGroups/Algebra/Coalgebra/GroupLikeBaseChange.lean).
- **Tensor products of coalgebra morphisms.** For a commutative `R`-algebra `S`,
  an `S`-linear coalgebra map and an `R`-linear coalgebra map induce an `S`-linear
  map on tensor products over `R`. Only `CoalgebraStruct` on independently
  universed additive-monoid modules is needed; identity and composition are
  respected, with a bridge to the full-law tensor map.
  [Module](AlgebraicGroups/Algebra/Coalgebra/TensorProduct.lean).
- **Tensor products of coalgebra quotients.** For coideals in modules with weak
  coalgebra structures over a commutative ring, the sum of the two tensor relation
  images is a coideal. Mathlib's linear comparison refines to a coalgebra
  equivalence on the canonical quotients, with representative formulas, a
  quotient-map square and unique factorization of maps vanishing on the relation
  sum. No flatness or coalgebra-law hypothesis is needed.
  [Module](AlgebraicGroups/Algebra/Coalgebra/TensorProductQuotient.lean),
  [integer product example](AlgebraicGroupsTest/Algebra/Coalgebra/TensorProductQuotient.lean).
- **Coalgebra morphism range constructions.** Over a field, `CoalgHom.range`
  equips exactly the underlying linear-map range with the restricted coalgebra;
  `CoalgHom.rangeRestrict` uses codomain restriction to that carrier. The source
  needs only `AddCommMonoid`, `Module` and `CoalgebraStruct`; the target has an
  additive commutative group and a full coalgebra. No source coalgebra laws or
  finite-dimensionality assumptions are used. The characteristic membership,
  evaluation and unique-factorization laws are stated alongside the constructions.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Hom.lean),
  [infinite monoid-algebra example](AlgebraicGroupsTest/Algebra/Coalgebra/MonoidAlgebraCollapse.lean).
- **Coideal quotient morphisms.** Over a commutative ring, coalgebra morphisms
  vanishing on a coideal descend uniquely; maps preserving coideals induce
  quotient maps respecting identity and composition. Additive-group modules with
  `CoalgebraStruct` suffice, in independent universes; no coalgebra laws, flatness,
  projectivity or field hypothesis. [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean).
- **Kernels with a flat quotient.** Over a commutative ring, the kernel of a
  linear map preserving comultiplication and counit is a coideal when the target
  module and the ordinary module quotient by the kernel are flat. No
  surjectivity or coalgebra laws are required.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean).
- **Coideal generator criterion.** Over a commutative ring, the span of an
  arbitrary set in an additive-group module with `CoalgebraStruct` is a coideal
  iff the counit and `(q ⊗ q) ∘ Δ` vanish on every generator, where `q` is the
  ordinary module quotient map by that span. Scalar and module universes are
  independent; no coalgebra laws, field, flatness, finiteness or nonemptiness are
  required. [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean).
- **Kernels over a field.** The linear kernel of any coalgebra morphism is a
  coideal, without surjectivity. Both source and target need only
  `CoalgebraStruct` on additive-group modules, in independent universes; no
  coalgebra laws or finite-dimensionality hypothesis is required. The field
  makes the quotient by the kernel flat; flatness of the ambient modules alone
  is not sufficient over general commutative rings.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean),
  [noninjective, nonsurjective example](AlgebraicGroupsTest/Algebra/Coalgebra/MonoidAlgebraCollapse.lean).
- **Finite subcoalgebras.** Over a field, every finitely generated subspace or
  finite subset of a coalgebra lies in a finite-dimensional subcoalgebra, with
  restricted coalgebra laws, bundled inclusion and unique morphism factorization.
  No ambient finite dimension, algebra/Hopf structure or least finite closure is
  assumed. [Modules and example](docs/COALGEBRAS.md#subcoalgebras-and-finite-containment-over-a-field).
- **Subcoalgebra images.** Over a field, injectivity of a coalgebra map only on
  a subcoalgebra gives an equivalence with its image, preserving and reflecting
  module-finiteness and finite generation. Ambient equivalences transport these
  carriers as an ordinary `Equiv`, not an order isomorphism; no ambient finiteness.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Equiv.lean).
- **Finite right subcomodules.** Over a commutative semiring, for additive-monoid
  modules, projectivity of the coacting coalgebra alone gives finite-subset
  containment in finitely generated subcomodules. Neither module need be finite,
  nor the coacted-on module projective. Flatness of the coacting coalgebra suffices
  for unique subtype coactions from image stability and unique colinear
  factorization; the counit need not be onto. [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean).
- **Carrier transport of right comodules.** For a specified right `C`-comodule
  `X` and an `R`-linear equivalence `e : V ≃ₗ[R] W`, `X.transport e` is a lawful
  right `C`-comodule on the given target module. The coalgebra stays fixed:
  its coaction at `w` is `(e tensor id_C) (X.coaction (e.symm w))`, changing
  only the first tensor factor. The constructor and its two coaction formulas
  work over commutative semirings on additive-commutative-monoid modules in
  independent universes, without flatness or finiteness. A full coherence or
  comodule-morphism transport API is not asserted here.
  [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Transport.lean).
- **Intrinsic coefficients.** Coefficient spans exist over commutative semirings.
  Over a field they form a subcoalgebra: unique full corestriction of a coaction
  to `D` on the **same module** is equivalent to coefficient-span containment in
  `D`. No ambient finite dimension is needed; module-finiteness of the comodule
  gives module-finite coefficients, not algebra finite generation.
  [Module and GL₂ model](docs/COALGEBRAS.md#intrinsic-coefficient-coalgebras).
- **Finite tensor-image containment.** Over a commutative semiring, a projective
  coalgebra's finite subsets lie in finitely generated `U` with `Δ(U)` in the
  image of `U ⊗ C`; over a field one obtains `D ⊗ D`. These are module, not
  algebra, finiteness assertions, with no ambient finiteness; semiring carriers
  need only additive monoids. [Module](AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean).
- **Algebra-generating coefficient matrices.** A finite-type, possibly
  noncommutative semiring algebra over a field, with a coalgebra on its canonical
  module, has a finite square matrix satisfying `Δ(aᵢⱼ) = Σₖ aᵢₖ ⊗ aₖⱼ` and
  `ε(aᵢⱼ) = δᵢⱼ`, whose entries generate the algebra. Size zero is allowed; no
  module-finiteness or multiplicative compatibility is required.
  [Module](AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean).
- **Counit ideals.** Over a commutative semiring, an idempotent principal ideal
  has coalgebra `Δ(d) = d ⊗ e`, with inclusion counit, including `e = 0, 1`.
  Any coalgebra's counit range is idempotent and acts with `I • ⊤ = ⊤`;
  tensor ranges multiply and the tensor counit is onto iff both factor counits
  are onto, already for BOTH `CoalgebraStruct`s on additive-monoid modules over
  a commutative semiring in independent universes. Scalar extension maps the
  range ideal. No surjectivity, freeness or finite generation is assumed. Over a commutative
  ring, an additive-group coalgebra is faithfully flat **iff flat and its counit
  is onto**; flatness is separate, with no projectivity or nontriviality required.
  [Modules and proper-range examples](docs/COALGEBRAS.md#idempotent-principal-ideal-coalgebras).
- **Hopf coefficient matrix units.** Over a commutative semiring, any finite
  square coefficient matrix in a possibly noncommutative semiring Hopf algebra,
  with the coproduct and counit equations above, is a unit with entrywise
  antipode as two-sided inverse, **without transpose**; empty indices are allowed.
  [Module](AlgebraicGroups/Algebra/Coalgebra/CoefficientMatrixUnit.lean).
- **Group-like cardinality and maps.** For a torsion-free coalgebra over a
  commutative domain, group-likes have cardinality at most module rank; rank
  below `ℵ₀` gives finiteness and a `finrank` bound, in particular for module-finite
  coalgebras, without freeness or a field. Separately, over any commutative
  semiring, normalized group-likes in additive-commutative-monoid modules
  correspond to scalar-source coalgebra maps by `g ↦ (r ↦ r • g)` and evaluation
  at `1`, without multiplication or nontriviality. `GroupLike.map` along
  coalgebra morphisms respects identity and composition, and this correspondence
  is natural. For possibly noncommutative semiring bialgebras,
  `BialgHom.groupLikeMap` induces a monoid homomorphism with the same laws,
  without Hopf structure. In possibly noncommutative semiring Hopf algebras,
  Mathlib's `GroupLike.toUnits` is injective, has image exactly the units with
  group-like underlying values, and commutes with `Units.map` under bialgebra
  morphisms, pointwise and as monoid homomorphisms. Mathlib provides the carrier,
  monoid/group structures, unit construction and antipode identities; this
  library adds transport maps and characterization/naturality laws. These
  transport and unit results allow independent universes, with no finiteness
  or nontriviality assumptions.
  [Cardinality](AlgebraicGroups/Algebra/Coalgebra/GroupLikeCardinality.lean),
  [coalgebra maps](AlgebraicGroups/Algebra/Coalgebra/GroupLikeHom.lean),
  [bialgebra maps](AlgebraicGroups/Algebra/Bialgebra/GroupLike.lean),
  [Hopf units](AlgebraicGroups/Algebra/HopfAlgebra/GroupLike.lean).
  For full coalgebras on additive-group modules over a commutative semiring,
  group-like differences are ordered skew primitives; see
  [the theorem and ordinary-permutation clients](docs/COALGEBRAS.md#ordered-group-like-differences-and-translations).
- **Group-like coalgebra coordinates.** Over a commutative semiring, arbitrary
  families of group-like elements in additive-commutative-monoid module coalgebras correspond
  to coalgebra maps from the free diagonal monoid-algebra coalgebra; the index needs
  no monoid structure. Over a field, evaluation is a coalgebra equivalence onto the
  group-like span, with diagonal coproduct and counit equal to the coefficient sum.
  No target multiplication, finite dimension or nonempty group-like family is required.
  [Extension](AlgebraicGroups/Algebra/Coalgebra/MonoidAlgebra.lean),
  [span coordinates](AlgebraicGroups/Algebra/Coalgebra/GroupLikeCoordinates.lean).
- **Monoid-algebra bialgebra maps.** Over a commutative semiring `R`, monoid
  homomorphisms `M →* GroupLike R A` correspond by an explicit equivalence to
  bialgebra maps `R[M] →ₐc[R] A`, for any monoid `M` and full `R`-bialgebra `A`.
  The target semiring may be noncommutative; no Hopf structure, finiteness or
  nontriviality is required. Evaluation, uniqueness and naturality laws describe
  the equivalence in independent scalar, monoid and target universes.
  [Module](AlgebraicGroups/Algebra/Bialgebra/MonoidAlgebra.lean).
- **Group-like coordinates.** In a coalgebra with a basis of group-like elements
  over a commutative semiring, an element is group-like exactly when distinct
  coordinates have product zero and their finite-support sum is one. Coordinate
  idempotence follows from these conditions; the basis index need not be finite.
  The canonical monoid-algebra criterion needs no monoid structure on its index
  type and agrees with Mathlib's monomial classification over commutative domains.
  [Basis coordinates](AlgebraicGroups/LinearAlgebra/Coalgebra/GroupLikeCoordinates.lean),
  [coefficients](AlgebraicGroups/Algebra/Coalgebra/GroupLikeCoefficients.lean).
- **Antipodes.** For full Hopf algebras over a commutative semiring, either
  commutative multiplication **or** cocommutative comultiplication suffices for
  `S² = id`; these are alternatives, not an iff or simultaneous requirements.
  Neither branch needs additive inverses, finiteness or nontriviality. Bialgebra
  maps commute with antipodes, and `Δ ∘ S = (S ⊗ S) ∘ τ ∘ Δ` holds without
  either commutativity assumption. [Involutivity](AlgebraicGroups/Algebra/HopfAlgebra/Antipode.lean),
  [maps](AlgebraicGroups/Algebra/HopfAlgebra/Hom.lean),
  [comultiplication](AlgebraicGroups/Algebra/HopfAlgebra/Comultiplication.lean).

### Matrix groups and group schemes

- **Roots of unity at all orders.** Over any commutative base ring, the cyclic
  group algebra `K[ZMod n]` represents the roots-of-unity functor for every
  natural `n`. At zero it is the Laurent Hopf algebra and its group scheme is
  canonically the existing multiplicative group; positive orders retain the
  polynomial presentation `K[T]/(T^n - 1)`. The coordinates are free with basis
  indexed by `ZMod n`. At positive order the structure morphism is finite, flat
  and locally of finite presentation, with pointwise scheme rank `n`, without
  requiring `n` to be invertible. Algebra finite presentation, flatness and local
  finite presentation hold also at order zero; no finiteness or rank-zero claim
  is made there. The zero-order extension is beyond Milne's positive-order
  item 2.4.
  [Module](AlgebraicGroups/GroupScheme/RootsOfUnity.lean),
  [API and rank conventions](docs/MATHEMATICS.md#roots-of-unity-at-all-orders),
  [rational-unit model](AlgebraicGroupsTest/RootsOfUnity.lean),
  [nonreduced second roots over `𝔽₂`](AlgebraicGroupsTest/InfinitesimalAdditiveTranslation.lean).
- **Connected group schemes.** A connected group scheme of finite type over any
  field is geometrically irreducible, even without reducedness. If it is also
  geometrically reduced, it is geometrically integral. Finite type is expressed
  by local finite type and quasi-compactness; no properness, perfectness or
  separate separatedness hypothesis is needed.
  [Module](AlgebraicGroups/GroupScheme/GeometricallyIntegral.lean),
  [multiplicative-group examples](AlgebraicGroupsTest/GroupScheme/GeometricallyIntegral.lean).
- **Finite additive products.** Over any commutative ring, the underlying
  over-scheme of the literal finite product of additive group schemes is affine
  space, preserving projections and the universal property against all schemes.
  Empty indices and zero rings are allowed; no group/Hopf isomorphism is asserted.
  [Module](AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace.lean).
- **Closed unitriangular stages.** Over any commutative ring, native finite
  stage quotients are Hopf algebras with closed stage/successor group-scheme
  arrows and multiplicative points over every coefficient algebra. Their
  polynomial coordinates identify the underlying schemes with affine spaces
  over the base, **not** additive groups or Hopf algebras; zero rings, empty ranks
  and exhausted stages are included. [Modules and guides](docs/MATHEMATICS.md#closed-unitriangular-stages).
- **Stage normality, coordinates and kernel.** All stages are normal subgroup
  objects with conjugation and matrix-point readbacks. For `1 ≤ r`, primitive
  superdiagonal coordinates define `S_r → Gₐ^J`, with successor its underlying
  fiber over the unit. The entire underlying arrow is an affine-space projection;
  setting higher variables to zero sections that arrow, **not** the group map.
  Zero rings and empty indices are allowed; no quotient or additive splitting.
  [Modules and guides](docs/MATHEMATICS.md#closed-unitriangular-stages).
- **Unitriangular base change.** For arbitrary same-universe commutative rings
  `R → S` and finite linearly ordered indices, scalar extension of the actual
  GL quotient is the quotient over `S`. The comparison preserves the independently
  given coproduct, counit and antipode and induces an isomorphism of the actual
  pulled-back group object. Identity and scalar-tower laws agree with tensor
  unit/cancellation and canonical pullback compositors (direct to iterated).
  Zero rings and empty indices are included, without flatness or injectivity.
  [Algebra modules](docs/MATHEMATICS.md#unitriangular-base-change),
  [scheme comparison](docs/UnitriangularSchemeBaseChange.md),
  [scheme coherence](docs/UnitriangularSchemeBaseChangeCoherence.md).
- **Triangular geometry and dimension.** Over any commutative ring, native
  multiplicative, finite diagonal and finite upper-triangular schemes are smooth
  with geometrically integral **fibers**; total spaces are integral over a domain.
  Empty indices and zero rings are included in the relative results. Over every
  field the actual diagonal and upper-triangular ring/scheme dimensions are `N`
  and `N + N.choose 2`. No arbitrary-base or general product-dimension formula.
  [Modules, retained indices and coordinate readbacks](docs/MATHEMATICS.md#triangular-geometry-and-coordinates).
- **Coordinate elimination.** Over any commutative ring, eliminating polynomial
  coordinates commutes with localization, even if the erased denominator is zero.
  Over a field with finitely many variables, a **supplied field-valued point**
  not annihilating the denominator gives full localization dimension; nonzero
  alone need not supply that point over a finite field. This is a limitation of
  the supplied-point hypothesis, not of the general nonzero-denominator formula.
  [Elimination](AlgebraicGroups/Algebra/LocalizedCoordinateQuotient/README.md),
  [dimension](AlgebraicGroups/Algebra/FinitePolynomialLocalizationDimension/README.md).
- **Represented triangular products.** Over any commutative ring, for finite
  same-universe linearly ordered indices, `U ⊗ D ≅ T` as schemes over `Spec K`.
  The forward map is `i(u)e(d)`; the inverse uses diagonal projection and column
  normalization. Conjugation on the actual identity fiber is `dᵢ uᵢⱼ dⱼ⁻¹`,
  and multiplication is `(u,d)(u',d') = (u α(d,u'), dd')`, **not** a direct-product
  group law. Readbacks allow all coefficient algebras, zero/nonreduced rings,
  empty indices and noninjective base maps. The diagonal projection splits with
  scheme-theoretic fiber `U`; for finite decidable same-universe indices, `D`
  is a product of `Gₘ`, including the empty terminal case. No global transported
  group instance, arbitrary-base change or normality of `U` in `GL` is asserted.
  [Modules and limits](docs/MATHEMATICS.md#triangular-geometry-and-coordinates).
- **Unitriangular point-group series.** Over a commutative ring, finite native
  unitriangular groups have central/lower-central series, successive additive
  quotients, derived series and sharp nilpotency bounds under the stated
  hypotheses. Prime-characteristic exponent results have separate coefficient
  and size conditions. [Series](AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md),
  [exact class](AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md).
- **GL and SL dimensions.** Over every field and finite decidable indices,
  the actual coordinate rings and affine schemes have dimensions `N²` and
  `N² - 1`, with natural subtraction before casting; rank zero gives zero in both.
  [Dimension](AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md),
  [related geometry](AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md).
- **Infinite vector-space dimension of GL coordinates.** Over a field and
  nonempty finite decidable indices, powers of any universal matrix entry are
  linearly independent, so the coordinate algebra is not module-finite. This
  is not just carrier infinitude or Krull dimension; empty indices give the field.
  [Module and GL₂ example](docs/MATHEMATICS.md#general-and-special-linear-geometry).

## Modules and examples

| Module / target | Contents |
| --- | --- |
| [`AlgebraicGroups`](AlgebraicGroups.lean) | Library aggregate; focused imports are linked above. |
| [`AlgebraicGroupsTest`](AlgebraicGroupsTest/) | Test library: ordinary-import clients and boundary examples. |
| [`AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport`](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Transport.lean) | Lawful carrier transport of specified right comodules with fixed coalgebra, and first-factor coaction formulas. |
| [`AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom`](AlgebraicGroups/Algebra/Coalgebra/GroupLikeHom.lean) | `GroupLike.map`, identity/composition, and naturality of the normalized group-like/scalar-source coalgebra-map equivalence over a commutative semiring; additive-commutative-monoid modules. |
| [`AlgebraicGroups.Algebra.Bialgebra.GroupLike`](AlgebraicGroups/Algebra/Bialgebra/GroupLike.lean) | Monoid homomorphism `BialgHom.groupLikeMap` with identity/composition laws for possibly noncommutative semiring bialgebras over a commutative semiring; no Hopf structure. |
| [`AlgebraicGroups.Algebra.HopfAlgebra.GroupLike`](AlgebraicGroups/Algebra/HopfAlgebra/GroupLike.lean) | Injectivity, image characterization and pointwise/monoid-homomorphism `Units.map` naturality of Mathlib's `GroupLike.toUnits` for possibly noncommutative semiring Hopf algebras over a commutative semiring. |
| [`AlgebraicGroups.Algebra.Bialgebra.MonoidAlgebra`][bialg-monoid] | Group-like map equivalence. |
| [`AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra`](AlgebraicGroups/Algebra/Coalgebra/MonoidAlgebra.lean) | Universal extension of group-like families and diagonal structural formulas. |
| [`AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates`](AlgebraicGroups/Algebra/Coalgebra/GroupLikeCoordinates.lean) | Group-like-span subcoalgebra and structure-preserving coordinates over a field. |

[bialg-monoid]: AlgebraicGroups/Algebra/Bialgebra/MonoidAlgebra.lean

The [coalgebra guide](docs/COALGEBRAS.md) gives API walkthroughs and models;
[mathematical topics](docs/MATHEMATICS.md) cover vector groups, triangular groups,
localization, quotients, components and density, with focused module/guide links.

## Use and build

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "algebraic-groups"
git = "https://github.com/FormalFrontier/algebraic-groups.git"
rev = "main"
```

GitHub `main` contains reviewed releases; Lake records the resolved commit in
`lake-manifest.json`. Use a commit from that history to pin a particular release.
Import `AlgebraicGroups` or a focused module linked above. For example:

```lean
import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
#check HopfAlgebra.antipode_involutive
```

Lean `v4.34.0-rc2` and exact GitHub dependencies are pinned in
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json). Direct requirements are Mathlib,
SchemeProperties, GeneralLinearGroups and CoherentModules; building requires
access to them.
At the root, install the pinned toolchain and fetch the matching cache **before**
building both library and test targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

See [building and focused targets](docs/BUILDING.md) for dependency/resource details
and [formalization metadata](formalization.yaml) for result declarations.

## References

Selected antecedents are Sweedler's *Hopf Algebras* (1969), Milne's *Algebraic
Groups* (2017) and distinct 2012/2015 notes, the Stacks Project, and the prior
formalizations in Mathlib and project dependencies. [References and scope](CREDITS.md#mathematical-sources)
give precise locators, qualifications and further sources; none asserts whole-source coverage.

## Credits and license

Authors: Formal Frontier Agents. AI agents developed the proofs and examples under
human project direction, reusing Mathlib and project libraries. Group-like coalgebra
coordinates combine Mathlib's diagonal coalgebra and linear-independence APIs with
this library's span-closure and restricted-subcoalgebra constructions. Original project
contributions use [Apache-2.0](LICENSE). [CREDITS.md](CREDITS.md) preserves contributor
roles, mathematical-method credit and authentic third-party notices separately
from redistribution rights.
