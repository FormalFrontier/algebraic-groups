# Algebraic groups

Lean definitions and theorems about matrix groups, affine group schemes and their
coordinate algebras, and coalgebras. The library builds on Mathlib and separately
maintained project libraries; it does not claim to formalize an entire source.

## Headline results

### Group objects

- **Family translations.** For a given group object `G` in any Cartesian
  monoidal category and any family `i : P → G`, the shears
  `(p, g) ↦ (p, i(p)g)` and `(g, p) ↦ (gi(p), p)` are isomorphisms of
  underlying objects. No group structure on `P` or multiplicativity of `i`
  is required. Projection and generalized-pair formulas, inverse/unit/composition
  laws and naturality preserve the noncommutative multiplication order.
  [Construction and factorization](AlgebraicGroups/GroupObject/FamilyTranslation.lean).
- **Ordered commutator word maps.** For a given group object in any Cartesian
  monoidal category, a supplied fan indexed by `Fin n × Fin 2` determines the
  ordered product of its `n` commutators. The API gives evaluation on arbitrary
  generalized points, the empty and single-pair formulas, naturality under
  monoid morphisms, and invariance under appending a unit pair. A limiting
  target fan supplies the extension and gives inclusion of generalized-point
  ranges. For any supplied limiting fans with `n + 1` pairs, a generalized point
  lies in the ordinary commutator subgroup exactly when it is a value of one
  of these words. No compatibility between fans or subgroup-image assertion
  for an individual word map is required.
  [Construction and completeness](AlgebraicGroups/GroupObject/CommutatorWord.lean).
- **Conjugacy of stabilizers.** For a given internal group action in a Cartesian
  monoidal category, an arbitrary group section `g` induces
  `ModObj.stabilizerConjIso x g` between the original chosen stabilizers of `x`
  and `g • x`. Only these two pullbacks are required. The inclusion squares,
  inverse, all-test conjugation formulas and precomposition naturality retain
  the original action. Over a scheme, both orbit-fibre projections and all test
  schemes are retained, with no reducedness or other geometric hypothesis.
  [Internal construction](AlgebraicGroups/GroupObject/StabilizerConjugacy.lean),
  [scheme specialization](AlgebraicGroups/GroupScheme/StabilizerConjugacy.lean).
- **Group structure on a monoid kernel.** In any Cartesian monoidal category,
  let `G` be a group object, `H` and `N` monoid objects, and `f : G → H` and
  `i : N → G` monoid morphisms. A supplied pullback of `f` along the unit of `H`
  with legs `i` and `N → 𝟙` gives `GrpObj.ofIsPullback f i hPB : GrpObj N`,
  retaining exactly the supplied monoid structure. Its characteristic API gives
  that equality, the original projection as a group-object morphism, its underlying
  map, and compatibility with inversion. This constructs kernel group structures
  without a group target or global pullbacks; the
  [integer-product example](AlgebraicGroupsTest/GroupObjectKernel.lean) has a proper
  nontrivial kernel and a non-group target.
  [Construction](AlgebraicGroups/GroupObject/Kernel.lean).
- **Inversion criterion.** For a group object in a Cartesian monoidal category,
  commutativity is equivalent to inversion being a monoid morphism. The braiding
  is explicit and unique in this setting. This is a categorical extension of the
  inversion criterion used in Milne, *Abelian Varieties*, proof of Corollary 1.4.
  [Criterion](AlgebraicGroups/GroupObject/Commutative.lean),
  [integer and permutation models](AlgebraicGroupsTest/GroupObject/Commutative.lean).
- **Trivial-kernel criterion.** A morphism from a group object to a monoid object
  in any Cartesian monoidal category is mono exactly when the canonical unit-to-fibre
  pullback lift is an isomorphism. The supplied fibre needs no group structure or
  global finite-limit hypothesis. For schemes this is the scheme-theoretic fibre,
  not a geometric-point test.
  [Criterion](AlgebraicGroups/GroupObject/KernelTorsor.lean),
  [proper `S₃ → S₃ × C₂` inclusion and monoid boundary](AlgebraicGroupsTest/GroupObject/TrivialKernel.lean).

- **Kernel pairs of group-to-monoid morphisms.** In a Cartesian monoidal
  category, let `G` be a group object, `Q` a monoid object and `q : G → Q` a
  monoid morphism. For any kernel pullback `N → G` over the unit of `Q`, the
  kernel-pair statement identifies `N × G` with `G ×_Q G` by
  `(n, g) ↦ (i(n)g, g)`. No group structure on `N`, inverse operation on `Q`
  or global finite-limit hypothesis is required.
  [Statement](AlgebraicGroups/GroupObject/KernelTorsor.lean).
  `GrpObj.isPullback_kernel_mul` uses this supplied `N` and `i` without a
  monoid structure on `N` or a multiplicativity condition on `i`.

### Coalgebras and Hopf algebras

- **A finitely presented rank-one nonflat coalgebra over a PID.** For any
  field `K`, put `R = K[X]`, `T = R/(X²)` and give `C = R ⊕ T`
  (implemented as `TrivSqZeroExt R T`) its primitive `R`-coalgebra structure.
  Then `C` is finitely presented of cardinal module rank one, has the nonzero
  torsion element `(0, [1])` killed by nonzero `X²`, and is not `R`-flat.
  Its `R`-group-like elements are equivalent to `K`, with parameter `k`
  represented by `(1, [Polynomial.C k * X])`. They are infinite if `K`
  is infinite; finite fields are included in the equivalence. This extends
  the rational construction in *Finite generation and group-like elements*, §3.
  [Module results](AlgebraicGroups/Algebra/Coalgebra/PrimitiveExtension/Polynomial/Module.lean),
  [group-like classification](AlgebraicGroups/Algebra/Coalgebra/PrimitiveExtension/Polynomial/GroupLike.lean).
  More generally, finite presentation and cardinal rank one hold for any
  commutative coefficient ring, with Mathlib's rank convention even for the
  zero ring. Nonzero torsion and nonflatness require only nontriviality;
  the group-like family is injective over any commutative ring, and it is
  exhaustive over a reduced ring. Infinitude is deduced only under `Infinite K`.
- **Cofree specified right comodules.** For an arbitrary coalgebra `C` over a
  commutative semiring `R` and arbitrary `R`-modules in independent universes,
  `V ⊗[R] C` has its canonical cofree coaction. Colinear maps into it correspond
  `R`-linearly to ordinary linear maps into `V`, with both inverse laws,
  naturalities and triangles. Every specified coaction gives a colinear injective
  map into this cofree comodule, with a linear retraction; colinearity of that
  projection is not asserted. At `V = R` the left unitor recovers the regular-target
  coefficient correspondence.
  [API](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Cofree.lean),
  [infinite natural-number diagonal use with proper range](AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule/Cofree.lean).
- **Coalgebra data on a linear range.** Over a commutative ring, let the source and
  codomain of a linear map be modules with additive commutative groups. If the source
  has weak coalgebra data and the kernel is a coideal, the linear range carries the
  quotient-transported data. The range restriction preserves counit and comultiplication;
  no coalgebra data on the codomain or full coalgebra laws on the source are required.
  [Construction and preservation](AlgebraicGroups/Algebra/Coalgebra/Range.lean).
- **Coideal annihilators and convolution subalgebras.** Over a commutative ring,
  the ordinary full-dual annihilator of a coideal contains the counit and is
  closed under convolution. These closure results require only `CoalgebraStruct`
  on an additive-group module, in independent universes; no coalgebra laws,
  projectivity, flatness or finite-dimensionality hypothesis is needed.
  With full `Coalgebra` laws, the annihilator defines a canonical subalgebra of
  `WithConv (Module.Dual R C)`, with membership and underlying-submodule API.
  [Module](AlgebraicGroups/Algebra/Coalgebra/DualAnnihilator.lean).
- **Coideals, cores and the complete lattice.** Over a commutative ring, an
  additive commutative group with a module structure and `CoalgebraStruct`,
  coideals bundle `Submodule.IsCoideal` and are ordered by inclusion. The greatest
  coideal contained in a submodule is right adjoint to inclusion; their Galois
  coinsertion induces a complete lattice. Joins and bottom have ambient submodule
  carriers; infima and top are cores, not generally ambient intersections or top.
  The rational natural-number-indexed group-like coalgebra has a nonzero proper
  counit kernel and a nonzero proper top-coideal carrier.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Coideal.lean),
  [example](AlgebraicGroupsTest/Algebra/Coalgebra/Coideal.lean).
- **Coideal scalar extension.** For commutative-ring algebras, extension of
  scalars preserves coideals; faithfully flat extension reflects them. Only
  `CoalgebraStruct` on the additive-group source module is needed, in independent
  universes: no field, finiteness, coalgebra laws or source/quotient-flatness.
  The canonical tensor datum and image carrier are Mathlib's; its quotient-based
  coideal predicate determines the ring/group boundary.
  [Module](AlgebraicGroups/Algebra/Coalgebra/BaseChange.lean),
  [one polynomial augmentation model](AlgebraicGroupsTest/Algebra/Coalgebra/CoidealBaseChange.lean)
  over `ℚ → ℚ[X]` on `AddMonoidAlgebra ℚ ℤ`, with nonzero proper carriers and
  a nonzero `X ⊗ (e₀ - e₁)` witness.
- **Automatic counit preservation.** Over a commutative semiring, a unital
  algebra map (`AlgHom`) from a Hopf algebra to a bialgebra that preserves
  comultiplication automatically preserves the counit. The algebras need not be
  commutative. [Module](AlgebraicGroups/Algebra/HopfAlgebra/Hom.lean).
- **Weak linear coefficient composition.** Over a commutative semiring `R`, let
  `C` and `M` be `R`-semimodules and let `Δ : C →ₗ[R] C ⊗[R] C` and
  `δ : M →ₗ[R] C ⊗[R] M` satisfy relative coassociativity. Arbitrary linear
  coefficients `α β : C →ₗ[R] A`, for a possibly noncommutative semiring
  `R`-algebra `A`, induce `A`-linear operators on `A ⊗[R] M`. Applying `α`
  first and `β` second combines coefficients as
  `(LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ)`: the outer
  coefficient `α` multiplies the inner coefficient `β` in that order. No
  multiplication on `C`, counit or multiplicativity of the coefficients is needed.
  [Composition theorem](AlgebraicGroups/Algebra/Coalgebra/CoefficientOperators.lean);
  the [matrix-unit example](AlgebraicGroupsTest/Algebra/Coalgebra/CoefficientOperators.lean)
  distinguishes the two orders.
- **Regular coefficient normalization and recovery.** Over a commutative semiring
  `R`, for arbitrary `R`-modules `M,N` and a linear map
  `F : M →ₗ[R] R ⊗[R] N`, conjugating its tensor extension by the left unitors
  gives `lid ∘ F`. This module-only
  [normalization API](AlgebraicGroups/LinearAlgebra/TensorProduct/Extension.lean)
  specializes to `F = (TensorProduct.map ell id) ∘ Δ`, giving
  `lid ∘ ell.rTensor C ∘ Δ` for arbitrary `Δ : C →ₗ[R] C ⊗[R] C` and
  `ell : C →ₗ[R] R`. If `C` is a coalgebra and `Δ` its registered
  comultiplication, postcomposition with the counit recovers `ell`. All scalar
  and module universes are independent; no multiplication on `C`, field,
  finiteness, flatness or projectivity is required.
  [Coefficient API](AlgebraicGroups/Algebra/Coalgebra/CoefficientOperators.lean).
- **Ordered rational matrix-point operators.** For arbitrary `U,V ∈ GL₂(ℚ)`
  with `(UV)₀₀ = 2` and `(VU)₀₀ = 1`, the two raw tensor-extended coefficient
  operator compositions differ. The points are the general-linear coordinate
  ring's multiplicative-equivalence images, and a supplied linear map is given
  equal to its registered comultiplication. The registered-counit readbacks,
  retaining both left unitors, are respectively `2` and `1`: applying `β`
  after `α` corresponds to `UV`, not `VU`.
  [Operators and readbacks](AlgebraicGroups/GroupScheme/GeneralLinearPointOperators.lean).
- **Scalar-extension characteristics.** Over a commutative semiring `R`, for any
  semiring `R`-algebra `A` and `R`-semimodule `M`, the tensor extension of a linear
  map `F : M →ₗ[R] A ⊗[R] M` is the identity exactly when `F(m) = 1 ⊗ₜ[R] m`.
  For a semiring `R`-algebra `C`, arbitrary linear `Δ : C →ₗ[R] C ⊗[R] C` and
  given `δ : M →ₗ[R] C ⊗[R] M`, relative coassociativity is equivalent to
  composition of the tensor-square operators for the ordered left and right
  inclusions. No commutativity of `A` or `C`, coalgebra structure or law on `Δ`
  is required. [Identity characteristic](AlgebraicGroups/LinearAlgebra/TensorProduct/Extension.lean),
  [tensor-square characteristic](AlgebraicGroups/Algebra/Coalgebra/CanonicalPointOperators.lean).
- **Canonical-point counit criterion.** For an `R`-bialgebra `C` over a
  commutative semiring `R` and an arbitrary linear map `δ : M →ₗ[R] C ⊗[R] M`,
  the counit law holds exactly when the tensor-extended operator at the convolution unit is the identity for
  every commutative coefficient algebra in `Type (max uR uC w)`. The module
  universe is independent of this tester universe; no coaction laws, flatness
  or injectivity of scalar extension are assumed. The bialgebra `C` need not
  be commutative, so the commutative-coordinate case follows by specialization.
  [Criterion](AlgebraicGroups/Algebra/Coalgebra/CanonicalPointOperators.lean),
  [zero-map boundary test](AlgebraicGroupsTest/Algebra/Coalgebra/CanonicalPointOperators.lean).
- **Canonical-point coassociativity and coaction-law criteria.** When the
  coordinate bialgebra `C` is commutative, a given left linear datum `δ` is
  coassociative exactly when applying the operator
  for `α` and then that for `β` gives the operator at the convolution product
  `α ⋆ β`, for all algebra points into every commutative coefficient algebra
  in `Type (max uR uC w)`. No counit law or bound on the module universe is
  required. The combined criterion pairs this composition law with the unit
  law, characterizing both coaction laws together.
  [Criteria](AlgebraicGroups/Algebra/Coalgebra/CanonicalPointOperators.lean),
  [non-coassociative boundary test](AlgebraicGroupsTest/Algebra/Coalgebra/CanonicalPointOperators.lean).
- **Scalar-extension postcomposition.** Over a commutative semiring `R`,
  extending an `R`-linear map `F : M →ₗ[R] N` to an `A`-linear map
  `A ⊗[R] M →ₗ[A] N` commutes with `A`-linear postcomposition when the target
  modules have compatible `R`- and `A`-actions. The scalar `R`-algebra `A` may
  be a noncommutative semiring; for commutative `A` the extension agrees with
  `LinearMap.liftBaseChange`.
  [API](AlgebraicGroups/LinearAlgebra/TensorProduct/Extension.lean).
- **Unit-counit normalization.** For a commutative semiring `R` and an
  additive-commutative-monoid `R`-module `C` carrying a full `Coalgebra R C`,
  an element with tensor-square comultiplication and unit counit is group-like.
  Scalar and carrier universes are independent; no multiplication on `C` is needed.
  [Module](AlgebraicGroups/Algebra/Coalgebra/GroupLike.lean).
- **Group-like elements and scalar extension.** The counit-one and tensor-square
  equations are preserved by extension of commutative semirings and reflected by
  faithfully flat extension of commutative rings, requiring only weak coalgebra
  data. The full group-like predicate has corresponding corollaries, with no
  flatness or finiteness assumption on the coalgebra module.
  [Module](AlgebraicGroups/Algebra/Coalgebra/GroupLikeBaseChange.lean).
- **Group-like elements of tensor products.** For full coalgebras over an arbitrary
  commutative semiring, normalized group-like elements of the tensor product
  correspond canonically to ordered pairs of group-like elements. The equivalence
  uses the two counit projections, has pure-tensor inverse values, and is natural
  under coalgebra morphisms. For bialgebras it is multiplicative, without requiring
  commutativity of the two bialgebras or nontriviality of the scalar semiring.
  [Coalgebra equivalence](AlgebraicGroups/Algebra/Coalgebra/GroupLikeTensorProduct.lean),
  [multiplicative equivalence](AlgebraicGroups/Algebra/Bialgebra/GroupLikeTensorProduct.lean).
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
- **Tensor products of subcoalgebras.** Over a field, the range of the tensor
  product of two subcoalgebra inclusions is spanned by the pure tensors from
  their factors. Membership is characterized by an arbitrary tensor preimage;
  containment in any submodule is equivalent to containment of those generators.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/TensorProduct.lean).
- **Surjective descent of coalgebra laws.** Coassociativity
  and both counitality laws descend over a commutative semiring from a coalgebra
  to a fixed `CoalgebraStruct` along a surjective `CoalgHomClass` map.
  `Coalgebra.ofSurjective` equips exactly that target structure with the laws;
  its parent, comultiplication and counit are unchanged, and it agrees with an
  existing full target structure. For a linear equivalence `e : D ≃ₗ[R] C`,
  `LinearEquiv.toCoalgEquiv` identifies the weak pullback data with the given data
  on `C`. From only `e` and a coalgebra on `C`, `Coalgebra.ofSurjective_coalgebra`
  uses its inverse morphism to recover exactly `e.coalgebra R`.
  Cocommutativity descends to the constructed coalgebra. The infinite semiring
  projection model uses the constructor; the nonsurjective zero-source boundary
  explains why surjectivity is needed. The negation example on `ℤ` distinguishes
  the pulled-back counit from the scalar counit on the same module.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Surjective.lean),
  [semiring example](AlgebraicGroupsTest/Algebra/Coalgebra/Surjective.lean).
- **Coideal quotient morphisms.** Over a commutative ring, coalgebra morphisms
  vanishing on a coideal descend uniquely; maps preserving coideals induce
  quotient maps respecting identity and composition. Additive-group modules with
  `CoalgebraStruct` suffice, in independent universes; no coalgebra laws, flatness,
  projectivity or field hypothesis. [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean).
- **Bialgebra quotient factorization.** Over a commutative ring `R`, let `A`
  be a possibly noncommutative ring and `B` a semiring, both full `R`-bialgebras.
  A bialgebra morphism `f : A →ₐc[R] B` factors canonically and uniquely through
  `A ⧸ I` for a two-sided ideal `I` contained in its ordinary ring kernel, with
  `I.restrictScalars R` a coideal. This uses Mathlib's fixed canonical quotient
  bialgebra and asserts uniqueness of the factor, not of quotient structures.
  [Module](AlgebraicGroups/Algebra/Bialgebra/Quotient.lean).
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
- **Surjective kernels.** Over a commutative ring, the linear kernel of a
  surjective coalgebra morphism is a coideal. Independent-universe additive-group
  modules with `CoalgebraStruct` suffice; no coalgebra laws or flatness assumption.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Quotient.lean).
- **Surjective first isomorphism.** Over a commutative ring, a surjective
  coalgebra morphism identifies its target with the quotient by its linear
  kernel, with the canonical quotient structure. Both independent-universe
  additive-group modules need only `CoalgebraStruct`; no coalgebra laws or flatness.
  Representative, inverse and linear-equivalence formulas characterize the map.
  [Module](AlgebraicGroups/Algebra/Coalgebra/FirstIsomorphism.lean).

- **Coideal correspondence.** For a surjective coalgebra morphism over a commutative
  ring, image and preimage give an order isomorphism between source coideals
  containing its linear kernel and target coideals. Only `CoalgebraStruct` is
  required; no coalgebra laws, flatness, field or finiteness assumption.
  [Module](AlgebraicGroups/Algebra/Coalgebra/CoidealCorrespondence.lean).

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
- **Supported diagonal subcoalgebras.** Over a field, for any index type and
  set `s`, `Finsupp.supportedSubcoalgebra K s` consists exactly of the finitely
  supported functions whose support lies in `s`, equivalently the span of the
  unit coordinate vectors indexed by `s`. Its API gives membership, span,
  coordinate inclusion and carrier-containment criteria. Finite `s` gives a
  finitely generated carrier and a module-finite subcoalgebra; neither the index
  type nor `s` need be finite for the construction.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Finsupp.lean),
  [diagonal examples](AlgebraicGroupsTest/Algebra/Coalgebra/SubcoalgebraDiagonal.lean).
- **Subcoalgebra images.** Over a field, injectivity of a coalgebra map only on
  a subcoalgebra gives an equivalence with its image, preserving and reflecting
  module-finiteness and finite generation. Ambient equivalences transport these
  carriers as an ordinary `Equiv`, not an order isomorphism; no ambient finiteness.
  [Module](AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Equiv.lean).
- **Algebra-valued tests for right-comodule stability.** Let `R` and `C` be
  commutative semirings, with `C` an `R`-algebra and a coalgebra on its canonical
  `R`-module, and let `X` be a specified right coaction on any additive-monoid
  `R`-module `M`. A submodule `U` is image-stable exactly when identity evaluation
  preserves `U.baseChange C`, the image of the tensor inclusion. Equivalently,
  every algebra-valued evaluation preserves `U.baseChange A`, for commutative
  `R`-algebras `A` in the compatible maximum of the coalgebra and tester
  universes. The forward implication permits an independently sized `A`.
  Evaluation is the stock scalar-extension lift of the commuted coaction;
  no flatness, bialgebra structure, finiteness, basis or tensor-inclusion
  injectivity is required. [Criteria and API](AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean).
- **Linear-coefficient evaluation of right coactions.** For a coalgebra `C`
  over a commutative semiring `K`, a specified right coaction on `V` and any
  linear map `φ : C →ₗ[K] A` to a commutative `K`-algebra `A` define an
  `A`-linear endomorphism of `A ⊗[K] V`.
  Evaluation is natural in the scalar algebra and colinear maps; the counit
  gives the identity, and every image-stable submodule has invariant
  scalar-extension image. No algebra structure on `C`, flatness or finiteness
  is required. Algebra-homomorphism inputs recover the stability criteria above.
  For the same right coaction, convolution satisfies
  `T_(φ * ψ) = T_φ.comp T_ψ`: the operator for `ψ` acts first.
  A Hopf algebra gives a homomorphism from algebra-valued convolution points to
  the units of the scalar-extended endomorphism monoid. Its inverse evaluates
  after the source antipode; coefficient changes and colinear maps intertwine
  these operators. Stable submodules retain their original tensor-inclusion
  images, preserved in both directions by the invertible point operators.
  [Data and API](AlgebraicGroups/Algebra/Coalgebra/Evaluation.lean),
  [composition](AlgebraicGroups/Algebra/Coalgebra/Evaluation/Convolution.lean),
  [point actions](AlgebraicGroups/Algebra/Coalgebra/Evaluation/Action.lean).
- **Convolution groups and algebra-valued points.** Algebra maps from a Hopf
  algebra over a commutative semiring to any commutative algebra form a group
  under convolution, without a coalgebra structure on the target. The named
  group structure uses the existing convolution monoid and agrees with the
  full original group structure when the target is also a bialgebra.
  For commutative Hopf algebras over commutative rings, postcomposition defines
  a group-valued functor on commutative algebras in independent universes.
  The same-universe spectrum comparison preserves the antipode inverse and
  change of coefficients.
  [Convolution API](AlgebraicGroups/Algebra/HopfAlgebra/Convolution.lean),
  [point functor](AlgebraicGroups/GroupScheme/PointGroup.lean).
- **Changing the coacting coalgebra.** Over a commutative semiring, a coalgebra
  morphism `f : C →ₗc[R] D` sends a specified right coaction `ρ` on `V` to
  `(id_V ⊗ f)ρ` on the same module. Full coalgebras and additive-monoid modules
  in independent universes suffice; no finiteness, flatness, projectivity or
  injectivity hypothesis is needed. The operation preserves identity, composition
  and colinear maps; change along the counit gives the scalar coaction for every
  comodule. [API and use](docs/COALGEBRAS.md#changing-the-coacting-coalgebra).
  `RightComodule.mapCoalgebra` changes the coalgebra factor;
  `RightComoduleHom.ofCoalgHom` makes the original coalgebra map colinear
  between the changed regular source comodule and the regular target comodule.
- **Inverses of colinear linear equivalences.** For specified right comodules
  `X` and `Y` over the same full coalgebra, a colinear linear equivalence
  `e : M ≃ₗ[R] N` has colinear inverse, by
  `Coalgebra.RightComoduleHom.colinear_symm`. This works over a commutative
  semiring on additive-commutative-monoid modules in independent universes,
  without flatness, a basis or finiteness. It reverses a map between fixed
  coactions, not the coacting coalgebra. The
  [nonidentity coordinate-swap clients over `ℕ`](AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule.lean)
  use distinct nonzero coactions.
  [API](docs/COALGEBRAS.md#inverses-of-colinear-linear-equivalences).
- **Finite right subcomodules.** Over a commutative semiring, for additive-monoid
  modules, projectivity of the coacting coalgebra alone gives finite-subset
  containment in finitely generated subcomodules. Neither module need be finite,
  nor the coacted-on module projective. Flatness of the coacting coalgebra suffices
  for unique subtype coactions from image stability and unique colinear
  factorization; the counit need not be onto. [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean).
  With projectivity of the coacting coalgebra, the module-finite subcomodules
  form a nonempty directed covering system containing every finite subset.
  Every compatible family of colinear maps from these specified stages to any
  target comodule glues to a unique colinear map on the original module.
  Restriction and gluing are mutually inverse data and commute with target
  postcomposition. Over a field these are the finite-dimensional stages, with
  no flatness, projectivity or finiteness hypothesis on the coalgebra or ambient
  vector space. More generally, directed covering sets of subcomodules have the
  same gluing property when the coacting coalgebra is flat.
  [Gluing and readbacks](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Gluing.lean).
  With flatness of the coacting coalgebra, containment of specified subcomodules
  gives canonical colinear inclusions with the ordinary submodule inclusion as
  underlying map. They satisfy identity, composition and unique ambient
  factorization. A nonzero coordinate line in the regular `ℕ[ℤ]` comodule
  embeds non-surjectively in the proper stable finitely generated span of two
  coordinates.
  [Inclusion model](AlgebraicGroupsTest/Algebra/Coalgebra/RightComoduleStability.lean).
- **The additive group's polynomial regular comodule.** Over any commutative
  ring `K`, transport of the regular comodule to `K[X]` keeps the coacting
  coalgebra `SymmetricAlgebra K K` fixed. Its generator has coaction
  `X ⊗ 1 + 1 ⊗ t`; the binomial formula proves stability of the usual
  degree-at-most-`n` submodules. These are module-finite subcomodules, increase
  and cover every polynomial, with finrank `n + 1` over every nontrivial
  commutative ring and finite-dimensional stages over a field.
  Over a nontrivial base every stage is proper and nonzero, while the ambient
  module is not module-finite. This is a comodule model, not an assertion of a
  polynomial Hopf-algebra equivalence or the full representation correspondence.
  [Construction and API](AlgebraicGroups/GroupScheme/AdditiveComodule.lean).
- **Ground-field invariance is not all-algebra invariance.** In this same
  polynomial right comodule over `𝔽₂`, the nonzero proper line spanned by
  `X² + X` is fixed by every ground-field point on the entire tensor-inclusion
  image. Over `𝔽₂[ε]/(ε²)`, the point `ε` sends its generator to
  `1 ⊗ (X² + X) + ε ⊗ 1`, outside the original inclusion image.
  The scalar-extended constant-coefficient linear map annihilates that image
  and takes the translated vector to the nonzero element `ε`. Thus this is
  failure of invariance for the same coaction and original image, not merely
  a comparison of different subspace predicates.
  [Countermodel](AlgebraicGroups/GroupScheme/AdditiveInvariantLine.lean).
- **Natural representations and specified right comodules.** For a commutative
  Hopf algebra `C` over a commutative ring `K` and any `K`-module `V`,
  `PointRepresentation.rightComoduleEquiv` constructs the correspondence between
  natural point representations on `R ⊗[K] V` and specified right coactions on
  the same `V`. Its inverse is the natural point action of a coaction; both
  composites return the original representation or comodule value. Generic-point
  reconstruction uses `ULift C`, an internal counit endomorphism and its tensor
  square, with independent base, coordinate, module and tester universes.
  Components read back coefficient evaluation, and canonical actions extend to
  independently sized coefficient algebras, naturally under every algebra map.
  The linear equivalence `pointHomEquiv` identifies point intertwiners with
  colinear maps of the same coactions, retaining underlying linear maps,
  identities and composition. Their scalar extensions give Mathlib's bundled
  intertwining maps. No finiteness, basis or flatness is needed. For infinite
  `V` this is the tensor-extension functor, not `Spec Sym(V*)`.
  [Reconstruction](AlgebraicGroups/GroupScheme/RepresentationReconstruction.lean),
  [equivalence and actions](AlgebraicGroups/GroupScheme/RepresentationEquivalence.lean),
  [morphisms](AlgebraicGroups/GroupScheme/RepresentationIntertwiner.lean).
- **Invariant original submodules and unique restriction.** Invariance means
  that all algebra-valued point operators preserve the image of the original
  scalar-extended subtype inclusion, on every tensor in that image. It is
  equivalent to image stability for the same recovered coaction, without
  flatness. If `C` is flat over `K`, the restricted coaction is constructed on
  exactly the original subtype `U`; its inclusion equation uniquely determines
  its coaction map and specified comodule value. The corresponding restricted
  point representation is likewise uniquely determined by the original
  inclusion as a point intertwiner. Component and arbitrary-algebra squares use
  precisely `U.subtype.baseChange R`. No injectivity is assumed over a general
  coefficient algebra; over a field it follows from flatness of vector spaces.
  [Criterion, restriction and readbacks](AlgebraicGroups/GroupScheme/RepresentationSubmodule.lean).
- **Changes of test-algebra universe.** Canonical extension presents the same
  recovered coaction at another tester level. Stock-lift restriction is
  constructed separately from the given representation's components at lifted
  coefficient algebras, followed by general linear coefficient descent. Its
  equality with canonical change, both inverse laws, iterated-lift and
  common-maximum comparisons are equations of representation values. Tensor
  comparisons are base-linear and coefficient-semilinear; conjugation and
  every-algebra-map descent retain the same coaction and point operators.
  Intertwiner transport retains the original linear map and its scalar
  extensions, respecting identity and composition.
  [Universe and Hom coherence](AlgebraicGroups/GroupScheme/RepresentationUniverse.lean).
- **The whole finite-dimensional subrepresentation system.** Over a field,
  finite stages are the module-finite subcomodules of the recovered coaction,
  with their original subspace subtypes and restricted representations. They
  contain zero, are directed under finite sums, cover `V` and contain every
  finite subset; no ambient or coordinate-algebra finite dimension is assumed.
  Canonical transition and ambient point maps retain the ordinary submodule
  inclusions and satisfy identity, composition and the ambient triangle.
  Every compatible family of point intertwiners on these stages into any target
  representation glues uniquely on the original `V`. Restriction and gluing are
  constructed inverse data with evaluation and covering-stage extensionality.
  They commute with target postcomposition and arbitrary source precomposition;
  finite-stage image containment gives choice-independent stage formulas.
  Changes of tester level and stock-lift restriction retain the same stage
  index, component maps, whole compatible families and ambient glued maps,
  including common-maximum comparisons.
  [Finite system and universal property](AlgebraicGroups/GroupScheme/RepresentationFiltration.lean).

- **Canonical affine-coordinate representations.** For a commutative ring `K`
  and an affine group `G` over `Spec K`, the canonical Hopf algebra on `Γ(G, O_G)`
  recovers the original group data through `G.isoSpec`. A natural multiplicative
  comparison identifies geometric points with coordinate-algebra maps in the
  scheme universe. The representation, original-image, intertwiner and whole
  finite-family APIs above specialize to this coordinate algebra on the same
  arbitrary `K`-module `V`, with their stated flatness and field boundaries.
  Independently sized test algebras use the coordinate point functor, not
  cross-universe scheme morphisms. For `G = Spec C`, an explicit bialgebra
  equivalence compatible with antipodes normalizes global sections to the
  original Hopf algebra `C`; the additive polynomial model keeps its original
  symmetric-algebra coalgebra and coaction under this readback.
  [Coordinate adapter and normalization](AlgebraicGroups/GroupScheme/AffineRepresentation.lean).
- **Right-comodule weight spaces.** For a full coalgebra over a commutative
  semiring and a specified right comodule, weight spaces are the submodules
  where the coaction is `v ↦ v ⊗ c`, for any coalgebra element `c`. The
  coalgebra and comodule carriers need only be additive-commutative-monoid
  modules, in independent universes. On a regular comodule, the counit and
  scalar multiplication by a group-like element satisfy both inverse
  equations, without a nontriviality assumption. Over a field, the weight
  submodules indexed by group-like elements are independent for arbitrary
  modules; no spanning or finite-dimensional hypothesis is used.
  [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule/WeightSpace.lean).
- **Components in a group-like basis.** Let `C` be a full coalgebra over a
  commutative semiring `R`, with a given basis `b` whose vectors are group-like.
  For any specified right `C`-comodule `V`, the stock right-basis tensor
  equivalence gives an `R`-linear map to finitely supported `V`-valued
  components. Each component is the coordinate projection of the coaction
  on its coalgebra factor, and the corresponding tensor sum reconstructs the
  coaction. The component at `i` coacts as its tensor with `b i`, and the
  finite sum of all components recovers the original vector. The modules `C`
  and `V` need only additive commutative monoids with `R`-module structures,
  in independent universes from `R` and the basis index; no finiteness,
  field, domain, nontriviality, flatness or projectivity is assumed. The
  group-like basis is an input, not a classification assertion.
  [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Components.lean).
- **Weight decomposition in a group-like basis.** With the same given basis
  and semiring/module hypotheses, the weight spaces `X.weightSpace (b i)`
  form an internal direct sum. The canonical inclusion-sum map is bijective,
  and its inverse `X.weightDecomposition b hb` is a linear equivalence whose
  coordinates are exactly `X.components b`. Each component is the identity
  on its own basis-weight space and vanishes on the others, so these projections
  are idempotent and pairwise orthogonal. The summands are indexed by the given
  basis, not by every group-like element of the coalgebra.
  [Decomposition and API](AlgebraicGroups/Algebra/Coalgebra/RightComodule/WeightDecomposition.lean).
- **Quotients of specified right comodules.** Over a commutative ring `R`, a
  specified right comodule over an `R`-coalgebra `C` on an additive-group
  `R`-module `M` descends canonically to `M ⧸ U` for every stable submodule `U`.
  No flatness hypothesis is needed on `C` or `M`. The canonical quotient map
  is a surjective comodule morphism, and colinear maps vanishing on `U`
  factor uniquely through it.
  [Construction and universal property](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Quotient.lean).
- **External tensor products of specified right comodules.** Over a commutative
  semiring, right comodules on arbitrary additive-monoid modules over full
  coalgebras `C` and `D` give a right comodule on `M ⊗[R] N` over the tensor
  coalgebra `C ⊗[R] D`, in five independent universes. The coaction shuffles
  the tensor of the input coaction values; regular comodules recover the
  regular comodule of that same tensor coalgebra. Specified comodule morphisms
  tensor via `TensorProduct.map`, preserving identities and composition, with
  all six composition-carrier universes independent. No flatness, projectivity,
  finiteness or purity of coaction values is required. This is an external
  construction, not an internal tensor product over a fixed bialgebra.
  [Construction and API](AlgebraicGroups/Algebra/Coalgebra/RightComodule/TensorProduct.lean),
  [Examples](AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule/TensorProduct.lean).
- **Modules of right-comodule morphisms.** Over a commutative semiring, morphisms
  between specified right comodules on additive-monoid modules form a module by
  pointwise operations. Their original underlying linear map is an injective
  bundled linear forgetful map, coherent with the generic linear-map class.
  No flatness, finiteness or nontriviality assumption is required.
  [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean),
  [coordinate and zero-module examples](AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule.lean).
- **Carrier transport of right comodules.** For a specified right `C`-comodule
  `X` and an `R`-linear equivalence `e : V ≃ₗ[R] W`, `X.transport e` is a lawful
  right `C`-comodule on the given target module. The coalgebra stays fixed:
  its coaction at `w` is `(e tensor id_C) (X.coaction (e.symm w))`, changing
  only the first tensor factor. The canonical colinear maps with underlying
  maps `e` and `e.symm` are mutual inverses. Transport respects identity,
  successive equivalences and inverse equivalences as equalities of specified
  comodule structures; colinearity of `e` characterizes the transported target.
  These results work over commutative semirings on additive-commutative-monoid
  modules in independent universes, without flatness or finiteness. They give
  object coherence and a canonical inverse pair, not transport of arbitrary
  comodule morphisms.
  [Module](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Transport.lean).
- **Intrinsic coefficients.** Coefficient spans exist over commutative semirings.
  Over a field they form a subcoalgebra: unique full corestriction of a coaction
  to `D` on the **same module** is equivalent to coefficient-span containment in
  `D`. No ambient finite dimension is needed; module-finiteness of the comodule
  gives module-finite coefficients, not algebra finite generation.
  For the regular right comodule of any coalgebra, `coefficientSpan = ⊤`
  over a commutative semiring; over a field,
  `coefficientSubcoalgebra.toSubmodule = ⊤`.
  [Module and GL₂ model](docs/COALGEBRAS.md#intrinsic-coefficient-coalgebras).
- **Regular-target correspondence.** Over a commutative semiring, composition
  with the counit identifies morphisms from a specified right comodule to the
  regular comodule with linear functionals on its underlying module. The inverse
  is the bundled coefficient morphism, naturally in the source comodule; the
  module and coalgebra universes are independent.
  [Correspondence](AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean),
  [nonidentity regular-comodule projection](AlgebraicGroupsTest/Algebra/Coalgebra/RegularComoduleCoefficients.lean).
- **Finite coefficient spans.** Over a commutative semiring, the all-dual
  coefficient span is the range of the coefficient map from the dual tensor
  the comodule. A module-finite tensor domain makes this span finitely generated;
  in particular, it suffices that both the comodule and its linear dual are
  module-finite. Over a Noetherian commutative ring, module-finiteness of the
  comodule alone suffices, without freeness or a chosen basis.
  [Tensor and finite-generation API](AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean),
  [finite nonfree integral comodule](AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsUse.lean).
- **Arbitrary-basis coefficient columns.** For a supplied module basis over a
  commutative semiring, the canonical tensor/Finsupp equivalence gives a finitely
  supported column for each value of the specified coaction. Its entries are
  coefficients, reconstruct the same coaction, and recover the original basis
  coordinates under the counit. Every functional has a coproduct expansion over
  that column's support. A finite basis index specializes this to the usual
  matrix-coefficient formula. The column identities use no finite-index
  hypothesis or finite-row-support claim.
  [Coordinate API](AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean),
  [infinite-basis columns](AlgebraicGroupsTest/Algebra/Coalgebra/RegularComoduleCoefficients.lean),
  [ordered GL₂ matrix formulas](AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsGL2.lean).
- **Coefficient functoriality.** For morphisms of specified right comodules
  over a commutative semiring, coefficients pull back along the underlying
  linear map; surjections decrease coefficient spans and bijections preserve
  them. Over a field, injections increase coefficient spans, with the same
  comparisons for the underlying submodules of coefficient subcoalgebras.
  [Module](AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean).
- **Coefficients under comodule morphisms.** For specified right comodules
  `X`, `Y` over one full coalgebra and `h : Coalgebra.RightComoduleHom X Y`,
  `RightComoduleHom.coefficient_apply` gives
  `Y.coefficient ell (h m) = X.coefficient (ell.comp h.toLinearMap) m`.
  Over a commutative semiring, surjectivity gives
  `Y.coefficientSpan ≤ X.coefficientSpan`, and bijectivity gives equality.
  Over a field, injectivity gives `X.coefficientSpan ≤ Y.coefficientSpan`.
  The carriers need only be additive-commutative-monoid modules in independent
  universes; no finite-generation hypothesis is required. Over a field with
  an additive-group ambient coalgebra, the coefficient subcoalgebras have the
  same respective underlying-submodule containments, and are equal for a
  bijective map. The rational `GL₂` column representation and its
  universe-lifted carrier retain a finitely generated, proper nonzero
  coefficient span with a nonzero off-diagonal coefficient.
  [API and models](docs/COALGEBRAS.md#coefficients-under-comodule-morphisms).
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
- **Group-like bases and coalgebra coordinates.** Over a commutative semiring `R`,
  a given basis `b : Module.Basis I R C` of group-like elements in a full
  coalgebra `C` determines `R[I] ≃ₗc[R] C` and, for every full coalgebra `D`,
  `(C →ₗc[R] D) ≃ (I → GroupLike R D)`. The modules need only
  `AddCommMonoid` and `Module R`, in independent universes. Basis evaluation,
  inverse coefficients, singleton formulas, extensionality and natural
  postcomposition laws characterize these constructions. They transport the
  existing free diagonal coalgebra's group-like-family correspondence: the index
  needs no monoid structure, and no field, finiteness, flatness or nonemptiness
  is assumed. Over a field, `GroupLike.spanCoalgebraEquiv` is the canonical
  span-basis specialization onto the group-like span, with diagonal coproduct
  and coefficient-sum counit.
  [Coordinates](AlgebraicGroups/Algebra/Coalgebra/GroupLikeCoordinates.lean),
  [free extension](AlgebraicGroups/Algebra/Coalgebra/MonoidAlgebra.lean),
  [nonidentity `ℕ[Bool]` equivalence, noninjective collapse and empty-index examples](AlgebraicGroupsTest/Algebra/Coalgebra/GroupLikeCoordinates.lean).
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
- **Group-like basis rigidity.** Over a nontrivial commutative semiring with
  preconnected prime spectrum, every group-like element equals the vector at a
  unique index of a given group-like basis. The module carries a full coalgebra;
  scalar, module and index universes are independent, with no finiteness or
  inhabitedness assumption on the index. The
  [theorem](AlgebraicGroups/LinearAlgebra/Coalgebra/GroupLikeBasis.lean) uses
  pairwise orthogonal, normalized coordinates and Mathlib's complemented-scalar
  clopen correspondence. An [infinite-basis example over field dual numbers](AlgebraicGroupsTest/LinearAlgebra/Coalgebra/GroupLikeBasis.lean)
  has a non-domain scalar ring with preconnected spectrum.
- **Comultiplicative algebra maps.** A unital algebra map from a full Hopf
  algebra to a bialgebra over a commutative semiring, preserving comultiplication,
  refines canonically to a bialgebra homomorphism with the same underlying
  algebra map, linear map and function. Counit preservation is automatic;
  neither algebra need be commutative, and the target need not be Hopf.
  [Module](AlgebraicGroups/Algebra/HopfAlgebra/Hom.lean),
  [infinite noncommutative group-algebra example](AlgebraicGroupsTest/Algebra/HopfAlgebra/Hom.lean).
- **Antipodes.** For full Hopf algebras over a commutative semiring, either
  commutative multiplication **or** cocommutative comultiplication suffices for
  `S² = id`; these are alternatives, not an iff or simultaneous requirements.
  Neither branch needs additive inverses, finiteness or nontriviality. Bialgebra
  maps commute with antipodes, and `Δ ∘ S = (S ⊗ S) ∘ τ ∘ Δ` holds without
  either commutativity assumption. [Involutivity](AlgebraicGroups/Algebra/HopfAlgebra/Antipode.lean),
  [maps](AlgebraicGroups/Algebra/HopfAlgebra/Hom.lean),
  [comultiplication](AlgebraicGroups/Algebra/HopfAlgebra/Comultiplication.lean).

- **Hopf images and first isomorphism.** Over any field, a bialgebra morphism
  from a possibly noncommutative ring Hopf algebra to a semiring Hopf algebra
  gives a full Hopf structure on its ordinary algebra range, with unchanged
  inherited semiring, algebra and module data. The ordinary quotient by its
  ring kernel is bialgebra-equivalent to this range via the ordinary algebra
  first-isomorphism equivalence. Inclusion, corestriction, both factor triangles,
  representative and inverse formulas, and uniqueness refer to these fixed
  structures; no surjectivity, injectivity or finiteness hypothesis is required.
  [API](AlgebraicGroups/Algebra/HopfAlgebra/Range.lean),
  [infinite cyclic augmentation client](AlgebraicGroupsTest/Algebra/HopfAlgebra/Ideal.lean).
- **Hopf-ideal kernels and inverse images.** Over a field, a bundled bialgebra
  homomorphism between full Hopf algebras has ordinary kernel with
  `Ideal.IsHopfIdeal`; inverse images preserve that property. Source rings may
  be noncommutative; kernels allow semiring targets and inverse images use ring
  targets. Over a commutative base ring, the corresponding statements assume
  scalar-restricted coideality of the kernel or preimage. This property alone
  asserts neither two-sidedness nor a quotient Hopf algebra.
  [Module](AlgebraicGroups/Algebra/HopfAlgebra/Ideal.lean),
  [proper augmentation example](AlgebraicGroupsTest/Algebra/HopfAlgebra/Ideal.lean).

### Matrix groups and group schemes

- **Closed points of a given scheme-theoretic kernel.** For given group schemes
  `G,H` locally of finite type over an algebraically closed field, a homomorphism
  `G → H`, and a supplied group-scheme unit-pullback `N → G`, the canonical comparison is a
  stock `ContinuousMulEquiv` from `N`'s closed-point group to the stock kernel of
  the original canonical closed-point map. It retains the full supplied group
  structures, original inclusion and original subspace topologies. The inclusion
  is a closed immersion and `N` is locally of finite type by derivation, not extra
  hypotheses; no normality, reducedness, joint continuity or topology on the field
  is assumed. Inclusion, inverse, rational-point/pullback-lift and unique-lift
  readbacks characterize the comparison. For every `n : ℕ`, the original `Gₘ`
  power map acts by `x ↦ x^n`, and `x^n = 1` is equivalent to a unique closed-point
  lift through the original `μₙ → Gₘ` inclusion. This includes order zero, using
  its whole-`Gₘ` group-algebra model, not a positive-order polynomial presentation.
  These are closed-point comparisons, not a test for equality of schemes.
  [Kernel comparison and readbacks](AlgebraicGroups/GroupScheme/ClosedPointKernel.lean),
  [all-order roots client](AlgebraicGroups/GroupScheme/RootsOfUnityClosedPoints.lean),
  [zero/one-order checks](AlgebraicGroupsTest/RootsOfUnity.lean).

- **Canonical continuous maps on closed points.** A homomorphism between given
  group schemes locally of finite type over an algebraically closed field induces
  a `ContinuousMonoidHom` on their canonical closed-point groups, with their original
  subspace topologies. The point action, comparison naturality, identities and
  compositions are characterized without unfolding. No joint continuity is assumed.
  A quasi-compact homomorphism has closed range on closed points, without global
  finite-type or quasi-separatedness assumptions. More generally, a locally closed
  range is closed. The determinant has full range when a matrix pivot is supplied,
  by its original group-scheme section.
  [Maps and readbacks](AlgebraicGroups/GroupScheme/ClosedPointHom.lean),
  [determinant split and range](AlgebraicGroups/GroupScheme/GeneralLinearClosedPoints.lean).

- **Locally closed subgroups of closed points.** For a group scheme locally
  of finite type over an algebraically closed field, a subgroup of its
  canonical closed-point group is closed exactly when it is a neighborhood
  of the identity within its closure. In particular, locally closed subgroups
  are closed in the original closed-point subspace topology. This uses
  separate continuity, not joint continuity, and asserts subset closedness,
  not a scheme-theoretic closed immersion.
  [Criteria](AlgebraicGroups/GroupScheme/ClosedPointSubgroup.lean).
- **Closed points of the additive group.** Over an algebraically closed field
  `K`, the closed-point subspace of the additive group scheme is homeomorphic
  to `K` with the cofinite topology. Field addition corresponds to the
  transported closed-point group law, whose multiplication is not continuous
  for the ordinary product of the closed-point subspace topologies.
  [Comparison and noncontinuity](AlgebraicGroups/GroupScheme/AdditiveClosedPoints.lean).
- **Separated group schemes.** Every group object over a base scheme whose
  underlying space has at most one point is separated over that base. In
  particular, this holds over every field, without a finite-type assumption.
  Over any base, a closed unit section suffices. The at-most-one-point result
  extends Milne, *Algebraic Groups* (2017), Proposition 1.22, using Mathlib's
  closed-section theorem. By Mathlib's postcomposition criterion, every
  over-map from such a group object to any scheme over the same base is separated;
  the target need not be a group object.
  `isSeparated_of_grpObj_of_subsingleton` includes the empty base, while
  `isSeparated_of_grpObj` is the field specialization; neither assumes
  reducedness. The additive-group clients distinguish zero and one points
  over every field and include arbitrary over-maps and the empty-base unit group.
  [Module](AlgebraicGroups/GroupScheme/Separated.lean),
  [additive-group and empty-base examples](AlgebraicGroupsTest/Additive.lean).
- **Separated morphisms and kernel units.** For any scheme `S`, a monoid
  morphism `q : G → Q` in `Over S` from a group object to a monoid object
  has the criterion `IsSeparated q.left ↔ IsClosedImmersion k.left`, where
  `K = pullback q η[Q]` in `Over S` and `k : 𝟙_(Over S) → K` is the
  canonical lift of the unit of `G` and the identity of the tensor unit,
  whose underlying scheme is `S`. The kernel is the whole scheme-theoretic
  fibre over the relative unit, not one geometric or reduced fibre. The
  criterion imposes no separatedness of `G → S`, target group structure,
  flatness, finiteness, field or nonemptiness hypothesis.
  [Statement](AlgebraicGroups/GroupScheme/Separated.lean),
  [multiplicative-group projection and boundary examples](AlgebraicGroupsTest/Multiplicative.lean).
- **Kernel fibres with a chosen lift.** In any Cartesian monoidal category,
  the chosen-lift statement concerns a monoid-object morphism `q : G → Q`
  from a group object `G` to a monoid object `Q` and a supplied kernel pullback.
  Right translation by an ordinary point `g : 𝟙 → G`, in the order `i(n) * g`,
  identifies the kernel with the fibre over `g ≫ q`. No monoid structure on the
  kernel or multiplicativity of its inclusion or of `g` is required. A target point
  without a chosen domain lift is not covered. The group-target specialization
  is the chosen-lift step in Milne's *Abelian Varieties*, Chapter I, proof of
  Proposition 7.1. The monoid-target formulation is more general than this source
  case.
  [Module](AlgebraicGroups/GroupObject/KernelTorsor.lean),
  [permutation and full-transformation-monoid example](AlgebraicGroupsTest/SplitKernelSemidirect.lean).
  The chosen-lift map is `GrpObj.isPullback_kernel_mulRight`.
  The [split-kernel clients](AlgebraicGroupsTest/SplitKernelSemidirect.lean)
  distinguish right from left translation using noncommuting permutations.
  Postcomposing the same projection with the canonical map to the full
  transformation monoid `Function.End (Fin 3)` retains the original kernel,
  inclusion and chosen point; the constant-zero transformation is not a unit.

- **Scalar extension of endomorphisms and automorphisms.** For an arbitrary
  module over a commutative ring, every map of commutative coefficient algebras
  induces maps on scalar-extended endomorphisms and invertible endomorphisms,
  respecting identity and composition. The base, module and successive
  coefficient-algebra universes are independent for the individual maps.
  Tensor cancellation has a readback on arbitrary tensors, not only pure ones.
  No finiteness, flatness or injectivity assumption is required. The comparison
  with literal right-ordered tensors transports the coefficient-module structure;
  The automorphism API varies the coefficient algebra, not arbitrary linear maps
  of the underlying module.
  [Endomorphisms](AlgebraicGroups/Algebra/MatrixEndBaseChange.lean),
  [automorphisms](AlgebraicGroups/Algebra/GeneralLinearBaseChange.lean),
  [examples](AlgebraicGroupsTest/MatrixEndBaseChange.lean).
- **Affine-target maps and convolution.** Over a commutative ring `R`, maps from
  an arbitrary scheme over `Spec R` to the spectrum of a commutative
  `R`-bialgebra correspond to algebra maps into global sections. Geometric
  pointwise multiplication corresponds to convolution; on affine sources the
  coefficient identification is `Γ(Spec T) ≅ T`. No source affineness or Hopf
  structure is required.
  [Module](AlgebraicGroups/GroupScheme/AffineHomOverConvolution.lean).
- **Cube-root coordinate and scheme decompositions.** When 3 is a unit, the
  coordinate algebra of μ₃ splits into the linear and quadratic factors. A
  chosen root of `X² + X + 1` splits the latter, in the order `1, ζ, ζ²`;
  over a field a primitive cube root suffices. The nonsplit quadratic is
  separable, including in characteristic two, and is identified with the
  subalgebra generated by a chosen root in an extension or the separable closure.
  The corresponding scheme isomorphisms are disjoint unions over the base,
  not products of group objects. In characteristic three a nonzero nilpotent
  coordinate and a nonidentity square-zero-algebra point coexist with trivial
  field-extension points.
  [Module and API guide](AlgebraicGroups/GroupScheme/RootsOfUnityThree.lean),
  [prime-field examples](AlgebraicGroupsTest/RootsOfUnityThree.lean).
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
- **Roots of unity as a power kernel.** Over any commutative ring and for every
  natural `n`, the canonical inclusion `μₙ → Gₘ` is a closed immersion and sends
  each root's affine point to its underlying unit. The square with the `n`-th
  power map on `Gₘ` and its unit section is a pullback both in schemes and over
  `Spec K`. Thus maps from arbitrary `K`-schemes whose `n`-th power is the unit
  factor uniquely through this inclusion; the source need not be affine or
  reduced. At `n = 0`, the power map is constant one, the kernel is all of `Gₘ`,
  and the inclusion agrees with the canonical zero-order isomorphism above.
  [Module](AlgebraicGroups/GroupScheme/RootsOfUnity.lean),
  [unique lift of the rational point `−1`](AlgebraicGroupsTest/RootsOfUnity.lean).
- **Unit-stalk dimension.** For a group scheme locally of finite type over any
  field, the Krull dimension of its full local ring at the canonical unit equals
  the topological Krull dimension of its underlying scheme. Neither algebraic
  closure of the field nor connectedness or reducedness of the group scheme is
  required.
  [Theorem](AlgebraicGroups/GroupScheme/Dimension.lean).
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
| [`AlgebraicGroups.GroupObject.CommutatorWord`](AlgebraicGroups/GroupObject/CommutatorWord.lean) | Ordered products of commutators on supplied fans, characteristic and naturality formulas, unit-pair extension and generalized-point range inclusion. |
| [`AlgebraicGroups.GroupObject.FamilyTranslation`](AlgebraicGroups/GroupObject/FamilyTranslation.lean) | Left and right shears for arbitrary parameter families, characteristic formulas, naturality and translated-product factorization. |
| [`AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport`](AlgebraicGroups/Algebra/Coalgebra/RightComodule/Transport.lean) | Carrier transport with fixed coalgebra, object-coherence laws, canonical inverse colinear maps and target characterization. |
| [`AlgebraicGroups.GroupScheme.AffineHomOverConvolution`](AlgebraicGroups/GroupScheme/AffineHomOverConvolution.lean) | Affine-target global-sections comparison with convolution, target and coefficient readbacks, naturality, and affine specialization. |
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

```lean
import AlgebraicGroups.GroupScheme.RootsOfUnity
#check AlgebraicGeometry.rootsOfUnitySchemeKernel_universal
```

For a map `f : T → Gₘ` over `Spec K`, this universal property takes the equation
that the composite with the `n`-th power map is the unit and supplies a unique
map `T → μₙ` whose composite with the canonical inclusion is `f`.
The [rational-point example](AlgebraicGroupsTest/RootsOfUnity.lean) identifies this
lift of `−1` at order two with the point of the explicit root `−1 : ℚ`.

Lean `v4.34.0-rc2` and exact GitHub dependencies are pinned in
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json). Direct requirements are Mathlib,
SchemeProperties, MinimalPrimes, GeneralLinearGroups, CoherentModules and
GroupTheory; building requires access to them.
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
Groups* (2017) and distinct 2012/2015 notes, his *Abelian Varieties*, version 2.0
(March 16, 2008), Chapter I, proof of Proposition 7.1 for chosen-lift fibre
translation, the Stacks Project, and the prior formalizations in Mathlib and
project dependencies. [References and scope](CREDITS.md#mathematical-sources)
give precise locators, qualifications and further sources; none asserts whole-source coverage.

## Credits and license

Authors: Formal Frontier Agents. AI agents developed the proofs and examples under
human project direction, reusing Mathlib and project libraries. Group-like coalgebra
coordinates combine Mathlib's diagonal coalgebra and linear-independence APIs with
this library's span-closure and restricted-subcoalgebra constructions. Original project
contributions use [Apache-2.0](LICENSE). [CREDITS.md](CREDITS.md) preserves contributor
roles, mathematical-method credit and authentic third-party notices separately
from redistribution rights.
