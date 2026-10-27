# Algebraic groups

Lean definitions and theorems about matrix groups, affine group schemes and their
coordinate algebras, and coalgebras. The library builds on Mathlib and separately
maintained project libraries; it does not claim to formalize an entire source.

## Headline results

### Group objects

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
  With projectivity of the coacting coalgebra, the underlying carriers of the
  module-finite subcomodules are directed and cover the whole comodule.
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
  [Module and GL₂ model](docs/COALGEBRAS.md#intrinsic-coefficient-coalgebras).
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
