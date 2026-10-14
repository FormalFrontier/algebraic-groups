# Coalgebras, comodules and coefficient matrices

This guide gives the detailed statements, models and API entry points behind the
[coalgebra headlines](../README.md#coalgebras-and-hopf-algebras). Scalar hypotheses
vary by construction: quotient maps use commutative rings, the projective
containment engine works over commutative semirings, and subcoalgebras and
intrinsic coefficient coalgebras use fields. Finiteness of a module is distinct
from finite generation of an algebra.

## Coalgebra morphisms on coideal quotients

Over a commutative ring `R`,
for `R`-modules with additive commutative group structures and
`CoalgebraStruct`, `Submodule.liftQCoalgHom` descends a coalgebra morphism
vanishing on a coideal uniquely through its quotient projection.
`Submodule.mapQCoalgHom` sends a morphism carrying one coideal into another
to a morphism between their quotients, respecting identity and composition.
The universes are independent; no coalgebra-law, field, flatness or
projectivity assumption is required. These constructions use Mathlib's
quotient structures and linear universal property. See the
[quotient-morphism API](../AlgebraicGroups/Algebra/Coalgebra/Quotient.lean) and
[clients](../AlgebraicGroupsTest/Algebra/Coalgebra/CoidealQuotient.lean).

## Subcoalgebras and finite containment over a field

For a field `K` and
a `K`-coalgebra `C`, `Subcoalgebra K C` is a subspace `D` such that every
member's comultiplication lies in the image of
`D ⊗[K] D → C ⊗[K] C`. Its subtype carries the restricted comultiplication
and counit satisfying the coalgebra laws. The inclusion is a coalgebra
homomorphism, and any coalgebra homomorphism with values in `D` factors
uniquely through it. `Coalgebra.exists_finite_subcoalgebra` puts every
finitely generated subspace inside such a `D` with `Module.Finite K D`;
there is also a finite-subset variant. The ambient coalgebra need not be
finite-dimensional, no algebra or Hopf structure is required, and no least
finite closure is asserted. See the
[carrier](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra.lean),
[restricted coalgebra](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Coalgebra.lean),
[homomorphisms](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Hom.lean) and
[finite containment](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Finite.lean).
The [diagonal example](../AlgebraicGroupsTest/Algebra/Coalgebra/SubcoalgebraDiagonal.lean)
uses the proper nonzero finite-dimensional subcoalgebra of `ℕ →₀ K`
supported on `{0, 1}`.

## Subcoalgebra image equivalences

For a field `K` and `K`-coalgebras
`C`, `C'` in independent universes, `Subcoalgebra.equivMapOfInjOn f D hf`
identifies `D` with its canonical image `Subcoalgebra.map f D` as a
coalgebra. It assumes only `hf : Set.InjOn f (D : Set C)` for the coalgebra
homomorphism `f`, not ambient injectivity. Under this local hypothesis, the
image carrier is finitely generated exactly when the source carrier is;
likewise `Module.Finite K (Subcoalgebra.map f D) ↔ Module.Finite K D`.
`CoalgEquiv.subcoalgebraCongr` transports subcoalgebras along an ambient
coalgebra equivalence as an ordinary `Equiv` (not a bundled order
isomorphism), preserving and reflecting `Module.Finite`. No ambient
finiteness is assumed. See the [API](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Equiv.lean) and the
[infinite-dimensional, globally noninjective but locally injective example](../AlgebraicGroupsTest/Algebra/Coalgebra/SubcoalgebraImageEquiv.lean).

## Finite right-subcomodule containment

`Coalgebra.RightComodule R C M`
specifies a right linear coaction `ρ : M →ₗ[R] M ⊗[R] C` satisfying
coassociativity and right counitality. The scalars are an arbitrary commutative
semiring; `C` and `M` are modules with additive commutative monoid structures,
`C` is a coalgebra, and all three universes are independent. These definitions
need no projectivity. With only the additional hypothesis
`[Module.Projective R C]`, every finite subset of `M` lies in a
`RightComodule.Subcomodule` whose underlying submodule is finitely generated.
The witness carries a coaction on its subtype and a colinear inclusion;
every member has coaction in the image of `U ⊗ C → M ⊗ C`.
Neither `C` nor `M` need be finitely generated, and `M` need not be projective
or free. Under `[Module.Flat R C]`, image stability induces a unique subtype
coaction, with subcomodule extensionality and unique colinear factorization
through the inclusion. The counit need not be surjective. See the
[right-comodule API](../AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean) and
[coefficient engine](../AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean).
The [examples](../AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule.lean) include
the nonprojective `ℕ`-module `ℕ →₀ ZMod 2` and a coaction of the proper
projective ideal `(3)` in `ZMod 6`, with nonsurjective counit and coacting
generator satisfying `ε(e₃) = 3 ≠ 1`, so it is not group-like.

## Intrinsic coefficient coalgebras

For a right comodule `X` with coaction
`ρ : M →ₗ[K] M ⊗[K] C` over a commutative semiring, `X.coefficientSpan`
spans the coefficients obtained by applying every linear functional
`M →ₗ[K] K` to the first tensor factor, for every element of `M`.
Over a field, `X.coefficientSubcoalgebra` has exactly this span as its
underlying submodule, with comultiplication in the image of its tensor-square
inclusion into `C ⊗ C`.
For any subcoalgebra `D`, there is a unique full structure
`Y : Coalgebra.RightComodule K D M` satisfying
`(id_M ⊗ ι_D) ∘ Y.coaction = ρ` if and only if
`X.coefficientSpan ≤ D.toSubmodule`. This changes the coacting coalgebra
from `C` to `D`, not the module `M`. Neither `M` nor `C` need be
finite-dimensional; `[Module.Finite K M]` is required only for finite
generation of the coefficient subcoalgebra's underlying module, not algebra
finite generation. See the [intrinsic API](../AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean),
[rational GL₂ model](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsGL2.lean)
and [corestriction clients](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsUse.lean).

## Finite coalgebra containment

Over a commutative semiring, every finite
subset of a coalgebra with projective ambient module lies in a
module-finitely-generated submodule `U` whose every member has comultiplication in the image of
`U ⊗ C → C ⊗ C`; the ambient additive structure need only be a commutative
monoid. No ambient finite generation is required, and free modules are included
through Mathlib's free-to-projective instance. Over a field, every finite subset
lies in a module-finitely-generated submodule `D` with every-member image closure
under `D ⊗ D → C ⊗ C`.
These theorems assert tensor-image containment, not algebra finite generation;
the restricted coalgebra structure over a field is constructed separately by
the subcoalgebra API above. See
[finite containment](../AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean),
[coefficient spans with explicit ambient coordinate maps](../AlgebraicGroups/Algebra/Coalgebra/Coefficients.lean)
and [group-like spans](../AlgebraicGroups/Algebra/Coalgebra/GroupLikeSpan.lean).

## Algebra-generating coalgebra coefficients

A finite-type, possibly
noncommutative semiring algebra `A` over a field `K`, carrying a coalgebra
structure on its canonical `K`-module, admits a finite square matrix `a`
with `Δ(a i j) = ∑ k, a i k ⊗ a k j`, `ε(a i j) = δᵢⱼ`, and entries
generating `A` as a `K`-algebra. The matrix size may be zero; neither
module-finiteness nor algebra–coalgebra multiplicative compatibility is
required. See `Coalgebra.exists_coefficientMatrix_adjoin_eq_top` in the
[finite-coalgebra API](../AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean).

## Idempotent principal ideal coalgebras

For an idempotent `e` in any
commutative semiring `K`, the existing ideal `Ideal.span {e}` has counit
the scalar inclusion and comultiplication `d ↦ d ⊗ e`. The explicit
constructor includes zero and one and needs no freeness assumption. See
the [module](../AlgebraicGroups/Algebra/Coalgebra/IdempotentIdeal.lean) and
[clients](../AlgebraicGroupsTest/Algebra/Coalgebra/IdempotentIdeal.lean).
For a lawful coalgebra over a commutative semiring, the
[counit range](../AlgebraicGroups/Algebra/Coalgebra/CounitRange.lean) is an
idempotent scalar ideal `I` satisfying `I • ⊤ = ⊤` on the coalgebra. Its counit
is zero exactly when the carrier is subsingleton. These statements use the
coalgebra laws, with no surjectivity, freeness or finite-generation premise.

In contrast, tensor counit ranges multiply, and the tensor counit is surjective
**if and only if both factor counits are surjective**, already for
`[CommSemiring R]`, additive commutative monoid modules in independent universes,
and **only `CoalgebraStruct` on each factor**. Neither statement needs coalgebra
laws, flatness or tensor-inclusion injectivity. The
[clients](../AlgebraicGroupsTest/Algebra/Coalgebra/CounitRange.lean) equip the
natural-number ideals `(2)` and `(3)` with zero comultiplications and inclusion
counits. Their tensor counit has image `(6)` and is not surjective; a nonzero
generator tensor and an explicit failure of the left counit identity distinguish
these chosen structures from lawful coalgebras.

For lawful coalgebras, orthogonal supports can make the tensor product
subsingleton even when both factors are nontrivial: the ideals `(3)` and `(4)`
in `ZMod 6` have proper nonzero, orthogonal counit ranges. Tensoring `(3)` with
itself retains its proper nonzero range. Projectivity gives flatness, not
surjectivity: `(3)` is a nonfree projective module with nonsurjective counit.
For a nontrivial free coalgebra the counit is surjective, without a finite-basis
assumption; the free zero module over `ℕ` shows why nontriviality matters.
Infinite diagonal coalgebras over `ℕ` and `ℚ`, zero ideal coalgebras and the
empty diagonal coalgebra over a trivial ring retain the infinite and degenerate
boundaries rather than imposing finite generation or nonzero scalars.

Separately, over a commutative ring `R`, a lawful `[Coalgebra R C]` on an
additive commutative group module satisfies `Module.FaithfullyFlat R C`
**if and only if `Module.Flat R C` AND its counit is surjective**, equivalently
has range the whole scalar ring. Thus faithful flatness gives both full range
and surjectivity; flatness is a separate requirement, with no finite generation,
freeness, projectivity or nontriviality premise. The forward proof combines the
counit-law action, ideal transport and Mathlib's ideal-top reflection criterion.
The converse uses CoherentModules' public `Module.FaithfullyFlat.of_surjective`:
source flatness is supplied by the hypothesis on `C`, while Mathlib's
`Module.FaithfullyFlat.self` supplies the target scalar ring's faithful flatness.
This is not a scalar-extension flatness assumption or a new global instance.
Faithful scalar action together with finite generation of the **actual counit
image ideal** also gives surjectivity; it does not require the ambient module
to be finite, and faithfulness alone does not suffice. The infinite coalgebra
`ℕ →₀ ℚ` has finitely generated counit image but is not a finite module.

Under extension of scalars
from `R` to a commutative `R`-algebra `S`, the counit ideal of `S ⊗[R] C` is
`Ideal.map (algebraMap R S)` of the original counit ideal, without flatness
or projectivity hypotheses. See [scalar extension](../AlgebraicGroups/Algebra/Coalgebra/BaseChange.lean)
and [clients](../AlgebraicGroupsTest/Algebra/Coalgebra/BaseChange.lean).

## Hopf coefficient matrix units

Over a commutative scalar semiring, a
finite square matrix `M` in a possibly noncommutative semiring Hopf algebra,
with `Δ(M i j) = ∑ k, M i k ⊗ M k j` and `ε(M i j) = δᵢⱼ`, is a unit
in the matrix semiring with entrywise antipode as two-sided inverse, without a transpose.
Empty indices are allowed. See the [construction and entry API](../AlgebraicGroups/Algebra/Coalgebra/CoefficientMatrixUnit.lean)
and [integer-weight and empty-index clients](../AlgebraicGroupsTest/Algebra/Coalgebra/CoefficientMatrixUnit.lean).

## Cardinality of group-like elements

For a torsion-free coalgebra over a
commutative domain, the cardinality of Mathlib's `GroupLike` carrier is at most
the coalgebra's module rank. Rank strictly below `ℵ₀` gives bundled and
predicate-set finiteness and a `Nat.card` bound by `finrank`; module-finite
coalgebras have these consequences without freeness or a field hypothesis.
Integer diagonal coalgebras give sharp, zero and infinite examples. The
rank-two diagonal coalgebra over `ℤ × ℤ` admits four group-like elements,
demonstrating the domain hypothesis. See the
[module](../AlgebraicGroups/Algebra/Coalgebra/GroupLikeCardinality.lean) and
[clients](../AlgebraicGroupsTest/GroupLikeCardinality.lean).

## Group-like elements and scalar-source coalgebra maps

Over a commutative
semiring `R`, normalized group-like elements of an `R`-coalgebra `C` correspond
to coalgebra morphisms from the canonical scalar coalgebra `R` to `C`.
The forward map sends `r` to `r • g`; the inverse evaluates at `1`. No
multiplication on `C`, field hypothesis, basis or nontriviality is required.
See the [equivalence API](../AlgebraicGroups/Algebra/Coalgebra/GroupLikeHom.lean)
and [concrete clients](../AlgebraicGroupsTest/Algebra/Coalgebra/GroupLikeHom.lean).

## Ordered group-like differences and translations

For `[CommSemiring R]`, `[AddCommGroup C]`, `[Module R C]` and a full
`[Coalgebra R C]`, in independent universes, group-like `g, h : C` have
`ε(g - h) = 0` and
`Δ(g - h) = g ⊗ (g - h) + (g - h) ⊗ h`. The endpoints are ordered `(g, h)`.
The [difference theorem](../AlgebraicGroups/Algebra/Coalgebra/SkewPrimitive.lean)
uses the canonical full-class predicates, not a `CoalgebraStruct`-only API;
no multiplication on the carrier is required.

The [complete clients](../AlgebraicGroupsTest/Algebra/Coalgebra/SkewPrimitive.lean)
work over a commutative ring for the submodule and translation statements.
Writing `S` for the skew-primitive submodule and `D = span {g - h}`, they give
`D ≤ S` and both directions of membership under `a ↦ a + t • (g - h)` for
arbitrary `a, t`, without assuming membership of `a` or invertibility of `t`.
On `S`, the stock `Equiv.addRight` is an **ordinary permutation**, with inverse
`x ↦ x - t • (g - h)` and both inverse-composition identities. It is not an
additive, linear or coalgebra equivalence.

The wrapped diagonal `ℤ[ℤ]` model has distinct normalized group-like endpoints,
a nonzero difference, and a nonidentity translation which moves zero. Both `S`
and `D` are proper nonzero submodules; the third basis vector `δ₂` lies outside
`S`. The integer-indexed basis makes the ambient module not finitely generated,
despite each vector's finite support. Only `D ≤ S` is asserted, not `S = D` or
an extension-class classification. Coincident endpoints, zero translation
scalar, the scalar-self coalgebra and zero scalars give collapsing cases.
The zero carrier over nontrivial scalars has no normalized group-like endpoints
and is not a positive witness; these examples do not supply a structure-only
translation equivalence.

## Modules and examples

Import `AlgebraicGroups` for the aggregate or a focused producer linked above.
For images under coalgebra homomorphisms over a field `K`, import
[`AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Map`](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Map.lean).
`Subcoalgebra.map f D` has underlying submodule
`Submodule.map f.toLinearMap D.toSubmodule`. Image membership means
`∃ x ∈ D, f x = y`; containment in a target submodule means every member
of `D` maps into it. The API also gives identity and composition laws,
monotonicity for containment of underlying submodules, preservation of
finite generation, and zero reflection: the image carrier is zero exactly
when the source carrier is zero, even for a noninjective homomorphism.
The [homomorphism API](../AlgebraicGroups/Algebra/Coalgebra/Hom.lean) gives the
underlying linear-map zero criterion over any commutative scalar semiring;
only the source needs the coalgebra laws.

For right comodules, the focused import is
`AlgebraicGroups.Algebra.Coalgebra.RightComodule`. Given `X : Coalgebra.RightComodule R C M`
and `hs : s.Finite`, use `X.exists_fg_subcomodule_of_finite hs` when
`[Module.Projective R C]` is available. Its witness `U` exposes `U.toSubmodule`,
`U.comodule`, the bundled colinear inclusion `U.subtype` and every-member closure
`U.coaction_mem`. For linear-map operations on a `Coalgebra.RightComoduleHom`,
use its `toLinearMap` projection.

For intrinsic coefficients, import
`AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients`. Over a field,
`X.coefficientComodule` is a right comodule on the same `M` over
`X.coefficientSubcoalgebra`, and
`X.subtype_lTensor_comp_coefficientComodule_coaction` gives its inclusion equation.
Use `X.existsUnique_restrictCoalgebra_iff D` to characterize full corestriction
uniqueness by coefficient-span containment, and `X.coefficientSubcoalgebra_fg`
when `[Module.Finite K M]` is available. The
[ordinary-import GL₂ clients](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsUse.lean)
apply both theorems to the proper nonzero span of the four matrix entries in the
[rational column representation](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsGL2.lean).

[Split tensor coordinates](../AlgebraicGroups/Algebra/TensorProduct/Split.lean)
give finite-support reconstruction and all-index contraction formulas along an
arbitrary split free presentation over a commutative semiring, without a basis
or finite-generation assumption on the presented module. The
[clients](../AlgebraicGroupsTest/Algebra/TensorProduct/Split.lean) include infinite
free semiring modules, the nonfree ideal `(3)` in `ZMod 6`, its countable
non-finitely-generated direct sum, empty indices and a nonsplit counterexample.
## References and related topics

The field coalgebra theorem and coefficient method are credited to M. E.
Sweedler, *Hopf Algebras* (1969). Mathlib supplies the coalgebra, tensor, module
and morphism interfaces; the detailed mathematical and formalization credits
are in [CREDITS.md](../CREDITS.md#mathematical-sources). These citations do not
assert a general two-factor containment theorem over semirings.

For antipode involutivity, bialgebra maps and comultiplication, see the
[mathematical topic guide](MATHEMATICS.md#antipode-involutivity). For pinned
requirements and focused target commands, see [building](BUILDING.md).
