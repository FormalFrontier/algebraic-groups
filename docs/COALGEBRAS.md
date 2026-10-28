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

Shared foundations use `TauCeti.Subcoalgebra K C` directly. For a subcoalgebra
`D`, its module carrier is `D.toSubmodule`, and `D.coalgebra` gives the
restricted coalgebra. The inclusion and factorization API in the retained
[homomorphism module](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Hom.lean)
uses this canonical type. Tau Ceti supplies the
[restricted structures](https://github.com/TauCetiProject/TauCeti/blob/31e387c73506f4de0ba05e251d2905c46bea1419/TauCeti/Algebra/Coalgebra/Subcoalgebra/Structure.lean),
[group-like spans](https://github.com/TauCetiProject/TauCeti/blob/31e387c73506f4de0ba05e251d2905c46bea1419/TauCeti/Algebra/Coalgebra/Subcoalgebra/GroupLike.lean) and
[finite-subcoalgebra theorem](https://github.com/TauCetiProject/TauCeti/blob/31e387c73506f4de0ba05e251d2905c46bea1419/TauCeti/Algebra/Coalgebra/Subcoalgebra/Finite.lean).
Over a field, finite subsets lie in module-finite subcoalgebras, without an
ambient dimension bound or a claim of least finite closure. The proper nonzero
`{0,1}`-supported diagonal example remains in
[the regression client](../AlgebraicGroupsTest/Algebra/Coalgebra/SubcoalgebraDiagonal.lean).

## Subcoalgebra image equivalences

The retained [image and equivalence API](../AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Equiv.lean)
works on canonical subcoalgebras. Injectivity of a coalgebra map only on `D`
suffices to identify `D.toSubmodule` with its image and to preserve and reflect
module-finiteness. Ambient equivalences transport subcoalgebras as an ordinary
`Equiv`; no ambient finite-dimensionality is assumed. The
[locally injective example](../AlgebraicGroupsTest/Algebra/Coalgebra/SubcoalgebraImageEquiv.lean)
remains globally noninjective.

## Changing the coacting coalgebra

The canonical class is `TauCeti.Comodule R C M`, with coaction `coact`, and
morphisms are `TauCeti.Comodule.Hom R C M N`. A specified coaction is installed
as a local instance when a proof compares two structures on the same module.
For a coalgebra map `f : C →ₗc[R] D`,
[`TauCeti.Comodule.Corestrict`](https://github.com/TauCetiProject/TauCeti/blob/31e387c73506f4de0ba05e251d2905c46bea1419/TauCeti/Algebra/Coalgebra/Comodule/Corestrict.lean)
changes the coaction to `(id_M ⊗ f)ρ`; `corestrictHom` acts on morphisms, and
`CoalgHom.toComoduleHom` makes the original coalgebra map colinear. Identity,
composition and counit specialization use canonical corestriction lemmas.
The scalars may be a commutative semiring and the independently sized modules
need only be additive commutative monoids. No field, finiteness, flatness or
injectivity assumption is imposed. The natural-number monoid-algebra example
still collapses the coalgebra factor while retaining the two distinct module
basis elements.

The retained inverse lift to a subcoalgebra, in
[ComoduleCoefficients](../AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean),
requires the coaction to lie in the image of the tensor of its inclusion. Over
a field it constructs `restrictCoalgebra` on the same module; its inclusion
formula recovers the original coaction. This inverse lift differs from changing
the module carrier.

## Inverses of colinear linear equivalences

`TauCeti.Comodule.Hom.colinear_symm` proves that the inverse of a colinear
linear equivalence is colinear over a commutative semiring, for independently
sized additive-monoid modules. No flatness, basis or finiteness is needed.
The [coordinate-swap clients](../AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule.lean)
compare distinct nonzero coactions over `ℕ`. Carrier transport itself uses
canonical `TauCeti.Comodule.Transport`; the retained
[transport module](../AlgebraicGroups/Algebra/Coalgebra/RightComodule/Transport.lean)
adds identity/tower coherence and the target characterization.

## Finite right-subcomodule containment

The retained [projective containment theorem](../AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean)
puts every finite subset in a finitely generated `TauCeti.Subcomodule R C M`
when the coacting coalgebra is projective over a commutative semiring. Neither
the ambient comodule nor the coalgebra need be finitely generated, and the
comodule need not be projective. Canonical subcomodule carriers and inclusion
morphisms are used directly. The module also proves directedness and exhaustion
by these finite carriers and algebra-valued evaluation criteria for stability.
The [boundary examples](../AlgebraicGroupsTest/Algebra/Coalgebra/RightComodule.lean)
retain the nonprojective module `ℕ →₀ ZMod 2` and the projective ideal `(3)`
in `ZMod 6` with nonsurjective counit `ε(e₃) = 3 ≠ 1`.

## Intrinsic coefficient coalgebras

Use canonical `TauCeti.Comodule.matrixCoefficient` and
`matrixCoefficientSubmodule`; the coalgebra argument is explicit when it cannot
be inferred from the functional and vector. Over a field, the retained
`TauCeti.Comodule.coefficientSubcoalgebra` has this coefficient span as its
underlying submodule. Full corestriction to a subcoalgebra on the same module
exists uniquely exactly when that span is contained in its carrier. No ambient
finite dimension is required. Module-finiteness of the comodule gives
module-finite coefficients, not finite generation of an algebra.

### Coefficients under comodule morphisms

Canonical matrix coefficients pull back along comodule morphisms. Surjections
decrease coefficient spans over a commutative semiring; bijections preserve
them. Over a field, injections increase them, by extension of linear
functionals. The retained
[functoriality and corestriction API](../AlgebraicGroups/Algebra/Coalgebra/ComoduleCoefficients.lean)
gives the corresponding coefficient-subcoalgebra comparisons. The
[rational GL₂ model](../AlgebraicGroupsTest/Algebra/Coalgebra/ComoduleCoefficientsGL2.lean)
and its universe-lifted carrier retain a proper, nonzero, finitely generated
coefficient span and a visible off-diagonal coefficient. They use canonical
GL Hopf coordinates, rather than an external duplicate localization.

## Finite coalgebra containment

The retained [coefficient engine](../AlgebraicGroups/Algebra/Coalgebra/FiniteSubcoalgebra.lean)
works over commutative semirings with a projective ambient coalgebra: every
finite subset lies in finitely generated `U` with `Δ(U)` in the tensor image
of `U ⊗ C`. Over a field the stronger `D ⊗ D` containment and canonical
finite-subcoalgebra theorem apply. The assertions concern module finiteness,
not algebra finite generation, and allow infinite ambient modules. Explicit
ambient coordinates remain in [Coefficients](../AlgebraicGroups/Algebra/Coalgebra/Coefficients.lean).

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

Import `AlgebraicGroups` for the aggregate, or a focused retained module linked
above. Import canonical Tau Ceti foundation modules directly when only their
mathematics is needed. There are no forwarding modules for the removed local
subcoalgebra or group-like-span definitions.

Use `D.toSubmodule` for a canonical subcoalgebra’s module carrier. Install a
specified `TauCeti.Comodule` structure with `letI` when using its class-based
morphism or coefficient API. The retained finite-containment and coefficient
modules extend these canonical structures; their ordinary-import clients cover
infinite ambient coalgebras, nonfree semiring modules and degenerate rings.

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

The determinant-localized coordinate-ring model of `GL₂` follows J. S. Milne,
*Algebraic Groups* (2017), §2, item 2.8. The coefficient comparisons use Mathlib's
linear maps, duals and extension of linear functionals; carrier transport uses
its linear equivalences and tensor naturality interfaces.

For antipode involutivity, bialgebra maps and comultiplication, see the
[mathematical topic guide](MATHEMATICS.md#antipode-involutivity). For pinned
requirements and focused target commands, see [building](BUILDING.md).
