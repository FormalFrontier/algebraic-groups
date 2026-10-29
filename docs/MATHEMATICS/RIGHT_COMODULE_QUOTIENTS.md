# Quotients of specified right comodules

Let `R` be a commutative ring, let `C` be an `R`-coalgebra, and let
`X : Coalgebra.RightComodule R C M` be a specified right comodule. The scalar,
coalgebra, source-module and target-module universes are independent. The
underlying additive structure of `M` is an additive commutative group; that of
`C` need only be an additive commutative monoid. All modules use the existing
Mathlib module structures.

Write `ρ = X.coaction : M →ₗ[R] M ⊗[R] C`. Fix an ordinary submodule
`U : Submodule R M` and a proof `hU : X.IsStable U`. Thus, for every `m ∈ U`,
`ρ m` belongs to the range of `U.subtype.rTensor C`. This condition does not
choose a comodule structure on the subtype and does not require the tensor of
the subtype inclusion to be injective.

## The quotient and its canonical morphism

Use the existing module quotient `M ⧸ U` and its map `q = U.mkQ`. Write
`X.quotient U hU` for the specified right comodule on this quotient whose
coaction is the module-quotient descent

```text
U.liftQ ((U.mkQ.rTensor C) ∘ₗ X.coaction) hzero.
```

Here `hzero` says that the displayed map vanishes on `U`. Image stability
supplies a tensor-inclusion preimage, and `U.mkQ ∘ₗ U.subtype = 0` annihilates
that preimage after tensoring. No flatness or tensor-inclusion injectivity is
involved.

The characteristic representative law is

```text
(X.quotient U hU).coaction (U.mkQ m) =
  U.mkQ.rTensor C (X.coaction m).
```

The coaction satisfies the same right coassociativity and counit identities as
`X`. The coefficient coalgebra remains `C`; this is not a quotient coalgebra.
The canonical morphism

```text
X.mkQ U hU : Coalgebra.RightComoduleHom X (X.quotient U hU)
```

has underlying linear map exactly `U.mkQ`, is surjective, and satisfies
`X.mkQ U hU m = U.mkQ m`. The representative law also uniquely determines the
quotient coaction among linear maps on the existing quotient.

## Colinear descent and uniqueness

Let `N` be an `R`-module with an additive commutative monoid structure, let
`Y : Coalgebra.RightComodule R C N`, and fix
`f : Coalgebra.RightComoduleHom X Y`. Suppose
`hf : U ≤ LinearMap.ker f.toLinearMap`. There is a canonical morphism

```text
f.liftQ U hU hf :
  Coalgebra.RightComoduleHom (X.quotient U hU) Y.
```

Its underlying linear map has the representative law

```text
f.liftQ U hU hf (U.mkQ m) = f m.
```

An `R`-module over a ring already has the canonical additive-group structure
with negation `(-1) • n`. This structure can be used internally for Mathlib's
linear quotient lift; no extra additive-group hypothesis on `N` belongs in the
public descent statement. With explicit additive-group data on `N`, the
underlying-linear-map agreement lemma `liftQ_toLinearMap` identifies it with
Mathlib's `U.liftQ f.toLinearMap hf`. The general underlying-map composition law
and factorization property do not require that extra data in their statements.

The universal property is

```text
∃! g : Coalgebra.RightComoduleHom (X.quotient U hU) Y,
  g.comp (X.mkQ U hU) = f.
```

In particular, `f.liftQ U hU hf` composed with `X.mkQ U hU` is `f`, and any
specified morphism with that composite equals the canonical lift. Equality is
equality in the existing `RightComoduleHom` type, not a new class of maps.

The characteristic API consists of:

- `RightComodule.quotient` and `quotient_coaction_mkQ`;
- `RightComodule.mkQ`, `mkQ_toLinearMap`, `mkQ_apply` and `mkQ_surjective`;
- `RightComodule.quotient_coaction_unique`;
- `RightComoduleHom.liftQ`, `liftQ_toLinearMap` and `liftQ_mkQ`;
- `RightComoduleHom.liftQ_comp_mkQ`, `liftQ_unique` and `existsUnique_liftQ`.

The module family is
`AlgebraicGroups.Algebra.Coalgebra.RightComodule.Quotient`, importing the
existing specified-comodule home and Mathlib's module-quotient/tensor machinery.
No arbitrary-submodule comodule factory, new quotient carrier, category,
evaluator, representation reconstruction or separate image/kernel construction
is needed.

## A nonzero proper quotient over the rationals

Take `M = ℚ × ℚ`, coefficient coalgebra `ℚ`, and the scalar comodule
`X = Coalgebra.RightComodule.scalar ℚ M`. Its coaction sends `(a, b)` to
`(a, b) ⊗ₜ[ℚ] 1`. Let

```text
p = LinearMap.snd ℚ ℚ ℚ,
U = LinearMap.ker p,
hU = Coalgebra.RightComodule.scalar_isStable U.
```

Then `U` is the first coordinate axis: `(a, b) ∈ U` exactly when `b = 0`.
The element `(1, 0)` is a nonzero member of `U`, whereas `(0, 1)` is outside it.
Apply the quotient construction above to this particular `X`, `U` and `hU`.
Its descended coaction obeys

```text
(X.quotient U hU).coaction (U.mkQ (a, b)) =
  U.mkQ (a, b) ⊗ₜ[ℚ] 1.
```

The ordinary quotient linear equivalence

```text
e = LinearMap.quotKerEquivOfSurjective p LinearMap.snd_surjective
```

identifies the quotient with the second coordinate `ℚ`: it sends
`U.mkQ (a, b)` to `b`, and its inverse sends `b` to `U.mkQ (0, b)`. In
particular, `e (U.mkQ (0, 1)) = 1`, so the quotient is nonzero.

The projection `p` is colinear between the scalar comodules and vanishes on
`U`. Its unique quotient factor is `e.toLinearMap`; the representative law
proves its colinearity, and the inverse equivalence is colinear as well. Thus
this single model exercises the descended coaction, canonical quotient
morphism, factorization, uniqueness and coordinate identification. It does not
replace the descended coaction by an independently chosen scalar structure.

For the boundary submodules `U = ⊥` and `U = ⊤`, the quotient respectively
identifies with the original module and is subsingleton. Only the corresponding
quotient-map, representative-coaction and uniqueness specializations are
needed.

## Scope of the ring assumption

The source quotient is Mathlib's additive-group module quotient, constructed
using additive-subgroup differences. This explains the ring and source
additive-group scope; no general semiring-exactness assertion is made. There
is no flatness, field, finite-generation, finite-dimensionality, freeness,
projectivity, basis or algebra-structure assumption on `C` or `M`. The field
`ℚ` occurs only in the concrete example.
