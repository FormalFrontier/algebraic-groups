# Unit laws for external tensor products of right comodules

This guide specifies the two external tensor unitors and the maps used to express them. The displayed unitor morphisms and equations are mathematical contracts, not additional Lean declarations.

## Scalars, coefficients and carriers

Use independent universes for `R`, `C`, `D`, `M` and `N`, with

```text
R : Type uR                         [CommSemiring R]
C : Type uC   [AddCommMonoid C] [Module R C] [Coalgebra R C]
D : Type uD   [AddCommMonoid D] [Module R D] [Coalgebra R D]
M : Type uM   [AddCommMonoid M] [Module R M]
N : Type uN   [AddCommMonoid N] [Module R N]
```

The scalar coalgebra is **`CommSemiring.toCoalgebra R`**. Its comultiplication is `r ↦ 1 ⊗ₜ[R] r` and its counit is the identity. Write `U` for `Coalgebra.RightComodule.regular R R` with exactly this coalgebra instance. Its carrier and coefficient coalgebra are both the canonical scalar module `R`. The instance-explicit expression is `@Coalgebra.RightComodule.regular R R _ _ _ (CommSemiring.toCoalgebra R)`.

There is no independent `[Coalgebra R R]` parameter. In particular, `U` is not the regular comodule of an arbitrary coalgebra structure on the scalar type. The coefficient coalgebra `C` remains arbitrary and full: no multiplication, `Algebra R C`, field, flatness, finiteness, basis, projectivity or cocommutativity assumption is used. Degenerate semirings and zero carriers are allowed.

Throughout, `X : Coalgebra.RightComodule R C M`, and `⊗` means `⊗[R]`. The notation `⊠` below means the existing `Coalgebra.RightComodule.externalTensor`, not a tensor product over a fixed bialgebra.

## Coefficient and carrier equivalences

The coefficient equivalences are the existing Mathlib maps:

```text
λC := Coalgebra.TensorProduct.lid R C
    : (R ⊗ C) ≃ₗc[R] C
ρC := Coalgebra.TensorProduct.rid R R C
    : (C ⊗ R) ≃ₗc[R] C
λC.symm : C ≃ₗc[R] (R ⊗ C)
ρC.symm : C ≃ₗc[R] (C ⊗ R)
```

Their readbacks, for `r : R` and `c : C`, are

```text
λC (r ⊗ₜ c) = r • c        λC.symm c = 1 ⊗ₜ c
ρC (c ⊗ₜ r) = r • c        ρC.symm c = c ⊗ₜ 1
```

For either equivalence or its inverse, write `a : A ≃ₗc[R] B` and `aₗ := a.toLinearEquiv.toLinearMap`. The bundled coalgebra laws have exactly the types

```text
(counit : B →ₗ[R] R) ∘ₗ aₗ = (counit : A →ₗ[R] R)
TensorProduct.map aₗ aₗ ∘ₗ (comul : A →ₗ[R] A ⊗ A)
  = (comul : B →ₗ[R] B ⊗ B) ∘ₗ aₗ
```

Use `a.toCoalgHom` when changing coefficients. Do not replace it by an arbitrary linear equivalence.

The carrier equivalences are

```text
ℓM := TensorProduct.lid R M : (R ⊗ M) ≃ₗ[R] M
rM := TensorProduct.rid R M : (M ⊗ R) ≃ₗ[R] M
```

`λC.toLinearEquiv = TensorProduct.lid R C`. For the right map, Mathlib's `rid_toLinearEquiv` gives `AlgebraTensorModule.rid R R C`, and `AlgebraTensorModule.rid_eq_rid` identifies this with `TensorProduct.rid R C`.

## Object directions

For this guide only, abbreviate

```text
AL(X) := U.externalTensor X
AR(X) := X.externalTensor U
L(X)  := AL(X).mapCoalgebra λC.toCoalgHom
Q(X)  := AR(X).mapCoalgebra ρC.toCoalgHom
```

These are notation for existing constructions, not new carrier structures.

| Object | Coefficient coalgebra | Carrier |
| --- | --- | --- |
| `AL(X)` | `R ⊗ C` | `R ⊗ M` |
| `L(X)` | `C` | `R ⊗ M` |
| `L(X).transport ℓM` | `C` | `M` |
| `X` | `C` | `M` |
| `AR(X)` | `C ⊗ R` | `M ⊗ R` |
| `Q(X)` | `C` | `M ⊗ R` |
| `Q(X).transport rM` | `C` | `M` |

`mapCoalgebra` follows the coefficient arrow forward. For `Z` on `V` and `e : V ≃ₗ[R] W`, `Z.transport e` is on `W`, with coaction

```text
(e.toLinearMap.rTensor C) ∘ₗ Z.coaction ∘ₗ e.symm.toLinearMap.
```

Transport changes only the carrier; it cannot turn `AL(X)` into a comodule over `C` without first changing the coefficients.

The unit object contracts, including their reverse directions, are

```text
L(X).transport ℓM = X              Q(X).transport rM = X
X.transport ℓM.symm = L(X)         X.transport rM.symm = Q(X)
(X.mapCoalgebra λC.symm.toCoalgHom).transport ℓM.symm = AL(X)
(X.mapCoalgebra ρC.symm.toCoalgHom).transport rM.symm = AR(X)
```

In the last two equalities the coefficient coalgebras are respectively `R ⊗ C` and `C ⊗ R`, not `C`. The reverse carrier transport in the second line still has coefficient coalgebra `C`.

The corresponding object-equality signatures, in `Coalgebra.RightComodule`, expand as follows:

```text
externalTensorLeftUnit_transport (X : RightComodule R C M) :
  (((U.externalTensor X).mapCoalgebra
    (Coalgebra.TensorProduct.lid R C).toCoalgHom).transport
    (TensorProduct.lid R M)) = X

externalTensorRightUnit_transport (X : RightComodule R C M) :
  (((X.externalTensor U).mapCoalgebra
    (Coalgebra.TensorProduct.rid R R C).toCoalgHom).transport
    (TensorProduct.rid R M)) = X
```

## Unitor morphism signatures

The four signatures below belong to `Coalgebra.RightComodule`. `U`, `λC` and `ρC` retain the canonical choices above. Each argument `X` has type `RightComodule R C M`; the coefficient and carrier class arguments are exactly those in the setting.

```text
externalTensorLeftUnitor (X : RightComodule R C M) :
  RightComoduleHom
    ((U.externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom) X

externalTensorLeftUnitorInv (X : RightComodule R C M) :
  RightComoduleHom X
    ((U.externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom)
```

```text
externalTensorRightUnitor (X : RightComodule R C M) :
  RightComoduleHom
    ((X.externalTensor U).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom) X

externalTensorRightUnitorInv (X : RightComodule R C M) :
  RightComoduleHom X
    ((X.externalTensor U).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
```

Write these maps as `lX`, `liX`, `rX`, `riX` in the remaining contracts. They form inverse pairs of existing `RightComoduleHom`s; no new comodule-equivalence structure is needed.

Their underlying maps must be exactly

```text
lX.toLinearMap  = ℓM.toLinearMap
liX.toLinearMap = ℓM.symm.toLinearMap
rX.toLinearMap  = rM.toLinearMap
riX.toLinearMap = rM.symm.toLinearMap
```

The full colinearity contracts, not merely their pure-tensor specializations, are

```text
X.coaction ∘ₗ ℓM.toLinearMap
  = ℓM.toLinearMap.rTensor C ∘ₗ L(X).coaction
L(X).coaction ∘ₗ ℓM.symm.toLinearMap
  = ℓM.symm.toLinearMap.rTensor C ∘ₗ X.coaction
X.coaction ∘ₗ rM.toLinearMap
  = rM.toLinearMap.rTensor C ∘ₗ Q(X).coaction
Q(X).coaction ∘ₗ rM.symm.toLinearMap
  = rM.symm.toLinearMap.rTensor C ∘ₗ X.coaction
```

Existing `RightComoduleHom.colinear_symm` supplies the inverse-colinearity implication for a linear equivalence. Existing `RightComodule.transport_eq_iff_colinear` expresses the first and third equations as the corresponding object-transport equalities. `transportHom` and `transportInvHom`, with those endpoint equalities, supply the required pair of morphism types.

## Evaluation, inverses and coaction readbacks

For arbitrary tensors `t : R ⊗ M`, `s : M ⊗ R`, and elements `m : M`, `a : R`, require

```text
lX t = ℓM t                    rX s = rM s
lX (a ⊗ₜ m) = a • m           rX (m ⊗ₜ a) = a • m
liX m = 1 ⊗ₜ m                riX m = m ⊗ₜ 1
liX.comp lX = RightComoduleHom.id L(X)
lX.comp liX = RightComoduleHom.id X
riX.comp rX = RightComoduleHom.id Q(X)
rX.comp riX = RightComoduleHom.id X
```

The source coaction readbacks have targets `(R ⊗ M) ⊗ C` and `(M ⊗ R) ⊗ C` respectively:

```text
L(X).coaction t = λC.toCoalgHom.toLinearMap.lTensor (R ⊗ M)
  ((U.externalTensor X).coaction t)
Q(X).coaction s = ρC.toCoalgHom.toLinearMap.lTensor (M ⊗ R)
  ((X.externalTensor U).coaction s)
```

The same coactions must satisfy

```text
L(X).coaction t = ℓM.symm.toLinearMap.rTensor C (X.coaction (ℓM t))
Q(X).coaction s = rM.symm.toLinearMap.rTensor C (X.coaction (rM s))
```

In particular these give pure-input readbacks with `ℓM (a ⊗ₜ m) = a • m` and `rM (m ⊗ₜ a) = a • m`. No assumption that `X.coaction m` is a pure tensor is made.

## Naturality

Let `Y : RightComodule R C N` and `f : RightComoduleHom X Y`. Using only existing morphism operations, put

```text
FL(f) := ((RightComoduleHom.id U).externalTensor f).mapCoalgebra
           (Coalgebra.TensorProduct.lid R C).toCoalgHom
       : RightComoduleHom L(X) L(Y)
FR(f) := (f.externalTensor (RightComoduleHom.id U)).mapCoalgebra
           (Coalgebra.TensorProduct.rid R R C).toCoalgHom
       : RightComoduleHom Q(X) Q(Y)
```

Their underlying linear maps are `TensorProduct.map LinearMap.id f.toLinearMap` and `TensorProduct.map f.toLinearMap LinearMap.id` respectively. The naturality contracts in the existing Hom type are

```text
lY.comp FL(f) = f.comp lX         liY.comp f = FL(f).comp liX
rY.comp FR(f) = f.comp rX         riY.comp f = FR(f).comp riX
```

For coefficient naturality let `h : C →ₗc[R] D`, with `λD` and `ρD` defined as above. The coefficient equations are

```text
λD.toCoalgHom.comp
  (Coalgebra.TensorProduct.map (CoalgHom.id R R) h)
  = h.comp λC.toCoalgHom
ρD.toCoalgHom.comp
  (Coalgebra.TensorProduct.map h (CoalgHom.id R R))
  = h.comp ρC.toCoalgHom
```

These are equalities of coalgebra morphisms from `R ⊗ C` and `C ⊗ R` to `D`. The scalar identity uses the same canonical scalar coalgebra. `Coalgebra.TensorProduct.map` works over the stated commutative semiring; the more restrictive `CoalgHom.lTensor` and `CoalgHom.rTensor` abbreviations are unnecessary here.

## Reuse and mathematical use

- `AlgebraicGroups.Algebra.Coalgebra.RightComodule`: specified comodules, `regular`, `mapCoalgebra`, `RightComoduleHom`, `colinear_symm`, identity, composition and coefficient-change morphisms.
- `AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct`: `externalTensor` on objects and morphisms, coaction and pure-tensor readbacks, and morphism identity/composition laws.
- `AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport`: carrier transport, the canonical forward/inverse morphisms and `transport_eq_iff_colinear`.
- `Mathlib.RingTheory.Coalgebra.Basic`: `CommSemiring.toCoalgebra` and its comultiplication/counit readbacks.
- `Mathlib.RingTheory.Coalgebra.TensorProduct`: the bundled coefficient unitors, their inverses and readbacks, and tensor products of coalgebra maps.
- `Mathlib.LinearAlgebra.TensorProduct.Associator` and `.Tower`: carrier unitors and the comparison for the right unitor.

For the regular comodule on an arbitrary `C`, these contracts identify the coefficient-adjusted external tensor with its original regular coaction under scalar multiplication. The existing regular monoid-algebra comodules over `ℕ` and the nonidentity scalar-tensor morphism in `AlgebraicGroupsTest.Algebra.Coalgebra.RightComodule.TensorProduct` provide nonzero-carrier uses of the surrounding operations. Zero carriers remain valid boundary cases, not evidence of nontriviality.

The contracts concern two unitors and their naturality. They assert no internal tensor product for an arbitrary fixed coalgebra and no triangle or other associativity compatibility law.
