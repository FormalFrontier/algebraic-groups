# Symmetry of external tensor products

This document specifies a mathematical interface for symmetry of specified
right comodules. The signatures and equations below are requirements, not
claims that additional Lean declarations have been implemented or checked.

## Generality and notation

Fix independent universes `uR uC uD uM uN` and the context

```text
R : Type uR, C : Type uC, D : Type uD
M : Type uM, N : Type uN
[CommSemiring R]
[AddCommMonoid C] [Module R C] [Coalgebra R C]
[AddCommMonoid D] [Module R D] [Coalgebra R D]
[AddCommMonoid M] [Module R M]
[AddCommMonoid N] [Module R N]
X : Coalgebra.RightComodule R C M
Y : Coalgebra.RightComodule R D N
```

Every displayed signature quantifies over this context when its variables occur.
The two tensor coalgebras always have their canonical full coalgebra structures.

There is no cocommutativity assumption, no algebra structure or multiplication
on `C` or `D`, and no field, freeness, flatness, basis, finiteness or projectivity
assumption. This is an external construction over changing coefficient
coalgebras, not an internal tensor product over a fixed bialgebra.

Write `H = Coalgebra.RightComoduleHom`. All shorthand below is textual
abbreviation for the specified expression, not an extra parameter or hypothesis.

## The coefficient map is a specific coalgebra equivalence

Required definition, in the namespace `Coalgebra.TensorProduct`:

```text
comm (R : Type uR) (C : Type uC) (D : Type uD)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D] :
    (C ⊗[R] D) ≃ₗc[R] (D ⊗[R] C)
```

Its value must bundle exactly `_root_.TensorProduct.comm R C D`, with that
linear equivalence and its inverse as its data, and with preservation of the
canonical counit and comultiplication as its obligations. It is not an identity
map and is not an arbitrary equivalence supplied by a caller.

For all later signatures define the textual abbreviations

```text
KCD = Coalgebra.TensorProduct.comm R C D
KDC = Coalgebra.TensorProduct.comm R D C
kCD = KCD.toCoalgHom
kDC = KDC.toCoalgHom
bMN = (_root_.TensorProduct.comm R M N)
bNM = (_root_.TensorProduct.comm R N M)
A = (X.externalTensor Y).mapCoalgebra kCD
B = Y.externalTensor X
```

In particular `A : Coalgebra.RightComodule R (D ⊗[R] C) (M ⊗[R] N)`
and `B : Coalgebra.RightComodule R (D ⊗[R] C) (N ⊗[R] M)`.

Required readbacks, in `Coalgebra.TensorProduct` (with `R C D` as above):

```text
comm_toLinearEquiv : KCD.toLinearEquiv = _root_.TensorProduct.comm R C D
comm_toCoalgHom_toLinearMap :
  kCD.toLinearMap = (_root_.TensorProduct.comm R C D).toLinearMap
comm_tmul (c : C) (d : D) : KCD (c ⊗ₜ[R] d) = d ⊗ₜ[R] c
comm_symm_tmul (c : C) (d : D) : KCD.symm (d ⊗ₜ[R] c) = c ⊗ₜ[R] d
comm_symm : KCD.symm = KDC
comm_trans_comm : KCD.trans KDC = CoalgEquiv.refl R (C ⊗[R] D)
```

The same readbacks with `C,D` exchanged describe the inverse. Writing
`epsilonCD`, `deltaCD` for `Coalgebra.counit`, `Coalgebra.comul` on
`C ⊗[R] D`, and similarly `epsilonDC`, `deltaDC`, the actual structure
fields must give both rows of this table:

| Map | Counit equation | Comultiplication equation |
| --- | --- | --- |
| `kCD` | `epsilonDC ∘ₗ kCD.toLinearMap = epsilonCD` | `TensorProduct.map kCD.toLinearMap kCD.toLinearMap ∘ₗ deltaCD = deltaDC ∘ₗ kCD.toLinearMap` |
| `kDC` | `epsilonCD ∘ₗ kDC.toLinearMap = epsilonDC` | `TensorProduct.map kDC.toLinearMap kDC.toLinearMap ∘ₗ deltaDC = deltaCD ∘ₗ kDC.toLinearMap` |

The canonical tensor coalgebra is already available from
`Mathlib.RingTheory.Coalgebra.TensorProduct`. That module supplies bundled
`Coalgebra.TensorProduct.assoc`, `lid` and `rid`, but does not supply the
`comm` above. The interface requires a bundled coefficient symmetry with
these characteristic readbacks, not a replacement tensor coalgebra engine.
A matching bundled map should be reused wherever it is available.

`LinearEquiv.toCoalgEquiv` in
`AlgebraicGroups.Algebra.Coalgebra.Equiv` is not by itself this definition:
its source uses pulled-back coalgebra data. Both ends here must instead be the
existing canonical tensor coalgebras.

## Carrier symmetry and its colinear inverse

Required signatures in `Coalgebra.RightComodule`:

```text
externalTensor_comm_colinear (X : Coalgebra.RightComodule R C M)
    (Y : Coalgebra.RightComodule R D N) :
  B.coaction ∘ₗ bMN.toLinearMap =
    bMN.toLinearMap.rTensor (D ⊗[R] C) ∘ₗ A.coaction

externalTensor_comm_symm_colinear (X : Coalgebra.RightComodule R C M)
    (Y : Coalgebra.RightComodule R D N) :
  A.coaction ∘ₗ bMN.symm.toLinearMap =
    bMN.symm.toLinearMap.rTensor (D ⊗[R] C) ∘ₗ B.coaction
```

These are colinearity statements over `D ⊗[R] C`, after coefficient
reindexing. Neither is colinearity between the two unreindexed external
tensors. The inverse statement is an instance of the existing
`Coalgebra.RightComoduleHom.colinear_symm`, not a new inverse theory.

Required bundled maps in the same namespace:

```text
externalTensorCommHom (X : Coalgebra.RightComodule R C M)
    (Y : Coalgebra.RightComodule R D N) :
  Coalgebra.RightComoduleHom
    ((X.externalTensor Y).mapCoalgebra
      (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
    (Y.externalTensor X)

externalTensorCommInvHom (X : Coalgebra.RightComodule R C M)
    (Y : Coalgebra.RightComodule R D N) :
  Coalgebra.RightComoduleHom
    (Y.externalTensor X)
    ((X.externalTensor Y).mapCoalgebra
      (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
```

Their prescribed underlying linear maps are respectively `bMN.toLinearMap`
and `bMN.symm.toLinearMap`. Write `sXY = externalTensorCommHom X Y`
and `tXY = externalTensorCommInvHom X Y` in the following readbacks.

```text
externalTensorCommHom_toLinearMap : sXY.toLinearMap = bMN.toLinearMap
externalTensorCommInvHom_toLinearMap : tXY.toLinearMap = bMN.symm.toLinearMap
externalTensorCommHom_apply (z : M ⊗[R] N) : sXY z = bMN z
externalTensorCommInvHom_apply (z : N ⊗[R] M) : tXY z = bMN.symm z
externalTensorCommHom_tmul (m : M) (n : N) :
  sXY (m ⊗ₜ[R] n) = n ⊗ₜ[R] m
externalTensorCommInvHom_tmul (m : M) (n : N) :
  tXY (n ⊗ₜ[R] m) = m ⊗ₜ[R] n
externalTensorCommInvHom_comp_externalTensorCommHom :
  tXY.comp sXY = H.id A
externalTensorCommHom_comp_externalTensorCommInvHom :
  sXY.comp tXY = H.id B
```

All these names are qualified by `Coalgebra.RightComodule`; all implicitly
quantify over `X,Y` and their standing context. Bundling these two existing
linear equivalences needs no new carrier category or dictionary.

## Transport directions

`Coalgebra.RightComodule.transport Z e` moves a specified coaction from the
source carrier of `e` to its target. Its value on a target vector `w` is
`e.toLinearMap.rTensor K (Z.coaction (e.symm w))`, where `K` is the unchanged
coefficient coalgebra. Coefficient change and carrier transport are different
operations.

Required headers in `Coalgebra.RightComodule`:

```text
externalTensor_comm_transport :
  ((X.externalTensor Y).mapCoalgebra kCD).transport bMN = Y.externalTensor X
externalTensor_comm_transport_symm :
  (Y.externalTensor X).transport bMN.symm =
    (X.externalTensor Y).mapCoalgebra kCD
externalTensor_comm_transport_reindex :
  (X.externalTensor Y).transport bMN =
    (Y.externalTensor X).mapCoalgebra kDC
```

All implicitly quantify over `X,Y` and the standing context. The first equality
is exactly the forward colinearity requirement expressed through the existing
`transport_eq_iff_colinear`; the second is its inverse-carrier form.

| Starting comodule | Coefficient change | Carrier transport | Result |
| --- | --- | --- | --- |
| `X.externalTensor Y` | `kCD`, into `D ⊗[R] C` | `bMN`, into `N ⊗[R] M` | `Y.externalTensor X` |
| `Y.externalTensor X` | none, remain over `D ⊗[R] C` | `bMN.symm`, into `M ⊗[R] N` | `(X.externalTensor Y).mapCoalgebra kCD` |
| `Y.externalTensor X` | `kDC`, into `C ⊗[R] D` | `bNM`, into `M ⊗[R] N` | `X.externalTensor Y` |
| `X.externalTensor Y` | none, remain over `C ⊗[R] D` | `bMN`, into `N ⊗[R] M` | `(Y.externalTensor X).mapCoalgebra kDC` |

The inverse Hom above remains over `D ⊗[R] C`. It is not literally the
forward Hom for `Y,X`, whose coefficient coalgebra is `C ⊗[R] D`.
Identifying them requires coefficient change and the double-change equality.

## Naturality with both coefficient types visible

Take four further independent universes and
`M0 : Type uM0`, `M1 : Type uM1`, `N0 : Type uN0`, `N1 : Type uN1`,
each an `AddCommMonoid` and an `R`-module. Let
`Xi : Coalgebra.RightComodule R C Mi` and
`Yi : Coalgebra.RightComodule R D Ni` for `i = 0,1`.
The coefficient context `R,C,D` is unchanged.

Required signatures in `Coalgebra.RightComodule`:

```text
externalTensorCommHom_naturality
    (f : H X0 X1) (g : H Y0 Y1) :
  (externalTensorCommHom X1 Y1).comp
      ((f.externalTensor g).mapCoalgebra kCD) =
    (g.externalTensor f).comp (externalTensorCommHom X0 Y0)

externalTensorCommInvHom_naturality
    (f : H X0 X1) (g : H Y0 Y1) :
  (externalTensorCommInvHom X1 Y1).comp (g.externalTensor f) =
    ((f.externalTensor g).mapCoalgebra kCD).comp
      (externalTensorCommInvHom X0 Y0)
```

The first equation lies in
`H ((X0.externalTensor Y0).mapCoalgebra kCD) (Y1.externalTensor X1)`;
the second lies in
`H (Y0.externalTensor X0) ((X1.externalTensor Y1).mapCoalgebra kCD)`.
Both are over `D ⊗[R] C`. Forgetting colinearity gives, in the forward case,

```text
(TensorProduct.comm R M1 N1).toLinearMap ∘ₗ
    TensorProduct.map f.toLinearMap g.toLinearMap =
  TensorProduct.map g.toLinearMap f.toLinearMap ∘ₗ
    (TensorProduct.comm R M0 N0).toLinearMap
```

This is the stock tensor-map symmetry identity, not a new morphism tensor
construction. Use `Coalgebra.RightComoduleHom.externalTensor`, its
`toLinearMap_externalTensor`, `externalTensor_tmul`, `externalTensor_id` and
`externalTensor_comp`, together with `mapCoalgebra` on Homs, without duplicating
those definitions or their identity/composition laws.

## Involutivity without mismatched Hom endpoints

In addition to `comm_symm`, `comm_trans_comm` and the two bundled inverse
identities above, require the following in `Coalgebra.RightComodule`:

```text
externalTensor_comm_mapCoalgebra_involutive :
  ((X.externalTensor Y).mapCoalgebra kCD).mapCoalgebra kDC =
    X.externalTensor Y

externalTensor_comm_involutive :
  ((((X.externalTensor Y).mapCoalgebra kCD).transport bMN)
    .mapCoalgebra kDC).transport bNM = X.externalTensor Y
```

Both sides of each equality have type
`Coalgebra.RightComodule R (C ⊗[R] D) (M ⊗[R] N)`.
These statements quantify over the original `X,Y` and context, not the
four-carrier naturality context.
A composite of forward symmetry Homs with exchanged arguments cannot be
written as an equality to an identity Hom before reconciling the double
coefficient change. The inverse-Hom identities avoid this typing problem.

## Mathematical clients and boundary cases

The existing module
`AlgebraicGroupsTest.Algebra.Coalgebra.RightComodule.TensorProduct` supplies
regular comodules for distinct coefficient coalgebras
`C = MonoidAlgebra ℕ Bool` and `D = MonoidAlgebra ℕ (Fin 3)`.
For `c = MonoidAlgebra.single false 1` and
`d = MonoidAlgebra.single (0 : Fin 3) 1`, a symmetry client should read back
`KCD (c ⊗ₜ[ℕ] d) = d ⊗ₜ[ℕ] c` on coefficients and the same swap on
carriers. This distinguishes the two coefficient types and fixes the direction
of the map. The existing coordinate/counit detectors give nonzero
regular-comodule inputs and distinguish a coefficient from its input; no basis
assumption is part of the symmetry theorem.

That module also contains the scalar-coalgebra morphism client over `ℕ`:
`(2 • H.id (Coalgebra.RightComodule.regular ℕ ℕ)).externalTensor
 (3 • H.id (Coalgebra.RightComodule.regular ℕ ℕ))`
sends `1 ⊗ₜ 1` to `2 ⊗ₜ 3`, with left-unitor image `6`, not `1`.

The naturality requirement swaps this output to `3 ⊗ₜ 2`; it must not silently
replace either morphism by an identity. This scalar client tests the morphism
map, while the distinct-coefficient client tests coefficient reindexing. They
serve different purposes and are not interchangeable.

Zero carriers, the zero semiring, and equal coefficient types remain allowed
by the general signatures. In the equal-type case, the coefficient swap is
still the specified tensor permutation, not an identity assumption. Regular
comodules and the bottom-subcomodule boundary already have an external tensor
API; symmetry should use that API rather than replace its object construction.

## Existing operations to retain

* `Coalgebra.RightComodule.externalTensor` and `externalTensorCoaction`;
* `Coalgebra.RightComoduleHom.externalTensor`, with its map, application,
  pure-tensor, identity and composition readbacks;
* `Coalgebra.RightComodule.mapCoalgebra` and the corresponding Hom operation;
* `Coalgebra.RightComodule.transport`, `transport_eq_iff_colinear`, and
  `Coalgebra.RightComoduleHom.colinear_symm`;
* `_root_.TensorProduct.comm`, `comm_tmul`, `comm_symm`, `comm_comp_comm`
  and `map_comp_comm_eq`.
