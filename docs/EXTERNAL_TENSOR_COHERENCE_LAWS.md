# Triangle and pentagon for external tensor products

The equations and signatures here are mathematical statement contracts, not claims of additional Lean declarations. They concern external tensor products of specified right comodules: both coefficient coalgebras and carriers change. A coefficient equation or a carrier equation alone is not the comodule-Hom coherence statement.

## Context and canonical maps

Use nine independent universes, with the following standing context:

```text
R : Type uR                         [CommSemiring R]
C : Type uC  D : Type uD  E : Type uE  F : Type uF
M : Type uM  N : Type uN  P : Type uP  Q : Type uQ
```

Each of `C,D,E,F` has `[AddCommMonoid _] [Module R _] [Coalgebra R _]`; each of `M,N,P,Q` has `[AddCommMonoid _] [Module R _]`. Let

```text
X : Coalgebra.RightComodule R C M
Y : Coalgebra.RightComodule R D N
Z : Coalgebra.RightComodule R E P
W : Coalgebra.RightComodule R F Q
```

No ring, field, flatness, freeness, finiteness, basis, projectivity, cocommutativity or algebra structure on a coefficient is assumed. Tensor coalgebras always have their canonical full coalgebra structures. For the triangle, use exactly `CommSemiring.toCoalgebra R` on the scalar type and `U := Coalgebra.RightComodule.regular R R`; there is no independent `[Coalgebra R R]` parameter.

All notation below abbreviates specified expressions, not hypotheses or new structures. Write `⊗` for `⊗[R]`, `⊠` for `RightComodule.externalTensor`, and `H` for `Coalgebra.RightComoduleHom`. Set

```text
I(A) = CoalgHom.id R A
T(f,g) = Coalgebra.TensorProduct.map (R := R) (S := R) f g
a(A,B,K) = (Coalgebra.TensorProduct.assoc R R A B K).toCoalgHom
l(A) = (Coalgebra.TensorProduct.lid R A).toCoalgHom
r(A) = (Coalgebra.TensorProduct.rid R R A).toCoalgHom
```

Here `a(A,B,K) : ((A ⊗ B) ⊗ K) →ₗc[R] A ⊗ (B ⊗ K)`, `l(A) : R ⊗ A →ₗc[R] A`, and `r(A) : A ⊗ R →ₗc[R] A` are forward maps.

For carriers, set

```text
b(A,B,K) = (_root_.TensorProduct.assoc R A B K).toLinearMap
ll(A) = (_root_.TensorProduct.lid R A).toLinearMap
rr(A) = (_root_.TensorProduct.rid R A).toLinearMap
L(f,g) = _root_.TensorProduct.map f g
J(A) = (LinearMap.id : A →ₗ[R] A)
```

These are the underlying maps of the stock linear equivalences, not arbitrary maps satisfying a compatibility assumption. `g.comp f` and `g ∘ₗ f` mean first `f`, then `g`. In particular `mapCoalgebra` follows these coefficient arrows forward, retaining the carrier.

## Pentagon: both coefficient routes

Use the following vertices, with the indicated coefficient and carrier types:

| Vertex | Comodule | Coefficient `K_i` | Carrier `V_i` |
|---|---|---|---|
| 0 | `B0 = ((X ⊠ Y) ⊠ Z) ⊠ W` | `((C ⊗ D) ⊗ E) ⊗ F` | `((M ⊗ N) ⊗ P) ⊗ Q` |
| 1 | `B1 = (X ⊠ (Y ⊠ Z)) ⊠ W` | `(C ⊗ (D ⊗ E)) ⊗ F` | `(M ⊗ (N ⊗ P)) ⊗ Q` |
| 2 | `B2 = X ⊠ ((Y ⊠ Z) ⊠ W)` | `C ⊗ ((D ⊗ E) ⊗ F)` | `M ⊗ ((N ⊗ P) ⊗ Q)` |
| 3 | `B3 = X ⊠ (Y ⊠ (Z ⊠ W))` | `C ⊗ (D ⊗ (E ⊗ F))` | `M ⊗ (N ⊗ (P ⊗ Q))` |
| 4 | `B4 = (X ⊠ Y) ⊠ (Z ⊠ W)` | `(C ⊗ D) ⊗ (E ⊗ F)` | `(M ⊗ N) ⊗ (P ⊗ Q)` |

The coefficient edges, each of type `K_i →ₗc[R] K_j`, are exactly

```text
c01 = T(a(C,D,E), I(F))        c12 = a(C,D ⊗ E,F)
c23 = T(I(C), a(D,E,F))        c04 = a(C ⊗ D,E,F)
c43 = a(C,D,E ⊗ F)
```

The two explicit coefficient paths have the SAME type:

```text
pCL = c23.comp (c12.comp c01) : K0 →ₗc[R] K3
pCS = c43.comp c04           : K0 →ₗc[R] K3
```

Required coefficient headline, in `Coalgebra.TensorProduct`:

```text
assoc_pentagon : pCL = pCS
```

This quantifies over precisely `R,C,D,E,F` and their standing instances; `pCL,pCS` are the displayed expressions, not parameters. The equality is a conclusion to establish independently of comodules, never a new hypothesis. Both paths send `(((c ⊗ₜ d) ⊗ₜ e) ⊗ₜ f)` to `c ⊗ₜ (d ⊗ₜ (e ⊗ₜ f))`.

The two carrier routes are equally explicit. For edges `vij : Vi →ₗ[R] Vj`, put

```text
v01 = L(b(M,N,P), J(Q))       v12 = b(M,N ⊗ P,Q)
v23 = L(J(M), b(N,P,Q))       v04 = b(M ⊗ N,P,Q)
v43 = b(M,N,P ⊗ Q)
pML = v23 ∘ₗ (v12 ∘ₗ v01)   : V0 →ₗ[R] V3
pMS = v43 ∘ₗ v04            : V0 →ₗ[R] V3
```

Carrier headline: **`pML = pMS`**, on all tensors, not just pure tensors. Both routes take `(((m ⊗ₜ n) ⊗ₜ p) ⊗ₜ q)` to `m ⊗ₜ (n ⊗ₜ (p ⊗ₜ q))`. This is stock tensor associativity coherence, expressible using `TensorProduct.assoc_tensor''` and its companion identities; no replacement carrier coherence engine is required.

## Triangle: coefficient and carrier routes

Here only `R,C,D,M,N,X,Y` are used. Set

```text
D0 = (X ⊠ U) ⊠ Y    A0 = (C ⊗ R) ⊗ D    T0 = (M ⊗ R) ⊗ N
D1 = X ⊠ (U ⊠ Y)    A1 = C ⊗ (R ⊗ D)    T1 = M ⊗ (R ⊗ N)
D2 = X ⊠ Y          A2 = C ⊗ D          T2 = M ⊗ N
```

The exact coefficient edges and complete routes are

```text
t01 = a(C,R,D)           : A0 →ₗc[R] A1
t12 = T(I(C), l(D))      : A1 →ₗc[R] A2
t02 = T(r(C), I(D))      : A0 →ₗc[R] A2
tCS = t02               : A0 →ₗc[R] A2
tCL = t12.comp t01      : A0 →ₗc[R] A2
```

Required headline in `Coalgebra.TensorProduct`, quantifying over `R,C,D` with their standing instances and the canonical scalar coalgebra:

```text
assoc_triangle : tCS = tCL
```

The source is `(C ⊗ R) ⊗ D`; the direct path uses the RIGHT unitor on `C`, while the associator path uses the LEFT unitor on `D`. They send `((c ⊗ₜ s) ⊗ₜ d)` respectively to `(s • c) ⊗ₜ d` and `c ⊗ₜ (s • d)`.

The corresponding carrier edges and routes are

```text
w01 = b(M,R,N)          : T0 →ₗ[R] T1
w12 = L(J(M), ll(N))    : T1 →ₗ[R] T2
w02 = L(rr(M), J(N))    : T0 →ₗ[R] T2
tMS = w02              : T0 →ₗ[R] T2
tML = w12 ∘ₗ w01       : T0 →ₗ[R] T2
```

Carrier headline: **`tMS = tML`**. On pure tensors it is the tensor balancing equation `(s • m) ⊗ₜ n = m ⊗ₜ (s • n)`; the stated equality is of whole linear maps.

## The coefficient-change interchange needed for Hom paths

Tensoring a coefficient-changed comodule is not definitionally the same specified object as changing the tensor's coefficients. The object interchange contract has this exact proposed header in `Coalgebra.RightComodule`:

```text
externalTensor_mapCoalgebra
    (X : RightComodule R C M) (Y : RightComodule R D N)
    (f : C →ₗc[R] C') (g : D →ₗc[R] D') :
  (X.mapCoalgebra f).externalTensor (Y.mapCoalgebra g) =
    (X.externalTensor Y).mapCoalgebra
      (Coalgebra.TensorProduct.map (R := R) (S := R) f g)
```

In addition to the relevant standing context, `C' : Type uC'` and `D' : Type uD'` have independent universes and full `[AddCommMonoid _] [Module R _] [Coalgebra R _]` instances. Its natural home is `AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct`, alongside the existing object/coaction API. This is an equality to prove from the existing coactions and tensor-map naturality, not a law to supply as input.

For the coefficient headlines the natural mathematical home is `Mathlib.RingTheory.Coalgebra.TensorProduct`; a deliverable addition can live in `AlgebraicGroups.Algebra.Coalgebra.TensorProduct` as bridge lemmas about the stock maps. Hom coherence belongs in `AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Coherence`, importing `.Associator` and `.Unitors`.

Endpoint substitutions below mean ordinary substitution along THESE object equalities, `RightComodule.mapCoalgebra_id`, `RightComodule.mapCoalgebra_comp`, and the stated coefficient headline after it is proved. They retain the underlying linear map. They do not identify distinct coefficient types, assume the coherence law, introduce a generic cast API, or use heterogeneous equality. No new category, comodule dictionary, coalgebra associator or unitor is needed.

## Pentagon: actual Hom paths over one coefficient coalgebra

Abbreviate the existing maps by

```text
h(A,B,K) = Coalgebra.RightComodule.externalTensorAssocHom A B K
id(A) = Coalgebra.RightComoduleHom.id A
```

For comodules with coefficients `A',B',K'`, `h(A,B,K)` has type
`H (((A ⊠ B) ⊠ K).mapCoalgebra a(A',B',K')) (A ⊠ (B ⊠ K))`.

Define the following edge expressions, with sources normalized using the interchange bridge and the identity-change equation:

| Edge Hom | Prescribed expression | Type after that normalization |
|---|---|---|
| `e01` | `(h(X,Y,Z)).externalTensor (id(W))` | `H (B0.mapCoalgebra c01) B1` |
| `e12` | `h(X,Y ⊠ Z,W)` | `H (B1.mapCoalgebra c12) B2` |
| `e23` | `(id(X)).externalTensor (h(Y,Z,W))` | `H (B2.mapCoalgebra c23) B3` |
| `e04` | `h(X ⊠ Y,Z,W)` | `H (B0.mapCoalgebra c04) B4` |
| `e43` | `h(X,Y,Z ⊠ W)` | `H (B4.mapCoalgebra c43) B3` |

Before normalization, for example, `e01` starts at
`(((X ⊠ Y) ⊠ Z).mapCoalgebra a(C,D,E)) ⊠ W`, and `e23` starts at
`X ⊠ (((Y ⊠ Z) ⊠ W).mapCoalgebra a(D,E,F))`.
Those are equal to the displayed sources by the bridge; they are not silently interchangeable by definitional equality. Each `eij.toLinearMap` must be exactly `vij`.

Now fix the common FINAL coefficient coalgebra `K3`. All intermediate objects used for composition must be over it:

```text
S0 = B0.mapCoalgebra pCS
S1 = B1.mapCoalgebra (c23.comp c12)
S2 = B2.mapCoalgebra c23
S3 = B3
S4 = B4.mapCoalgebra c43
```

These have carriers `V0,V1,V2,V3,V4` respectively. Define typed edge maps by the following specified coefficient changes and endpoint substitutions:

```text
A01 = e01.mapCoalgebra (c23.comp c12) : H S0 S1
A12 = e12.mapCoalgebra c23           : H S1 S2
A23 = e23                           : H S2 S3
A04 = e04.mapCoalgebra c43           : H S0 S4
A43 = e43                           : H S4 S3
```

The precise source equations required here are

```text
(B0.mapCoalgebra c01).mapCoalgebra (c23.comp c12)
  = B0.mapCoalgebra pCL = B0.mapCoalgebra pCS = S0
(B1.mapCoalgebra c12).mapCoalgebra c23 = S1
(B0.mapCoalgebra c04).mapCoalgebra c43 = S0
```

The middle equality in the first line uses `assoc_pentagon` as a theorem to establish beforehand, NOT as a parameter. The other steps use `mapCoalgebra_comp`. Targets are exactly the displayed `Si`.

The complete path definitions and headline signatures, in `Coalgebra.RightComodule`, are:

```text
externalTensorPentagonLongHom (X : RightComodule R C M)
    (Y : RightComodule R D N) (Z : RightComodule R E P)
    (W : RightComodule R F Q) : H (B0.mapCoalgebra pCS) B3
  prescribed value: A23.comp (A12.comp A01)

externalTensorPentagonShortHom (X : RightComodule R C M)
    (Y : RightComodule R D N) (Z : RightComodule R E P)
    (W : RightComodule R F Q) : H (B0.mapCoalgebra pCS) B3
  prescribed value: A43.comp A04

externalTensor_pentagon (X : RightComodule R C M)
    (Y : RightComodule R D N) (Z : RightComodule R E P)
    (W : RightComodule R F Q) :
  externalTensorPentagonLongHom X Y Z W =
    externalTensorPentagonShortHom X Y Z W
```

Their characteristic `toLinearMap` equations are respectively `= pML` and `= pMS`; their arbitrary-input application equations are evaluation of those maps. Both must read back the pure-tensor reassociation given above. The equalities are in the single type `H S0 B3`, not between Homs over `K0` and `K3`.

## Triangle: actual Hom paths over `C ⊗ D`

Use the existing unitors, with the canonical `U`:

```text
rx = Coalgebra.RightComodule.externalTensorRightUnitor X
  : H ((X ⊠ U).mapCoalgebra r(C)) X
ly = Coalgebra.RightComodule.externalTensorLeftUnitor Y
  : H ((U ⊠ Y).mapCoalgebra l(D)) Y
```

Their underlying maps are exactly `rr(M)` and `ll(N)`. The edge expressions are

```text
f01 = h(X,U,Y)                  : H (D0.mapCoalgebra t01) D1
f12 = (id(X)).externalTensor ly : H (D1.mapCoalgebra t12) D2
f02 = rx.externalTensor (id(Y)) : H (D0.mapCoalgebra t02) D2
```

For `f12`, substitute the bridge equality between
`X ⊠ ((U ⊠ Y).mapCoalgebra l(D))` and `D1.mapCoalgebra t12`.
For `f02`, substitute between `((X ⊠ U).mapCoalgebra r(C)) ⊠ Y` and `D0.mapCoalgebra t02`. The unchanged factor uses `mapCoalgebra_id`. Thus `fij.toLinearMap = wij` for all three edges; the above types are after these explicit source substitutions.

Use the common coefficient `A2 = C ⊗ D` and objects

```text
O0 = D0.mapCoalgebra tCS    O1 = D1.mapCoalgebra t12    O2 = D2
G01 = f01.mapCoalgebra t12 : H O0 O1
G12 = f12                 : H O1 O2
G02 = f02                 : H O0 O2
```

For `G01`, the full source normalization is

```text
(D0.mapCoalgebra t01).mapCoalgebra t12
  = D0.mapCoalgebra tCL = D0.mapCoalgebra tCS = O0
```

The second equality is the image of the independently established `assoc_triangle`, in its reverse direction. No coefficient law is added as a hypothesis.

Required definitions and headline in `Coalgebra.RightComodule`:

```text
externalTensorTriangleLongHom (X : RightComodule R C M)
    (Y : RightComodule R D N) : H (D0.mapCoalgebra tCS) D2
  prescribed value: G12.comp G01

externalTensorTriangleShortHom (X : RightComodule R C M)
    (Y : RightComodule R D N) : H (D0.mapCoalgebra tCS) D2
  prescribed value: G02

externalTensor_triangle (X : RightComodule R C M)
    (Y : RightComodule R D N) :
  externalTensorTriangleShortHom X Y = externalTensorTriangleLongHom X Y
```

The required underlying-map readbacks are `tMS` for the short path and `tML` for the long path, with arbitrary-input application readbacks. In particular the two pure-input outputs are `(s • m) ⊗ₜ n` and `m ⊗ₜ (s • n)`. Their equality is an ordinary equality in `H O0 D2`.

## Reuse, colinearity and nondegeneracy

The path constructions use actual colinear maps from `.Associator` and `.Unitors`, existing `RightComoduleHom.externalTensor`, `mapCoalgebra`, and `comp`. With the source equalities above established, they have the full colinearity fields

```text
B3.coaction ∘ₗ pML = pML.rTensor K3 ∘ₗ S0.coaction
B3.coaction ∘ₗ pMS = pMS.rTensor K3 ∘ₗ S0.coaction
D2.coaction ∘ₗ tMS = tMS.rTensor A2 ∘ₗ O0.coaction
D2.coaction ∘ₗ tML = tML.rTensor A2 ∘ₗ O0.coaction
```

Only AFTER constructing these Homs in their common types does `RightComoduleHom.toLinearMap_injective` turn carrier coherence into Hom coherence. Neither coefficient-map equality alone nor an unbundled linear-map equation is silently promoted to a full comodule theorem.

`Mathlib.LinearAlgebra.TensorProduct.Associator` supplies `assoc_tensor`, `assoc_tensor'`, `assoc_tensor''`, tensor extensionality and balancing. `SemimoduleCat.MonoidalCategory.pentagon` and `.triangle` in `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic` express the carrier diagrams categorically; the direct tensor formulation retains independent universes. `Mathlib.Algebra.Category.CoalgCat.Monoidal` is ring-based and must not force a ring assumption here. Stock `Coalgebra.TensorProduct.map`, `assoc`, `lid`, `rid` remain the coefficient maps. The existing `TensorProduct.mapCoalgHom_eq_coalgebraTensorProductMap` in `AlgebraicGroups.Algebra.Coalgebra.TensorProduct` compares the more general data-level map with the stock full-coalgebra map; it is not a second coherence construction.

For nonzero witnesses over `ℕ`, use regular monoid-algebra comodules as in `AlgebraicGroupsTest.Algebra.Coalgebra.RightComodule.TensorProduct`, including the distinct coefficients `MonoidAlgebra ℕ Bool` and `MonoidAlgebra ℕ (Fin 3)`. Repeating regular factors gives four factors; weight-one monomials have iterated counit value `1`, so neither the initial pure tensor nor its reassociated image is zero. In the scalar triangle, `((1 ⊗ₜ 2) ⊗ₜ 1)` has left-unitor output `2`, not zero. The existing actual morphism client `(2 • id U).externalTensor (3 • id U)` has left-unitor output `6`, not `1`; the maps are not all identities. Zero carriers remain allowed, not the sole witnesses. No source-specific coefficient comparison or symmetry law follows from these two coherence contracts.
