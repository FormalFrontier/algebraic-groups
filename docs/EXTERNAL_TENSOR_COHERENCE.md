# Associativity of external tensor products of right comodules

This is a mathematical definition contract and a collection of proposed
statement headers, not a claim that these statements have been formalized.
The coefficient coalgebra and the carrier must both be reassociated. Merely
reassociating the carrier does not give a morphism between comodules over
two different coefficient coalgebras.

## Generality and notation

The context for every header below is:

```lean
import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport

open scoped TensorProduct
universe uR uC uD uE uM uN uP
variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE}
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
```

All seven universes are independent. The coalgebras are full coalgebras,
not merely specified comultiplications. No field, flatness, finite generation,
basis, projectivity, cocommutativity, algebra structure on a coefficient
coalgebra, or extra multiplication is assumed. This is an external tensor
product, not an internal tensor product over a fixed bialgebra.

The following are documentation abbreviations for existing expressions,
not proposed new definitions:

```lean
namespace Coalgebra.RightComodule
variable (X : RightComodule R C M) (Y : RightComodule R D N)
variable (Z : RightComodule R E P)
local notation "CL" => ((C ⊗[R] D) ⊗[R] E)
local notation "CR" => (C ⊗[R] (D ⊗[R] E))
local notation "aC" => Coalgebra.TensorProduct.assoc R R C D E
local notation "aM" => _root_.TensorProduct.assoc R M N P
local notation "L" => ((X.externalTensor Y).externalTensor Z)
local notation "T" => (X.externalTensor (Y.externalTensor Z))
local notation "Lr" => (L.mapCoalgebra aC.toCoalgHom)
```

## Reuse: the coefficient associator is already bundled

Use the existing definition in `Mathlib.RingTheory.Coalgebra.TensorProduct`:

```lean
Coalgebra.TensorProduct.assoc R R C D E : CL ≃ₗc[R] CR
```

Do not introduce another coefficient coalgebra associator.
`Coalgebra.TensorProduct.assoc_toLinearEquiv` identifies its underlying
linear equivalence with `AlgebraTensorModule.assoc R R R C D E`;
`AlgebraTensorModule.assoc_eq` identifies the latter with
`_root_.TensorProduct.assoc R C D E`. The inverse is `aC.symm`, with
`CoalgEquiv.symm_toLinearEquiv` providing the inverse linear readback.
Thus these are the actual reassociations, not arbitrary equivalences
satisfying an assumed compatibility condition.

Existing pure-tensor readbacks are
`Coalgebra.TensorProduct.assoc_tmul` and
`Coalgebra.TensorProduct.assoc_symm_tmul`:

```lean
aC ((c ⊗ₜ[R] d) ⊗ₜ[R] e) = c ⊗ₜ[R] (d ⊗ₜ[R] e)
aC.symm (c ⊗ₜ[R] (d ⊗ₜ[R] e)) = (c ⊗ₜ[R] d) ⊗ₜ[R] e
```

For `c : C`, `d : D`, `e : E`, the preceding equations are existing APIs.
The counit and comultiplication contracts are already the fields
`aC.toCoalgHom.counit_comp` and `aC.toCoalgHom.map_comp_comul`:

```lean
Coalgebra.counit (R := R) (A := CR) ∘ₗ aC.toCoalgHom.toLinearMap =
  Coalgebra.counit (R := R) (A := CL)
_root_.TensorProduct.map aC.toCoalgHom.toLinearMap aC.toCoalgHom.toLinearMap ∘ₗ
    Coalgebra.comul (R := R) (A := CL) =
  Coalgebra.comul (R := R) (A := CR) ∘ₗ aC.toCoalgHom.toLinearMap
```

For the inverse, use the same existing fields on `aC.symm.toCoalgHom`,
with `CL` and `CR` interchanged. No compatibility theorem is assumed
as an additional hypothesis.

## The two transports have different jobs

`RightComodule.mapCoalgebra` pushes the coefficient forward; it does not
change the carrier. `RightComodule.transport` pushes the carrier forward
along a linear equivalence; it keeps the coefficient fixed.

| Expression | Coefficient | Carrier |
| --- | --- | --- |
| `L` | `CL` | `(M ⊗[R] N) ⊗[R] P` |
| `T` | `CR` | `M ⊗[R] (N ⊗[R] P)` |
| `Lr` | `CR` | `(M ⊗[R] N) ⊗[R] P` |
| `Lr.transport aM` | `CR` | `M ⊗[R] (N ⊗[R] P)` |
| `T.transport aM.symm` | `CR` | `(M ⊗[R] N) ⊗[R] P` |
| `T.mapCoalgebra aC.symm.toCoalgHom` | `CL` | `M ⊗[R] (N ⊗[R] P)` |
| `L.transport aM` | `CL` | `M ⊗[R] (N ⊗[R] P)` |
| `(T.mapCoalgebra aC.symm.toCoalgHom).transport aM.symm` | `CL` | `(M ⊗[R] N) ⊗[R] P` |

In particular, the forward coefficient map is `aC.toCoalgHom`, not its
inverse. The reverse coefficient map is `aC.symm.toCoalgHom`.
The existing coaction readbacks specialize as follows, with
`t : M ⊗[R] (N ⊗[R] P)`:

```lean
Lr.coaction =
  aC.toCoalgHom.toLinearMap.lTensor ((M ⊗[R] N) ⊗[R] P) ∘ₗ L.coaction
(Lr.transport aM).coaction t =
  aM.toLinearMap.rTensor CR (Lr.coaction (aM.symm t))
```

## Proposed colinearity and transport headers

The following headers are proposed additions in the namespace opened above.
They have no proof bodies here. In particular, colinearity is the conclusion,
not an input field or a hypothesis carrying the desired result.

```lean
theorem externalTensor_assoc_colinear :
    T.coaction ∘ₗ aM.toLinearMap =
      aM.toLinearMap.rTensor CR ∘ₗ Lr.coaction

theorem externalTensor_assoc_symm_colinear :
    Lr.coaction ∘ₗ aM.symm.toLinearMap =
      aM.symm.toLinearMap.rTensor CR ∘ₗ T.coaction

theorem externalTensor_transport_assoc :
    Lr.transport aM = T

theorem externalTensor_transport_assoc_symm :
    T.transport aM.symm = Lr

theorem externalTensor_mapCoalgebra_assoc_symm :
    T.mapCoalgebra aC.symm.toCoalgHom = L.transport aM

theorem externalTensor_mapCoalgebra_transport_assoc_symm :
    (T.mapCoalgebra aC.symm.toCoalgHom).transport aM.symm = L
```

The first two equations live over `CR`. The fifth and sixth equations
express the reverse coefficient direction over `CL`; they are not an
identification of `CL` and `CR` by definitional equality.

## Proposed morphisms and characteristic readbacks

Reuse `Coalgebra.RightComoduleHom`, not a new comodule-equivalence bundle.
These two definitions must use exactly the indicated linear maps, with
colinearity furnished by the preceding statements.

```lean
def externalTensorAssocHom : RightComoduleHom Lr T

def externalTensorAssocInvHom : RightComoduleHom T Lr

@[simp] theorem externalTensorAssocHom_toLinearMap :
    (externalTensorAssocHom X Y Z).toLinearMap = aM.toLinearMap

@[simp] theorem externalTensorAssocInvHom_toLinearMap :
    (externalTensorAssocInvHom X Y Z).toLinearMap = aM.symm.toLinearMap

@[simp] theorem externalTensorAssocHom_apply (t : (M ⊗[R] N) ⊗[R] P) :
    externalTensorAssocHom X Y Z t = aM t

@[simp] theorem externalTensorAssocInvHom_apply (t : M ⊗[R] (N ⊗[R] P)) :
    externalTensorAssocInvHom X Y Z t = aM.symm t
```

```lean
@[simp] theorem externalTensorAssocHom_tmul (m : M) (n : N) (p : P) :
    externalTensorAssocHom X Y Z ((m ⊗ₜ[R] n) ⊗ₜ[R] p) =
      m ⊗ₜ[R] (n ⊗ₜ[R] p)

@[simp] theorem externalTensorAssocInvHom_tmul (m : M) (n : N) (p : P) :
    externalTensorAssocInvHom X Y Z (m ⊗ₜ[R] (n ⊗ₜ[R] p)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] p

@[simp] theorem externalTensorAssocInvHom_comp_externalTensorAssocHom :
    (externalTensorAssocInvHom X Y Z).comp (externalTensorAssocHom X Y Z) =
      RightComoduleHom.id Lr

@[simp] theorem externalTensorAssocHom_comp_externalTensorAssocInvHom :
    (externalTensorAssocHom X Y Z).comp (externalTensorAssocInvHom X Y Z) =
      RightComoduleHom.id T
```

The object and hom operations `externalTensor`, including underlying-map,
pure-tensor, identity and composition readbacks for homs, already exist in
`AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct`.
They must not be redefined to implement this contract.

## Proposed naturality headers

The target carriers have three additional independent universes. The
coefficient coalgebras stay `C`, `D`, `E`; coefficient naturality under
additional coalgebra morphisms is not asserted here.

```lean
universe uM' uN' uP'
variable {M' : Type uM'} {N' : Type uN'} {P' : Type uP'}
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N'] [Module R N']
variable [AddCommMonoid P'] [Module R P']
variable {X0 : RightComodule R C M} {X1 : RightComodule R C M'}
variable {Y0 : RightComodule R D N} {Y1 : RightComodule R D N'}
variable {Z0 : RightComodule R E P} {Z1 : RightComodule R E P'}

theorem externalTensorAssocHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1)
    (h : RightComoduleHom Z0 Z1) :
    (f.externalTensor (g.externalTensor h)).comp
        (externalTensorAssocHom X0 Y0 Z0) =
      (externalTensorAssocHom X1 Y1 Z1).comp
        (((f.externalTensor g).externalTensor h).mapCoalgebra aC.toCoalgHom)
```

```lean
theorem externalTensorAssocInvHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1)
    (h : RightComoduleHom Z0 Z1) :
    (((f.externalTensor g).externalTensor h).mapCoalgebra aC.toCoalgHom).comp
        (externalTensorAssocInvHom X0 Y0 Z0) =
      (externalTensorAssocInvHom X1 Y1 Z1).comp
        (f.externalTensor (g.externalTensor h))

end Coalgebra.RightComodule
```

Both equalities are equalities of existing comodule homs over `CR`.
After forgetting to linear maps, the forward equality is precisely the
naturality of `TensorProduct.assoc`; the inverse equality is its inverse
naturality. They do not silently compare homs over different coalgebras.

## Proof approach and definition-use requirements

A proof should expand only through the existing coaction readbacks and
reduce the forward colinearity equation to naturality of the tensor
permutation defining `externalTensorCoaction`. Tensor induction applies
to arbitrary coaction values, which need not be pure tensors.

Reuse `RightComoduleHom.colinear_symm` for inverse colinearity, and
`RightComodule.transport_eq_iff_colinear` for the carrier-transport
readbacks. The reverse coefficient statements should use the inverse
coalgebra equivalence and the existing `mapCoalgebra_comp` and
`mapCoalgebra_id` APIs, not new transport infrastructure.

For naturality and inverse-composition readbacks, use
`RightComoduleHom.toLinearMap_injective`, existing external-tensor hom
readbacks, and `TensorProduct.map_map_comp_assoc_eq` and
`TensorProduct.map_map_comp_assoc_symm_eq`.

The regular-comodule identification `RightComodule.externalTensor_regular`
is an existing meaningful use of the object operation. Existing examples
include a nonidentity external tensor morphism over the semiring `ℕ`.
These are leads for checking hypotheses and nondegeneracy, not a substitute
for source-specific model data. The proposed morphisms must eventually be
used through their characteristic API, including a nontrivial associator
client; this document supplies no new such proof.

## Scope boundary

This contract addresses the associator first. Unit maps, the swap map,
pentagon and triangle coherence, and any source-specific coefficient
comparison formula require their own statements and are not established
by these headers. In particular, an associator compatibility statement
for source-specific comultiplication data must retain that data, not replace
it by the regular-comodule example or a scalar test.

A comparison with separately specified coactions requires their actual
coaction equations, coefficient maps and carrier maps. These data cannot
be inferred from a regular-comodule example or a scalar test. The generic
statements here fix their own canonical coefficient and carrier maps;
they do not assert an additional source-specific comparison.
