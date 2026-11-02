/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.Algebra.Module.TensorProductAction
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Right Hopf-module compatibility

A specified right comodule with a given right algebra action is a right Hopf
module when its balanced action is colinear. The source comodule is the existing
external tensor product with the regular comodule, followed by the coalgebra
map given by multiplication. Thus no additional tensor-comodule construction is
needed.

This compatibility uses only a bialgebra over a commutative semiring, not an
antipode. Its ordered diagram reads
`ρ(m · h) = ∑ (m₀ · h₁) ⊗ (m₁ * h₂)` even for noncommutative coefficients.
The right regular module is compatible by multiplicativity of comultiplication.
All scalar modules and opposite-algebra actions are the given ones, in
independent universes.

Specialization to a Hopf algebra uses its inherited bialgebra and algebra
parents: the balanced action, predicate, diagram and regular comodule are these
same values, with no additional parent instances or change of scalar action.
Coinvariants remain the existing weight space at `1`; no decomposition or
antipode-dependent construction is introduced here.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- A right Hopf module is a specified comodule whose given balanced right action is
colinear against the tensor product with the regular comodule. This condition
already makes sense for a bialgebra. -/
def IsHopfModule (X : RightComodule R H M) : Prop :=
  X.coaction ∘ₗ _root_.TensorProduct.rightAction R H M =
    (_root_.TensorProduct.rightAction R H M).rTensor H ∘ₗ
      ((X.externalTensor (regular R H)).mapCoalgebra (Bialgebra.mulCoalgHom R H)).coaction

private theorem action_tensor_regular_coaction (X : RightComodule R H M) :
    (_root_.TensorProduct.rightAction R H M).rTensor H ∘ₗ
        ((X.externalTensor (regular R H)).mapCoalgebra (Bialgebra.mulCoalgHom R H)).coaction =
      _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M) (LinearMap.mul' R H) ∘ₗ
        (_root_.TensorProduct.tensorTensorTensorComm R M H H H).toLinearMap ∘ₗ
          _root_.TensorProduct.map X.coaction (comul (R := R) (A := H)) := by
  apply _root_.TensorProduct.ext'
  intro m h
  simp only [LinearMap.comp_apply, mapCoalgebra_coaction_apply, externalTensor_coaction,
    externalTensorCoaction_tmul, regular_coaction, _root_.TensorProduct.map_tmul,
    LinearEquiv.coe_coe]
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    CoalgHom.toLinearMap_eq_coe, Bialgebra.toLinearMap_mulCoalgHom]

/-- The colinearity condition is exactly the ordered four-factor compatibility diagram. -/
theorem isHopfModule_iff_diagram (X : RightComodule R H M) :
    X.IsHopfModule ↔
      X.coaction ∘ₗ _root_.TensorProduct.rightAction R H M =
        _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M) (LinearMap.mul' R H) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R M H H H).toLinearMap ∘ₗ
            _root_.TensorProduct.map X.coaction (comul (R := R) (A := H)) := by
  rw [IsHopfModule, action_tensor_regular_coaction]

/-- Compatibility can be constructed or tested on pure tensors without choosing tensor
presentations. The second coefficient is multiplied in the order `m₁ * h₂`. -/
theorem isHopfModule_iff (X : RightComodule R H M) :
    X.IsHopfModule ↔ ∀ m h,
      X.coaction (MulOpposite.op h • m) =
        _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M) (LinearMap.mul' R H)
          (_root_.TensorProduct.tensorTensorTensorComm R M H H H
            (X.coaction m ⊗ₜ[R] comul (R := R) h)) := by
  rw [isHopfModule_iff_diagram]
  constructor
  · intro hX m h
    simpa only [LinearMap.comp_apply, _root_.TensorProduct.rightAction_tmul,
      _root_.TensorProduct.map_tmul, LinearEquiv.coe_coe] using
      LinearMap.congr_fun hX (m ⊗ₜ[R] h)
  · intro hX
    apply _root_.TensorProduct.ext'
    intro m h
    simpa only [LinearMap.comp_apply, _root_.TensorProduct.rightAction_tmul,
      _root_.TensorProduct.map_tmul, LinearEquiv.coe_coe] using hX m h

/-- The pure-tensor compatibility formula constructs right Hopf-module compatibility. -/
theorem isHopfModule_of_coaction_smul (X : RightComodule R H M)
    (hX : ∀ m h, X.coaction (MulOpposite.op h • m) =
      _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M) (LinearMap.mul' R H)
        (_root_.TensorProduct.tensorTensorTensorComm R M H H H
          (X.coaction m ⊗ₜ[R] comul (R := R) h))) : X.IsHopfModule :=
  (isHopfModule_iff X).mpr hX

/-- Elimination of compatibility gives the ordered coaction formula for the given action. -/
theorem IsHopfModule.coaction_smul {X : RightComodule R H M} (hX : X.IsHopfModule)
    (m : M) (h : H) :
    X.coaction (MulOpposite.op h • m) =
      _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M) (LinearMap.mul' R H)
        (_root_.TensorProduct.tensorTensorTensorComm R M H H H
          (X.coaction m ⊗ₜ[R] comul (R := R) h)) :=
  (isHopfModule_iff X).mp hX m h

/-- A compatible balanced action bundled as a morphism of the existing comodules. -/
def IsHopfModule.actionHom {X : RightComodule R H M} (hX : X.IsHopfModule) :
    RightComoduleHom
      ((X.externalTensor (regular R H)).mapCoalgebra (Bialgebra.mulCoalgHom R H)) X where
  toLinearMap := _root_.TensorProduct.rightAction R H M
  colinear := hX

/-- The bundled action has the original balanced action as its underlying linear map. -/
@[simp] theorem IsHopfModule.actionHom_toLinearMap {X : RightComodule R H M}
    (hX : X.IsHopfModule) :
    hX.actionHom.toLinearMap = _root_.TensorProduct.rightAction R H M := rfl

/-- The bundled action acts on pure tensors by the given right action. -/
@[simp] theorem IsHopfModule.actionHom_tmul {X : RightComodule R H M}
    (hX : X.IsHopfModule) (m : M) (h : H) :
    hX.actionHom (m ⊗ₜ[R] h) = MulOpposite.op h • m :=
  _root_.TensorProduct.rightAction_tmul R H M m h

/-- Right multiplication and the regular coaction form a right Hopf module over any
bialgebra. No antipode is needed. -/
theorem regular_isHopfModule : (regular R H).IsHopfModule := by
  apply isHopfModule_of_coaction_smul
  intro x h
  have hmul :
      _root_.TensorProduct.map (_root_.TensorProduct.rightAction R H H) (LinearMap.mul' R H) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R H H H H).toLinearMap =
        LinearMap.mul' R (H ⊗[R] H) := by
    apply _root_.TensorProduct.ext_fourfold'
    intro a b c d
    simp only [LinearMap.comp_apply, _root_.TensorProduct.tensorTensorTensorComm_tmul,
      _root_.TensorProduct.map_tmul, _root_.TensorProduct.rightAction_tmul, op_smul_eq_mul,
      LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.coe_coe]
  rw [op_smul_eq_mul, regular_coaction, regular_coaction, Bialgebra.comul_mul]
  exact (LinearMap.congr_fun hmul
    (comul (R := R) x ⊗ₜ[R] comul (R := R) h)).symm

/-- Regular right multiplication, viewed through the compatible action API, retains its
ordinary multiplication map. -/
theorem regular_actionHom_toLinearMap :
    (regular_isHopfModule (R := R) (H := H)).actionHom.toLinearMap =
      LinearMap.mul' R H := by
  rw [IsHopfModule.actionHom_toLinearMap, _root_.TensorProduct.rightAction_eq_mul']

end Coalgebra.RightComodule
