/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.AntipodeContraction

/-!
# Reconstruction from the antipode contraction

Applying the antipode contraction to the first leg of a right coaction, then
applying the given right action, recovers the original element. This uses
coassociativity, associativity of the action, left-antipode cancellation, and
the comodule counit.

## Main declarations

* `Coalgebra.RightComodule.rightAction_comp_antipodeContraction_rTensor_comp_coaction`
  is the reconstruction identity of linear maps.
* `Coalgebra.RightComodule.rightAction_antipodeContraction_coaction` evaluates
  that identity at an element.

## Implementation notes

Compatibility between the action and coaction is not required. In particular,
this identity does not assert that the contraction takes values in coinvariants,
or establish an inverse law inside the tensor product of coinvariants with the
Hopf algebra.

## References

The ordered reconstruction calculation is the first inverse law in
*Decomposition of a right Hopf module over a commutative semiring*, §6.
The contraction and balanced action reuse the right-comodule and
`TensorProduct.rightAction` constructions.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- The right action reconstructs an element from its coaction after applying
antipode contraction to the module leg. No action-coaction compatibility is needed. -/
theorem rightAction_comp_antipodeContraction_rTensor_comp_coaction
    (X : RightComodule R H M) :
    _root_.TensorProduct.rightAction R H M ∘ₗ
        X.antipodeContraction.rTensor H ∘ₗ X.coaction = LinearMap.id := by
  have hP : X.antipodeContraction =
      _root_.TensorProduct.rightAction R H M ∘ₗ
        (HopfAlgebra.antipode R).lTensor M ∘ₗ X.coaction := by
    ext m
    simpa only [LinearMap.comp_apply] using X.antipodeContraction_apply m
  have h_assoc :
      _root_.TensorProduct.rightAction R H M ∘ₗ
          (_root_.TensorProduct.rightAction R H M).rTensor H ∘ₗ
          ((HopfAlgebra.antipode R).lTensor M).rTensor H =
        _root_.TensorProduct.rightAction R H M ∘ₗ
          (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H).lTensor M ∘ₗ
          (_root_.TensorProduct.assoc R M H H).toLinearMap := by
    apply _root_.TensorProduct.ext_threefold
    intro m a b
    simpa only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      LinearEquiv.coe_coe, _root_.TensorProduct.assoc_tmul, LinearMap.mul'_apply] using
      _root_.TensorProduct.rightAction_rightAction_tmul R H M m
        (HopfAlgebra.antipode R a) b
  have h_unit :
      _root_.TensorProduct.rightAction R H M ∘ₗ (Algebra.linearMap R H).lTensor M =
        (_root_.TensorProduct.rid R M).toLinearMap := by
    apply _root_.TensorProduct.ext'
    intro m r
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
      LinearEquiv.coe_coe, _root_.TensorProduct.rid_tmul]
    rw [Algebra.algebraMap_eq_smul_one, _root_.TensorProduct.tmul_smul, map_smul]
    simp only [_root_.TensorProduct.rightAction_tmul, MulOpposite.op_one, one_smul]
  calc
    _root_.TensorProduct.rightAction R H M ∘ₗ
        X.antipodeContraction.rTensor H ∘ₗ X.coaction =
        (_root_.TensorProduct.rightAction R H M ∘ₗ
          (_root_.TensorProduct.rightAction R H M).rTensor H ∘ₗ
          ((HopfAlgebra.antipode R).lTensor M).rTensor H) ∘ₗ
          X.coaction.rTensor H ∘ₗ X.coaction := by
      rw [hP, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
      simp only [LinearMap.comp_assoc]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H).lTensor M ∘ₗ
        ((_root_.TensorProduct.assoc R M H H).toLinearMap ∘ₗ
          X.coaction.rTensor H ∘ₗ X.coaction) := by
      rw [h_assoc]
      simp only [LinearMap.comp_assoc]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H).lTensor M ∘ₗ
        ((comul (R := R) (A := H)).lTensor M ∘ₗ X.coaction) := by
      rw [X.coassoc]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H ∘ₗ
          comul (R := R) (A := H)).lTensor M ∘ₗ X.coaction := by
      simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        (Algebra.linearMap R H ∘ₗ counit (R := R) (A := H)).lTensor M ∘ₗ
        X.coaction := by
      rw [HopfAlgebra.mul_antipode_rTensor_comul]
    _ = (_root_.TensorProduct.rid R M).toLinearMap ∘ₗ
        (counit (R := R) (A := H)).lTensor M ∘ₗ X.coaction := by
      simp only [LinearMap.lTensor_comp, ← LinearMap.comp_assoc]
      rw [h_unit]
    _ = LinearMap.id := by
      ext m
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] using
        X.rid_counit_coaction m

/-- Pointwise reconstruction by the given right action after antipode contraction
on the first leg of the coaction. -/
@[simp] theorem rightAction_antipodeContraction_coaction
    (X : RightComodule R H M) (m : M) :
    _root_.TensorProduct.rightAction R H M
        (X.antipodeContraction.rTensor H (X.coaction m)) = m := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun X.rightAction_comp_antipodeContraction_rTensor_comp_coaction m

end Coalgebra.RightComodule
