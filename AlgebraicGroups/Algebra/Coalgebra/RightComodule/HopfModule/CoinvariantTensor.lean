/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Cofree
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.Basic
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace
public import AlgebraicGroups.Algebra.Module.TensorProductAction
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# The action map from coinvariants tensored with a bialgebra

For a right comodule `X` with a given right action of the bialgebra `H` on its
underlying module, `coinvariantTensorToModule` sends `c ⊗ h` to
`MulOpposite.op h • (c : M)`. Right multiplication on the second tensor factor
intertwines this map with the given action.

The map and its right-action identity need only a bialgebra: neither an antipode
nor compatibility between the action and coaction is required. Given an explicit
Hopf-module compatibility proof, the map also intertwines the canonical cofree
coaction with the coaction of `X`. The coinvariants retain just their submodule
structure; no action of `H` on them or injectivity of their tensored inclusion
is asserted. For the regular comodule, the coinvariant unit shows that the
forward map is surjective.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- Act on the underlying module after tensoring the inclusion of the coinvariants
with the identity of the bialgebra. -/
def coinvariantTensorToModule (X : RightComodule R H M) :
    (X.weightSpace (1 : H)) ⊗[R] H →ₗ[R] M :=
  (_root_.TensorProduct.rightAction R H M).comp ((X.weightSpace (1 : H)).subtype.rTensor H)

/-- The forward map is the existing tensor action after the tensored inclusion. -/
theorem coinvariantTensorToModule_apply (X : RightComodule R H M)
    (z : (X.weightSpace (1 : H)) ⊗[R] H) :
    coinvariantTensorToModule X z =
      _root_.TensorProduct.rightAction R H M ((X.weightSpace (1 : H)).subtype.rTensor H z) :=
  rfl

/-- On pure tensors the forward map is the original right action. -/
@[simp] theorem coinvariantTensorToModule_tmul (X : RightComodule R H M)
    (c : X.weightSpace (1 : H)) (h : H) :
    coinvariantTensorToModule X (c ⊗ₜ[R] h) = MulOpposite.op h • (c : M) := by
  simp only [coinvariantTensorToModule_apply, LinearMap.rTensor_tmul,
    Submodule.subtype_apply, _root_.TensorProduct.rightAction_tmul]

/-- Right multiplication on the second tensor factor preserves the given right action. -/
theorem coinvariantTensorToModule_map_mulRight (X : RightComodule R H M) (h : H)
    (z : (X.weightSpace (1 : H)) ⊗[R] H) :
    coinvariantTensorToModule X
        (_root_.TensorProduct.map
          (LinearMap.id : X.weightSpace (1 : H) →ₗ[R] X.weightSpace (1 : H))
          (LinearMap.mulRight R h) z) =
      MulOpposite.op h • coinvariantTensorToModule X z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul c k =>
    simpa only [_root_.TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulRight_apply,
      coinvariantTensorToModule_tmul, _root_.TensorProduct.rightAction_tmul] using
      (_root_.TensorProduct.rightAction_rightAction_tmul R H M (c : M) k h).symm
  | add z w hz hw => simp only [map_add, hz, hw, smul_add]

/-- The action map on coinvariants intertwines the cofree coaction with the
coaction of a right Hopf module. The cofree coaction is the inverse associator
after comultiplication on the second tensor factor. -/
theorem coinvariantTensorToModule_colinear (X : RightComodule R H M)
    (hX : X.IsHopfModule) :
    X.coaction ∘ₗ coinvariantTensorToModule X =
      (coinvariantTensorToModule X).rTensor H ∘ₗ
        (cofree R H (X.weightSpace (1 : H))).coaction := by
  apply _root_.TensorProduct.ext'
  intro c h
  change X.coaction (coinvariantTensorToModule X (c ⊗ₜ[R] h)) =
    (coinvariantTensorToModule X).rTensor H
      ((cofree R H (X.weightSpace (1 : H))).coaction (c ⊗ₜ[R] h))
  rw [coinvariantTensorToModule_tmul, cofree_coaction_tmul,
    hX.coaction_smul, X.coaction_weightSpace (1 : H) c]
  generalize Coalgebra.comul (R := R) h = t
  induction t using _root_.TensorProduct.inductionOn with
  | tmul a b =>
    simp only [_root_.TensorProduct.tensorTensorTensorComm_tmul,
      _root_.TensorProduct.map_tmul, _root_.TensorProduct.rightAction_tmul,
      LinearMap.mul'_apply, one_mul, _root_.TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, coinvariantTensorToModule_tmul]
  | add t s ht hs => simp only [_root_.TensorProduct.tmul_add, map_add, ht, hs]

/-- For the regular comodule the forward map is surjective: the coinvariant unit
acts on every element of the bialgebra by right multiplication. -/
theorem regular_coinvariantTensorToModule_surjective :
    Function.Surjective (coinvariantTensorToModule (regular R H)) := by
  intro h
  have h1 : (1 : H) ∈ (regular R H).weightSpace (1 : H) := by
    rw [mem_weightSpace, regular_coaction]
    simpa only [Algebra.TensorProduct.one_def] using
      (Bialgebra.comul_one (R := R) (A := H))
  refine ⟨(⟨1, h1⟩ : (regular R H).weightSpace (1 : H)) ⊗ₜ[R] h, ?_⟩
  simp only [coinvariantTensorToModule_tmul, op_smul_eq_mul, one_mul]

end Coalgebra.RightComodule
