/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.AntipodeContraction
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.Basic
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace

/-!
# Antipode contraction on coinvariants

For a right Hopf module, antipode contraction sends the right action of `h`
on a coinvariant `c` to `ε(h) • c`. The proof uses the ordered cancellation
`∑ h₁ * S(h₂) = ε(h) • 1` and associativity of the given right action.
Coinvariants have only their existing submodule structure over the base.

The contraction also fixes every coinvariant. This retraction formula needs
no compatibility between the action and the coaction.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- Antipode contraction of the right action on a coinvariant is the counit
of the acting element times that coinvariant. -/
theorem antipodeContraction_smul_coe (X : RightComodule R H M)
    (hX : X.IsHopfModule) (c : X.weightSpace (1 : H)) (h : H) :
    X.antipodeContraction (MulOpposite.op h • (c : M)) =
      Coalgebra.counit (R := R) h • (c : M) := by
  -- The four-factor compatibility diagram contracts in the order h₁ * S(h₂).
  have hcontract (t : H ⊗[R] H) :
      _root_.TensorProduct.rightAction R H M
          ((HopfAlgebra.antipode R).lTensor M
            (_root_.TensorProduct.map (_root_.TensorProduct.rightAction R H M)
              (LinearMap.mul' R H)
              (_root_.TensorProduct.tensorTensorTensorComm R M H H H
                (((c : M) ⊗ₜ[R] (1 : H)) ⊗ₜ[R] t)))) =
        _root_.TensorProduct.rightAction R H M
          ((c : M) ⊗ₜ[R]
            LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H t)) := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul a b =>
        simp only [_root_.TensorProduct.tensorTensorTensorComm_tmul,
          _root_.TensorProduct.map_tmul, LinearMap.mul'_apply, one_mul,
          LinearMap.lTensor_tmul]
        exact _root_.TensorProduct.rightAction_rightAction_tmul R H M
          (c : M) a (HopfAlgebra.antipode R b)
    | add t u ht hu =>
        simp only [_root_.TensorProduct.tmul_add, map_add, ht, hu]
  rw [antipodeContraction_apply, hX.coaction_smul,
    X.coaction_weightSpace (1 : H) c, hcontract,
    HopfAlgebra.mul_antipode_lTensor_comul_apply,
    _root_.TensorProduct.rightAction_tmul]
  simpa only [MulOpposite.algebraMap_apply] using
    (algebraMap_smul Hᵐᵒᵖ (Coalgebra.counit (R := R) h) (c : M))

/-- Antipode contraction fixes coinvariants, without a Hopf-module compatibility
assumption. -/
theorem antipodeContraction_coe (X : RightComodule R H M)
    (c : X.weightSpace (1 : H)) :
    X.antipodeContraction (c : M) = (c : M) := by
  rw [antipodeContraction_apply, X.coaction_weightSpace (1 : H) c,
    LinearMap.lTensor_tmul, HopfAlgebra.antipode_one,
    _root_.TensorProduct.rightAction_tmul]
  exact one_smul Hᵐᵒᵖ (c : M)

end Coalgebra.RightComodule
