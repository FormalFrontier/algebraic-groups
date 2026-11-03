/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.AntipodeContraction
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.Basic
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace
public import AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication
public import AlgebraicGroups.Algebra.HopfAlgebra.TensorCancellation

/-!
# The canonical map to coinvariants of a right Hopf module

For a specified right comodule with a compatible given right action, the antipode
contraction has coinvariant values. Its corestriction therefore defines an
`R`-linear map to the existing weight space at `1`.

The proof keeps the noncommutative multiplication order: the four-factor map
sends `m ⊗ a ⊗ b ⊗ c` to `(m · S(c)) ⊗ a * S(b)`. Compatibility and
anti-comultiplicativity of the antipode identify the coaction of the contraction
with this map applied to the iterated coaction. Comodule coassociativity and the
ordered three-factor Hopf cancellation then give `ρ(P(m)) = P(m) ⊗ 1`.

The corestriction is made before any tensoring. No action on the coinvariant
submodule, injectivity of a tensored inclusion, or flatness is required.

## References

* *Decomposition of a right Hopf module over a commutative semiring*, §4.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

local notation "Δ" => comul (R := R) (A := H)
local notation "S" => HopfAlgebra.antipode R (A := H)
local notation "μ" => LinearMap.mul' R H
local notation "act" => _root_.TensorProduct.rightAction R H M

/-- The balanced four-factor map used to compute the coaction of the contraction. -/
private def coinvariantCoactionMap :
    M ⊗[R] (H ⊗[R] (H ⊗[R] H)) →ₗ[R] M ⊗[R] H :=
  (act).rTensor H ∘ₗ (_root_.TensorProduct.assoc R M H H).symm.toLinearMap ∘ₗ
    ((S).rTensor H ∘ₗ (_root_.TensorProduct.comm R H H).toLinearMap ∘ₗ
      (μ ∘ₗ (S).lTensor H).rTensor H ∘ₗ
      (_root_.TensorProduct.assoc R H H H).symm.toLinearMap).lTensor M

private theorem coinvariantCoactionMap_tmul (m : M) (a b c : H) :
    coinvariantCoactionMap (m ⊗ₜ[R] (a ⊗ₜ[R] (b ⊗ₜ[R] c))) =
      (MulOpposite.op (S c) • m) ⊗ₜ[R] (a * S b) := by
  simp only [coinvariantCoactionMap, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, _root_.TensorProduct.assoc_symm_tmul, _root_.TensorProduct.comm_tmul,
    LinearEquiv.coe_coe, LinearMap.mul'_apply, _root_.TensorProduct.rightAction_tmul]

/-- The same four-factor map in the parenthesization used by compatibility. -/
private theorem coinvariantCoactionMap_assoc :
    coinvariantCoactionMap (R := R) (H := H) (M := M) ∘ₗ
        (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap =
      _root_.TensorProduct.map act μ ∘ₗ
        (_root_.TensorProduct.tensorTensorTensorComm R M H H H).toLinearMap ∘ₗ
          (_root_.TensorProduct.map S S ∘ₗ
            (_root_.TensorProduct.comm R H H).toLinearMap).lTensor (M ⊗[R] H) := by
  apply _root_.TensorProduct.ext_fourfold'
  intro m a b c
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, _root_.TensorProduct.map_tmul,
    _root_.TensorProduct.assoc_tmul, _root_.TensorProduct.comm_tmul,
    _root_.TensorProduct.tensorTensorTensorComm_tmul, LinearEquiv.coe_coe,
    coinvariantCoactionMap_tmul, LinearMap.mul'_apply,
    _root_.TensorProduct.rightAction_tmul]

/-- Ordered Hopf cancellation after applying the given action to the surviving factor. -/
private theorem coinvariantCoactionMap_comul :
    coinvariantCoactionMap (R := R) (H := H) (M := M) ∘ₗ
        ((Δ).lTensor H ∘ₗ Δ).lTensor M =
      (_root_.TensorProduct.mk R M H).flip (1 : H) ∘ₗ act ∘ₗ (S).lTensor M := by
  apply _root_.TensorProduct.ext'
  intro m h
  simpa only [coinvariantCoactionMap, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, _root_.TensorProduct.assoc_symm_tmul, LinearEquiv.coe_coe,
    LinearMap.flip_apply, _root_.TensorProduct.mk_apply] using
    congrArg
      (fun t : H ⊗[R] H =>
        (act).rTensor H ((_root_.TensorProduct.assoc R M H H).symm (m ⊗ₜ[R] t)))
      (HopfAlgebra.antipode_tensor_mul_antipode_comul_apply (R := R) h)

/-- The antipode contraction of a compatible right Hopf module is coinvariant.
The compatibility proof is an explicit argument, not a typeclass or a projection-law
assumption. All actions and scalar modules are the given ones. -/
theorem antipodeContraction_mem_weightSpace (X : RightComodule R H M)
    (hX : X.IsHopfModule) (m : M) :
    X.antipodeContraction m ∈ X.weightSpace (1 : H) := by
  have hP : X.antipodeContraction = act ∘ₗ (S).lTensor M ∘ₗ X.coaction := by
    apply LinearMap.ext
    intro n
    exact X.antipodeContraction_apply n
  have hcompat :
      X.coaction ∘ₗ act ∘ₗ (S).lTensor M =
        coinvariantCoactionMap ∘ₗ
          (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
            _root_.TensorProduct.map X.coaction Δ := by
    apply _root_.TensorProduct.ext'
    intro n h
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, _root_.TensorProduct.map_tmul,
      _root_.TensorProduct.rightAction_tmul, LinearEquiv.coe_coe]
    rw [hX.coaction_smul, HopfAlgebra.comul_antipode]
    simpa only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun
        (coinvariantCoactionMap_assoc (R := R) (H := H) (M := M))
        (X.coaction n ⊗ₜ[R] Δ h)).symm
  have hnat :
      (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
          (Δ).lTensor (M ⊗[R] H) =
        ((Δ).lTensor H).lTensor M ∘ₗ (_root_.TensorProduct.assoc R M H H).toLinearMap := by
    simpa only [LinearMap.lTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.map_map_comp_assoc_eq
        (LinearMap.id : M →ₗ[R] M) (LinearMap.id : H →ₗ[R] H) Δ).symm
  have hiter :
      (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
          _root_.TensorProduct.map X.coaction Δ ∘ₗ X.coaction =
        ((Δ).lTensor H ∘ₗ Δ).lTensor M ∘ₗ X.coaction := by
    calc
      (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
          _root_.TensorProduct.map X.coaction Δ ∘ₗ X.coaction =
          ((_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
            (Δ).lTensor (M ⊗[R] H)) ∘ₗ (X.coaction.rTensor H ∘ₗ X.coaction) := by
              rw [← LinearMap.lTensor_comp_rTensor]
              simp only [LinearMap.comp_assoc]
      _ = (((Δ).lTensor H).lTensor M ∘ₗ
          (_root_.TensorProduct.assoc R M H H).toLinearMap) ∘ₗ
            (X.coaction.rTensor H ∘ₗ X.coaction) := by rw [hnat]
      _ = ((Δ).lTensor H).lTensor M ∘ₗ
          ((_root_.TensorProduct.assoc R M H H).toLinearMap ∘ₗ
            X.coaction.rTensor H ∘ₗ X.coaction) := by
              simp only [LinearMap.comp_assoc]
      _ = ((Δ).lTensor H).lTensor M ∘ₗ ((Δ).lTensor M ∘ₗ X.coaction) := by
            rw [X.coassoc]
      _ = ((Δ).lTensor H ∘ₗ Δ).lTensor M ∘ₗ X.coaction := by
            rw [LinearMap.lTensor_comp]
            simp only [LinearMap.comp_assoc]
  have hc :
      X.coaction ∘ₗ X.antipodeContraction =
        (_root_.TensorProduct.mk R M H).flip (1 : H) ∘ₗ X.antipodeContraction := by
    calc
      X.coaction ∘ₗ X.antipodeContraction =
          (X.coaction ∘ₗ act ∘ₗ (S).lTensor M) ∘ₗ X.coaction := by
            rw [hP]
            simp only [LinearMap.comp_assoc]
      _ = (coinvariantCoactionMap ∘ₗ
          (_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
            _root_.TensorProduct.map X.coaction Δ) ∘ₗ X.coaction := by rw [hcompat]
      _ = coinvariantCoactionMap ∘ₗ
          ((_root_.TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ
            _root_.TensorProduct.map X.coaction Δ ∘ₗ X.coaction) := by
              simp only [LinearMap.comp_assoc]
      _ = coinvariantCoactionMap ∘ₗ
          (((Δ).lTensor H ∘ₗ Δ).lTensor M ∘ₗ X.coaction) := by rw [hiter]
      _ = (coinvariantCoactionMap ∘ₗ ((Δ).lTensor H ∘ₗ Δ).lTensor M) ∘ₗ
          X.coaction := by simp only [LinearMap.comp_assoc]
      _ = ((_root_.TensorProduct.mk R M H).flip (1 : H) ∘ₗ act ∘ₗ (S).lTensor M) ∘ₗ
          X.coaction := by rw [coinvariantCoactionMap_comul]
      _ = (_root_.TensorProduct.mk R M H).flip (1 : H) ∘ₗ X.antipodeContraction := by
            rw [hP]
            simp only [LinearMap.comp_assoc]
  apply (X.mem_weightSpace (1 : H)).mpr
  exact LinearMap.congr_fun hc m

/-- The canonical antipode contraction, corestricted to the original coinvariant
submodule. Coinvariance is proved from compatibility before making this map. -/
def coinvariantProjection (X : RightComodule R H M) (hX : X.IsHopfModule) :
    M →ₗ[R] X.weightSpace (1 : H) :=
  X.antipodeContraction.codRestrict (X.weightSpace (1 : H))
    (X.antipodeContraction_mem_weightSpace hX)

/-- The corestriction does not change the underlying contraction. -/
@[simp] theorem coe_coinvariantProjection (X : RightComodule R H M)
    (hX : X.IsHopfModule) (m : M) :
    (X.coinvariantProjection hX m : M) = X.antipodeContraction m := rfl

/-- Composing the canonical projection with the original subtype inclusion recovers
exactly the antipode-contraction endomorphism. -/
@[simp] theorem subtype_comp_coinvariantProjection (X : RightComodule R H M)
    (hX : X.IsHopfModule) :
    (X.weightSpace (1 : H)).subtype ∘ₗ X.coinvariantProjection hX =
      X.antipodeContraction := by
  apply LinearMap.ext
  intro m
  exact X.coe_coinvariantProjection hX m

end Coalgebra.RightComodule
