/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.AntipodeContractionCoinvariant
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.AntipodeContractionReconstruction
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.CoinvariantProjection
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.CoinvariantTensor

/-!
# Decomposition of a right Hopf module

A right Hopf module is linearly equivalent to its coinvariants tensored with the
Hopf algebra. The forward map is the given right action on coinvariant elements.
The inverse applies the canonical coinvariant projection to the module leg of
the coaction, with target directly in the tensor product of coinvariants.

The first inverse law is reconstruction by the antipode contraction. For the
second, the projection of the action on a coinvariant is the counit times that
coinvariant. Thus projection after the forward map is the canonical cofree
projection. Colinearity of the forward map and the cofree counit identity prove
the inverse law inside the tensor product of coinvariants, without any claim
that tensoring the subtype inclusion preserves injectivity.

The coinvariants have only their original module structure over the base.
Right multiplication acts on the second tensor factor; the equivalence and its
inverse intertwine this operation with the given right action.

## Main declarations

* `Coalgebra.RightComodule.toCoinvariantsTensor` is the coaction followed by
  the canonical coinvariant projection on its module leg.
* `Coalgebra.RightComodule.coinvariantsTensorEquiv` is the decomposition
  equivalence, with forward map `coinvariantTensorToModule`.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969: the classical
  fundamental theorem of Hopf modules over fields.
* *Decomposition of a right Hopf module over a commutative semiring*, §6:
  an independent direct derivation over commutative semirings.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- The canonical projection fixes a coinvariant, as an equality in the original
coinvariant submodule, before any tensoring. -/
@[simp] theorem coinvariantProjection_coe (X : RightComodule R H M)
    (hX : X.IsHopfModule) (c : X.weightSpace (1 : H)) :
    X.coinvariantProjection hX (c : M) = c := by
  apply Subtype.ext
  rw [coe_coinvariantProjection]
  exact X.antipodeContraction_coe c

/-- Projection of the right action on a coinvariant is counit scaling inside the
coinvariant submodule. No action of the Hopf algebra on that submodule is used. -/
@[simp] theorem coinvariantProjection_smul_coe (X : RightComodule R H M)
    (hX : X.IsHopfModule) (c : X.weightSpace (1 : H)) (h : H) :
    X.coinvariantProjection hX (MulOpposite.op h • (c : M)) =
      Coalgebra.counit (R := R) h • c := by
  apply Subtype.ext
  change (X.coinvariantProjection hX (MulOpposite.op h • (c : M)) : M) =
    Coalgebra.counit (R := R) h • (c : M)
  rw [coe_coinvariantProjection]
  exact X.antipodeContraction_smul_coe hX c h

/-- The inverse decomposition map has target directly in coinvariants tensored
with the Hopf algebra. -/
def toCoinvariantsTensor (X : RightComodule R H M) (hX : X.IsHopfModule) :
    M →ₗ[R] (X.weightSpace (1 : H)) ⊗[R] H :=
  (X.coinvariantProjection hX).rTensor H ∘ₗ X.coaction

/-- The inverse map applies the actual canonical projection to the module leg
of the coaction. -/
theorem toCoinvariantsTensor_apply (X : RightComodule R H M)
    (hX : X.IsHopfModule) (m : M) :
    X.toCoinvariantsTensor hX m =
      (X.coinvariantProjection hX).rTensor H (X.coaction m) := rfl

/-- Acting after the inverse decomposition map reconstructs the original module
by the antipode-contraction reconstruction identity. -/
theorem coinvariantTensorToModule_comp_toCoinvariantsTensor
    (X : RightComodule R H M) (hX : X.IsHopfModule) :
    X.coinvariantTensorToModule ∘ₗ X.toCoinvariantsTensor hX = LinearMap.id := by
  have hθ : X.coinvariantTensorToModule =
      _root_.TensorProduct.rightAction R H M ∘ₗ
        (X.weightSpace (1 : H)).subtype.rTensor H := by
    apply LinearMap.ext
    intro z
    exact X.coinvariantTensorToModule_apply z
  calc
    X.coinvariantTensorToModule ∘ₗ X.toCoinvariantsTensor hX =
        _root_.TensorProduct.rightAction R H M ∘ₗ
          ((X.weightSpace (1 : H)).subtype.rTensor H ∘ₗ
            (X.coinvariantProjection hX).rTensor H) ∘ₗ X.coaction := by
      rw [hθ, toCoinvariantsTensor]
      simp only [LinearMap.comp_assoc]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        ((X.weightSpace (1 : H)).subtype ∘ₗ
          X.coinvariantProjection hX).rTensor H ∘ₗ X.coaction := by
      rw [LinearMap.rTensor_comp]
    _ = _root_.TensorProduct.rightAction R H M ∘ₗ
        X.antipodeContraction.rTensor H ∘ₗ X.coaction := by
      rw [subtype_comp_coinvariantProjection]
    _ = LinearMap.id :=
      X.rightAction_comp_antipodeContraction_rTensor_comp_coaction

/-- The second inverse identity is proved in the tensor product of coinvariants
itself, using the existing cofree coaction and its counit identity. -/
theorem toCoinvariantsTensor_comp_coinvariantTensorToModule
    (X : RightComodule R H M) (hX : X.IsHopfModule) :
    X.toCoinvariantsTensor hX ∘ₗ X.coinvariantTensorToModule = LinearMap.id := by
  have hPθ : X.coinvariantProjection hX ∘ₗ X.coinvariantTensorToModule =
      cofreeProjection R H (X.weightSpace (1 : H)) := by
    apply _root_.TensorProduct.ext'
    intro c h
    simp only [LinearMap.comp_apply, coinvariantTensorToModule_tmul,
      coinvariantProjection_smul_coe, cofreeProjection_tmul]
  calc
    X.toCoinvariantsTensor hX ∘ₗ X.coinvariantTensorToModule =
        (X.coinvariantProjection hX).rTensor H ∘ₗ
          (X.coaction ∘ₗ X.coinvariantTensorToModule) := by
      rw [toCoinvariantsTensor]
      simp only [LinearMap.comp_assoc]
    _ = (X.coinvariantProjection hX).rTensor H ∘ₗ
        ((X.coinvariantTensorToModule).rTensor H ∘ₗ
          (cofree R H (X.weightSpace (1 : H))).coaction) := by
      rw [X.coinvariantTensorToModule_colinear hX]
    _ = (X.coinvariantProjection hX ∘ₗ X.coinvariantTensorToModule).rTensor H ∘ₗ
        (cofree R H (X.weightSpace (1 : H))).coaction := by
      rw [LinearMap.rTensor_comp]
      simp only [LinearMap.comp_assoc]
    _ = (cofreeProjection R H (X.weightSpace (1 : H))).rTensor H ∘ₗ
        (cofree R H (X.weightSpace (1 : H))).coaction := by rw [hPθ]
    _ = LinearMap.id := cofreeProjection_rTensor_comp_coaction

/-- The forward map after the inverse is the identity on the original module. -/
@[simp] theorem coinvariantTensorToModule_toCoinvariantsTensor
    (X : RightComodule R H M) (hX : X.IsHopfModule) (m : M) :
    X.coinvariantTensorToModule (X.toCoinvariantsTensor hX m) = m := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (X.coinvariantTensorToModule_comp_toCoinvariantsTensor hX) m

/-- The inverse after the forward map is the identity inside coinvariants
tensored with the Hopf algebra. -/
@[simp] theorem toCoinvariantsTensor_coinvariantTensorToModule
    (X : RightComodule R H M) (hX : X.IsHopfModule)
    (z : (X.weightSpace (1 : H)) ⊗[R] H) :
    X.toCoinvariantsTensor hX (X.coinvariantTensorToModule z) = z := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (X.toCoinvariantsTensor_comp_coinvariantTensorToModule hX) z

/-- The inverse recovers a pure tensor from the action on a coinvariant. -/
@[simp] theorem toCoinvariantsTensor_smul_coe (X : RightComodule R H M)
    (hX : X.IsHopfModule) (c : X.weightSpace (1 : H)) (h : H) :
    X.toCoinvariantsTensor hX (MulOpposite.op h • (c : M)) = c ⊗ₜ[R] h := by
  simpa only [coinvariantTensorToModule_tmul] using
    X.toCoinvariantsTensor_coinvariantTensorToModule hX (c ⊗ₜ[R] h)

/-- A right Hopf module is linearly equivalent to its original coinvariants
tensored with the Hopf algebra, by the given right action and canonical projection.

This is a commutative-semiring version of the classical fundamental theorem of
Hopf modules over fields; see M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969.
The independent direct semiring derivation is given in
*Decomposition of a right Hopf module over a commutative semiring*, §6. -/
def coinvariantsTensorEquiv (X : RightComodule R H M) (hX : X.IsHopfModule) :
    (X.weightSpace (1 : H)) ⊗[R] H ≃ₗ[R] M :=
  { X.coinvariantTensorToModule with
    invFun := X.toCoinvariantsTensor hX
    left_inv := X.toCoinvariantsTensor_coinvariantTensorToModule hX
    right_inv := X.coinvariantTensorToModule_toCoinvariantsTensor hX }

/-- The forward linear map of the equivalence is the original action map. -/
@[simp] theorem coinvariantsTensorEquiv_toLinearMap (X : RightComodule R H M)
    (hX : X.IsHopfModule) :
    (X.coinvariantsTensorEquiv hX).toLinearMap = X.coinvariantTensorToModule := rfl

/-- The inverse linear map is the coaction followed by canonical projection. -/
@[simp] theorem coinvariantsTensorEquiv_symm_toLinearMap (X : RightComodule R H M)
    (hX : X.IsHopfModule) :
    (X.coinvariantsTensorEquiv hX).symm.toLinearMap = X.toCoinvariantsTensor hX := by
  apply LinearMap.ext
  intro m
  rfl

/-- Application of the decomposition equivalence is the original forward map. -/
theorem coinvariantsTensorEquiv_apply (X : RightComodule R H M)
    (hX : X.IsHopfModule) (z : (X.weightSpace (1 : H)) ⊗[R] H) :
    X.coinvariantsTensorEquiv hX z = X.coinvariantTensorToModule z := rfl

/-- On pure tensors the equivalence applies the given right action. -/
@[simp] theorem coinvariantsTensorEquiv_tmul (X : RightComodule R H M)
    (hX : X.IsHopfModule) (c : X.weightSpace (1 : H)) (h : H) :
    X.coinvariantsTensorEquiv hX (c ⊗ₜ[R] h) = MulOpposite.op h • (c : M) := by
  rw [coinvariantsTensorEquiv_apply, coinvariantTensorToModule_tmul]

/-- Application of the inverse equivalence is the direct map to the tensor
product of coinvariants. -/
@[simp] theorem coinvariantsTensorEquiv_symm_apply (X : RightComodule R H M)
    (hX : X.IsHopfModule) (m : M) :
    (X.coinvariantsTensorEquiv hX).symm m = X.toCoinvariantsTensor hX m := rfl

/-- Right multiplication on the second tensor factor intertwines the equivalence
with the original right action on the module. -/
theorem coinvariantsTensorEquiv_map_mulRight (X : RightComodule R H M)
    (hX : X.IsHopfModule) (h : H) (z : (X.weightSpace (1 : H)) ⊗[R] H) :
    X.coinvariantsTensorEquiv hX
        ((LinearMap.mulRight R h).lTensor (X.weightSpace (1 : H)) z) =
      MulOpposite.op h • X.coinvariantsTensorEquiv hX z := by
  simp only [coinvariantsTensorEquiv_apply, LinearMap.lTensor_def]
  exact X.coinvariantTensorToModule_map_mulRight h z

/-- The inverse equivalence intertwines the right action with right
multiplication on the second tensor factor, by genuine equivalence injectivity. -/
theorem coinvariantsTensorEquiv_symm_smul (X : RightComodule R H M)
    (hX : X.IsHopfModule) (h : H) (m : M) :
    (X.coinvariantsTensorEquiv hX).symm (MulOpposite.op h • m) =
      (LinearMap.mulRight R h).lTensor (X.weightSpace (1 : H))
        ((X.coinvariantsTensorEquiv hX).symm m) := by
  apply (X.coinvariantsTensorEquiv hX).injective
  rw [LinearEquiv.apply_symm_apply, X.coinvariantsTensorEquiv_map_mulRight hX,
    LinearEquiv.apply_symm_apply]

/-- The direct inverse map respects the right action, with multiplication only
on the Hopf-algebra tensor factor. -/
theorem toCoinvariantsTensor_smul (X : RightComodule R H M)
    (hX : X.IsHopfModule) (h : H) (m : M) :
    X.toCoinvariantsTensor hX (MulOpposite.op h • m) =
      (LinearMap.mulRight R h).lTensor (X.weightSpace (1 : H))
        (X.toCoinvariantsTensor hX m) := by
  simpa only [coinvariantsTensorEquiv_symm_apply] using
    X.coinvariantsTensorEquiv_symm_smul hX h m

end Coalgebra.RightComodule
