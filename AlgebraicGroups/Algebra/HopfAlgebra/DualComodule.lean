/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.DualTensor
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual

/-!
# The antipode-induced right comodule on the linear dual

For a finite projective Hopf algebra over a commutative semiring, the original
linear dual is a right comodule with coaction `HopfAlgebra.antipodeDualTensor`.
The constructor is named rather than installed as an instance. Its projection
and law lemmas allow use without unfolding the constructor.

The construction reuses the dual of the regular right comodule. The public
characteristic formula and Mathlib's tensor/Hom correspondence identify its
coaction with the antipode tensor, so its existing comodule laws apply.

## Implementation notes

All modules and the coalgebra are inherited from the given Hopf algebra. No
algebra action on the dual or Hopf-module compatibility is asserted here.
-/

@[expose] public section

open scoped TensorProduct

universe uR uH

namespace HopfAlgebra

variable (R : Type uR) (H : Type uH)
  [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [Module.Finite R H] [Module.Projective R H]

private theorem regular_dual_coaction :
    (Coalgebra.RightComodule.dual (Coalgebra.RightComodule.regular R H)).coaction =
      antipodeDualTensor R H := by
  ext φ
  apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
  ext x
  rw [Coalgebra.RightComodule.dual_coaction,
    Coalgebra.RightComodule.dualCoaction_characteristic,
    Coalgebra.RightComodule.regular_coaction, dualTensorHom_antipodeDualTensor_apply]
  have h (t : H ⊗[R] H) :
      HopfAlgebra.antipode R (Coalgebra.RightComodule.dualContraction φ t) =
        TensorProduct.lid R H (TensorProduct.map φ (HopfAlgebra.antipode R) t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add t u ht hu => simp only [map_add, ht, hu]
  exact h (Coalgebra.comul (R := R) x)

/-- The antipode tensor satisfies the right counit equation on the original dual. -/
theorem antipodeDualTensor_counit :
    (Coalgebra.counit (R := R) (A := H)).lTensor (Module.Dual R H) ∘ₗ
        antipodeDualTensor R H =
      (TensorProduct.rid R (Module.Dual R H)).symm.toLinearMap := by
  simpa only [regular_dual_coaction R H] using
    (Coalgebra.RightComodule.dual (Coalgebra.RightComodule.regular R H)).counit_comp

/-- The antipode tensor satisfies the right coassociativity equation on the
original dual, in the associator convention for `Coalgebra.RightComodule`. -/
theorem antipodeDualTensor_coassoc :
    (TensorProduct.assoc R (Module.Dual R H) H H).toLinearMap ∘ₗ
        (antipodeDualTensor R H).rTensor H ∘ₗ antipodeDualTensor R H =
      (Coalgebra.comul (R := R) (A := H)).lTensor (Module.Dual R H) ∘ₗ
        antipodeDualTensor R H := by
  simpa only [regular_dual_coaction R H] using
    (Coalgebra.RightComodule.dual (Coalgebra.RightComodule.regular R H)).coassoc

/-- The canonical right comodule on the original linear dual of a finite
projective Hopf algebra, with coaction given by the antipode tensor. -/
noncomputable def antipodeDualRightComodule :
    Coalgebra.RightComodule R H (Module.Dual R H) where
  coaction := antipodeDualTensor R H
  coassoc := antipodeDualTensor_coassoc R H
  counit_comp := antipodeDualTensor_counit R H

/-- The canonical dual comodule has precisely the antipode tensor as its coaction. -/
@[simp]
theorem antipodeDualRightComodule_coaction :
    (antipodeDualRightComodule R H).coaction = antipodeDualTensor R H := rfl

end HopfAlgebra
