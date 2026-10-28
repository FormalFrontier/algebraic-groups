/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport

/-!
# Associativity of external tensor products of right comodules

The coefficient change is the coalgebra associator, and the carrier change
is the linear tensor associator. The resulting maps are inverse comodule
morphisms, natural in all three comodules. Both directions of coefficient
change and carrier transport are stated as equalities of specified objects.

The shuffle proof is an equality of linear maps on six tensor factors;
arbitrary coaction values are not required to be pure tensors. Tensor and
coalgebra associators are Mathlib's constructions by Kenny Lau, Mario
Carneiro, Amelia Livingston and Andrew Yang.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uE uM uN uP

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE}
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
variable (X : RightComodule R C M) (Y : RightComodule R D N)
variable (Z : RightComodule R E P)

/-- Reassociate both the coefficient coalgebra and the carrier. -/
theorem externalTensor_assoc_colinear :
    (X.externalTensor (Y.externalTensor Z)).coaction ∘ₗ
        (_root_.TensorProduct.assoc R M N P).toLinearMap =
      (_root_.TensorProduct.assoc R M N P).toLinearMap.rTensor (C ⊗[R] (D ⊗[R] E)) ∘ₗ
        (((X.externalTensor Y).externalTensor Z).mapCoalgebra
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).coaction := by
  let sMN := (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap
  let sNP := (_root_.TensorProduct.tensorTensorTensorComm R N D P E).toLinearMap
  let sL := (_root_.TensorProduct.tensorTensorTensorComm
    R (M ⊗[R] N) (C ⊗[R] D) P E).toLinearMap
  let sR := (_root_.TensorProduct.tensorTensorTensorComm
    R M C (N ⊗[R] P) (D ⊗[R] E)).toLinearMap
  have hshuffle :
      sR ∘ₗ _root_.TensorProduct.map LinearMap.id sNP ∘ₗ
          (_root_.TensorProduct.assoc R (M ⊗[R] C) (N ⊗[R] D)
            (P ⊗[R] E)).toLinearMap =
        (_root_.TensorProduct.assoc R M N P).toLinearMap.rTensor (C ⊗[R] (D ⊗[R] E)) ∘ₗ
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom.toLinearMap.lTensor
            ((M ⊗[R] N) ⊗[R] P) ∘ₗ
          sL ∘ₗ _root_.TensorProduct.map sMN LinearMap.id := by
    apply _root_.TensorProduct.ext
    apply _root_.TensorProduct.ext_fourfold'
    intro m c n d
    apply _root_.TensorProduct.ext'
    intro p e
    rfl
  apply _root_.TensorProduct.ext_threefold
  intro m n p
  change sR (X.coaction m ⊗ₜ[R] sNP (Y.coaction n ⊗ₜ[R] Z.coaction p)) =
    (_root_.TensorProduct.assoc R M N P).toLinearMap.rTensor (C ⊗[R] (D ⊗[R] E))
      ((Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom.toLinearMap.lTensor
        ((M ⊗[R] N) ⊗[R] P)
        (sL (sMN (X.coaction m ⊗ₜ[R] Y.coaction n) ⊗ₜ[R] Z.coaction p)))
  exact LinearMap.congr_fun hshuffle
    ((X.coaction m ⊗ₜ[R] Y.coaction n) ⊗ₜ[R] Z.coaction p)

/-- Inverse reassociation is colinear over the reassociated coalgebra. -/
theorem externalTensor_assoc_symm_colinear :
    (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).coaction ∘ₗ
        (_root_.TensorProduct.assoc R M N P).symm.toLinearMap =
      (_root_.TensorProduct.assoc R M N P).symm.toLinearMap.rTensor (C ⊗[R] (D ⊗[R] E)) ∘ₗ
        (X.externalTensor (Y.externalTensor Z)).coaction :=
  RightComoduleHom.colinear_symm (_root_.TensorProduct.assoc R M N P)
    (externalTensor_assoc_colinear X Y Z)

/-- Carrier transport after forward coefficient change is the right bracketing. -/
theorem externalTensor_transport_assoc :
    (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).transport
        (_root_.TensorProduct.assoc R M N P) = X.externalTensor (Y.externalTensor Z) :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensor_assoc_colinear X Y Z)

/-- The inverse carrier transport recovers the left bracketing after coefficient change. -/
theorem externalTensor_transport_assoc_symm :
    (X.externalTensor (Y.externalTensor Z)).transport (_root_.TensorProduct.assoc R M N P).symm =
      ((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensor_assoc_symm_colinear X Y Z)

/-- Reverse coefficient change agrees with forward carrier transport. -/
theorem externalTensor_mapCoalgebra_assoc_symm :
    (X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom =
      ((X.externalTensor Y).externalTensor Z).transport
        (_root_.TensorProduct.assoc R M N P) := by
  have hcancel : (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom.comp
      (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom =
      CoalgHom.id R ((C ⊗[R] D) ⊗[R] E) := by
    apply CoalgHom.ext
    intro c
    exact (Coalgebra.TensorProduct.assoc R R C D E).symm_apply_apply c
  have hcomm :
      (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom.toLinearMap.lTensor
          (M ⊗[R] (N ⊗[R] P)) ∘ₗ
          (_root_.TensorProduct.assoc R M N P).toLinearMap.rTensor (C ⊗[R] (D ⊗[R] E)) =
        (_root_.TensorProduct.assoc R M N P).toLinearMap.rTensor ((C ⊗[R] D) ⊗[R] E) ∘ₗ
          (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom.toLinearMap.lTensor
            ((M ⊗[R] N) ⊗[R] P) := by
    apply _root_.TensorProduct.ext'
    intro t c
    rfl
  calc
    (X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom =
        ((((X.externalTensor Y).externalTensor Z).mapCoalgebra
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).transport
          (_root_.TensorProduct.assoc R M N P)).mapCoalgebra
          (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom := by
      rw [externalTensor_transport_assoc]
    _ = ((((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom).transport
        (_root_.TensorProduct.assoc R M N P) := by
      apply RightComodule.ext
      apply LinearMap.ext
      intro t
      simp only [mapCoalgebra_coaction_apply, transport_coaction_apply]
      exact LinearMap.congr_fun hcomm
        ((((X.externalTensor Y).externalTensor Z).mapCoalgebra
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).coaction
          ((_root_.TensorProduct.assoc R M N P).symm t))
    _ = ((X.externalTensor Y).externalTensor Z).transport
        (_root_.TensorProduct.assoc R M N P) := by
      rw [mapCoalgebra_comp, hcancel, mapCoalgebra_id]

/-- Reversing both changes recovers the original left-bracketed object. -/
theorem externalTensor_mapCoalgebra_transport_assoc_symm :
    ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom).transport
        (_root_.TensorProduct.assoc R M N P).symm = (X.externalTensor Y).externalTensor Z := by
  rw [externalTensor_mapCoalgebra_assoc_symm, transport_symm]

/-- The carrier associator as a morphism after forward coefficient change. -/
def externalTensorAssocHom :
    RightComoduleHom (((X.externalTensor Y).externalTensor Z).mapCoalgebra
      (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom)
      (X.externalTensor (Y.externalTensor Z)) where
  toLinearMap := (_root_.TensorProduct.assoc R M N P).toLinearMap
  colinear := externalTensor_assoc_colinear X Y Z

/-- The inverse carrier associator as a morphism over the right-bracketed coalgebra. -/
def externalTensorAssocInvHom :
    RightComoduleHom (X.externalTensor (Y.externalTensor Z))
      (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom) where
  toLinearMap := (_root_.TensorProduct.assoc R M N P).symm.toLinearMap
  colinear := externalTensor_assoc_symm_colinear X Y Z

/-- The forward morphism has the stock carrier associator as its underlying map. -/
@[simp] theorem externalTensorAssocHom_toLinearMap :
    (externalTensorAssocHom X Y Z).toLinearMap =
      (_root_.TensorProduct.assoc R M N P).toLinearMap := rfl

/-- The inverse morphism has the stock inverse carrier associator as its underlying map. -/
@[simp] theorem externalTensorAssocInvHom_toLinearMap :
    (externalTensorAssocInvHom X Y Z).toLinearMap =
      (_root_.TensorProduct.assoc R M N P).symm.toLinearMap := rfl

/-- Evaluate the forward morphism at an arbitrary tensor. -/
@[simp] theorem externalTensorAssocHom_apply (t : (M ⊗[R] N) ⊗[R] P) :
    externalTensorAssocHom X Y Z t = (_root_.TensorProduct.assoc R M N P) t := rfl

/-- Evaluate the inverse morphism at an arbitrary tensor. -/
@[simp] theorem externalTensorAssocInvHom_apply (t : M ⊗[R] (N ⊗[R] P)) :
    externalTensorAssocInvHom X Y Z t = (_root_.TensorProduct.assoc R M N P).symm t := rfl

/-- Forward reassociation on three pure factors. -/
@[simp] theorem externalTensorAssocHom_tmul (m : M) (n : N) (p : P) :
    externalTensorAssocHom X Y Z ((m ⊗ₜ[R] n) ⊗ₜ[R] p) =
      m ⊗ₜ[R] (n ⊗ₜ[R] p) := rfl

/-- Inverse reassociation on three pure factors. -/
@[simp] theorem externalTensorAssocInvHom_tmul (m : M) (n : N) (p : P) :
    externalTensorAssocInvHom X Y Z (m ⊗ₜ[R] (n ⊗ₜ[R] p)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] p := rfl

/-- Inverse after forward reassociation is the identity. -/
@[simp] theorem externalTensorAssocInvHom_comp_externalTensorAssocHom :
    (externalTensorAssocInvHom X Y Z).comp (externalTensorAssocHom X Y Z) =
      RightComoduleHom.id (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom) := by
  apply RightComoduleHom.ext
  intro t
  change (_root_.TensorProduct.assoc R M N P).symm
    ((_root_.TensorProduct.assoc R M N P) t) = t
  exact LinearEquiv.symm_apply_apply _ _

/-- Forward after inverse reassociation is the identity. -/
@[simp] theorem externalTensorAssocHom_comp_externalTensorAssocInvHom :
    (externalTensorAssocHom X Y Z).comp (externalTensorAssocInvHom X Y Z) =
      RightComoduleHom.id (X.externalTensor (Y.externalTensor Z)) := by
  apply RightComoduleHom.ext
  intro t
  change _root_.TensorProduct.assoc R M N P
    ((_root_.TensorProduct.assoc R M N P).symm t) = t
  exact LinearEquiv.apply_symm_apply _ _

universe uM' uN' uP'

variable {M' : Type uM'} {N' : Type uN'} {P' : Type uP'}
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N'] [Module R N']
variable [AddCommMonoid P'] [Module R P']
variable {X0 : RightComodule R C M} {X1 : RightComodule R C M'}
variable {Y0 : RightComodule R D N} {Y1 : RightComodule R D N'}
variable {Z0 : RightComodule R E P} {Z1 : RightComodule R E P'}

/-- Reassociation commutes with external tensor products of three morphisms. -/
theorem externalTensorAssocHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1)
    (h : RightComoduleHom Z0 Z1) :
    (f.externalTensor (g.externalTensor h)).comp
        (externalTensorAssocHom X0 Y0 Z0) =
      (externalTensorAssocHom X1 Y1 Z1).comp
        (((f.externalTensor g).externalTensor h).mapCoalgebra
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom) := by
  apply RightComoduleHom.toLinearMap_injective
  exact _root_.TensorProduct.map_map_comp_assoc_eq f.toLinearMap g.toLinearMap h.toLinearMap

/-- Inverse reassociation commutes with the same three morphisms. -/
theorem externalTensorAssocInvHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1)
    (h : RightComoduleHom Z0 Z1) :
    (((f.externalTensor g).externalTensor h).mapCoalgebra
        (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom).comp
        (externalTensorAssocInvHom X0 Y0 Z0) =
      (externalTensorAssocInvHom X1 Y1 Z1).comp
        (f.externalTensor (g.externalTensor h)) := by
  apply RightComoduleHom.toLinearMap_injective
  exact _root_.TensorProduct.map_map_comp_assoc_symm_eq f.toLinearMap g.toLinearMap h.toLinearMap

end Coalgebra.RightComodule
