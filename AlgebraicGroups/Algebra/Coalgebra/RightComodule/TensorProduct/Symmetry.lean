/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.TensorProduct.Symmetry
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport

/-!
# Symmetry of external tensor products of right comodules

Carrier symmetry is colinear after interchanging the coefficient coalgebras.
The inverse morphism remains over the same exchanged coefficient coalgebra.
Naturality and transport express these changes without identifying differently
typed coefficient objects. The four-factor shuffle argument follows the tensor
coherence constructions in Mathlib and the external tensor associator.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uM uN

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable {M : Type uM} {N : Type uN} [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable (X : RightComodule R C M) (Y : RightComodule R D N)

/-- Carrier symmetry is colinear after symmetry of the coefficient coalgebra. -/
theorem externalTensor_comm_colinear :
    (Y.externalTensor X).coaction ∘ₗ (_root_.TensorProduct.comm R M N).toLinearMap =
      (_root_.TensorProduct.comm R M N).toLinearMap.rTensor (D ⊗[R] C) ∘ₗ
        ((X.externalTensor Y).mapCoalgebra
          (Coalgebra.TensorProduct.comm R C D).toCoalgHom).coaction := by
  let sMN := (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap
  let sNM := (_root_.TensorProduct.tensorTensorTensorComm R N D M C).toLinearMap
  have hshuffle :
      sNM ∘ₗ (_root_.TensorProduct.comm R (M ⊗[R] C) (N ⊗[R] D)).toLinearMap =
        (_root_.TensorProduct.comm R M N).toLinearMap.rTensor (D ⊗[R] C) ∘ₗ
          (Coalgebra.TensorProduct.comm R C D).toCoalgHom.toLinearMap.lTensor
            (M ⊗[R] N) ∘ₗ sMN := by
    apply _root_.TensorProduct.ext_fourfold'
    intro m c n d
    rfl
  apply _root_.TensorProduct.ext'
  intro m n
  change sNM (Y.coaction n ⊗ₜ[R] X.coaction m) =
    (_root_.TensorProduct.comm R M N).toLinearMap.rTensor (D ⊗[R] C)
      ((Coalgebra.TensorProduct.comm R C D).toCoalgHom.toLinearMap.lTensor (M ⊗[R] N)
        (sMN (X.coaction m ⊗ₜ[R] Y.coaction n)))
  exact LinearMap.congr_fun hshuffle (X.coaction m ⊗ₜ[R] Y.coaction n)

/-- Inverse carrier symmetry is colinear over the exchanged coalgebra. -/
theorem externalTensor_comm_symm_colinear :
    ((X.externalTensor Y).mapCoalgebra
        (Coalgebra.TensorProduct.comm R C D).toCoalgHom).coaction ∘ₗ
      (_root_.TensorProduct.comm R M N).symm.toLinearMap =
        (_root_.TensorProduct.comm R M N).symm.toLinearMap.rTensor (D ⊗[R] C) ∘ₗ
          (Y.externalTensor X).coaction :=
  RightComoduleHom.colinear_symm (_root_.TensorProduct.comm R M N)
    (externalTensor_comm_colinear X Y)

/-- Forward coefficient change followed by carrier transport exchanges the factors. -/
theorem externalTensor_comm_transport :
    ((X.externalTensor Y).mapCoalgebra
        (Coalgebra.TensorProduct.comm R C D).toCoalgHom).transport
      (_root_.TensorProduct.comm R M N) = Y.externalTensor X :=
  (transport_eq_iff_colinear
    ((X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
    (_root_.TensorProduct.comm R M N) (Y.externalTensor X)).2
      (externalTensor_comm_colinear X Y)

/-- Inverse carrier transport recovers the coefficient-reindexed tensor. -/
theorem externalTensor_comm_transport_symm :
    (Y.externalTensor X).transport (_root_.TensorProduct.comm R M N).symm =
      (X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom :=
  (transport_eq_iff_colinear (Y.externalTensor X) (_root_.TensorProduct.comm R M N).symm
    ((X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom)).2
      (externalTensor_comm_symm_colinear X Y)

/-- Forward carrier transport agrees with reverse coefficient change. -/
theorem externalTensor_comm_transport_reindex :
    (X.externalTensor Y).transport (_root_.TensorProduct.comm R M N) =
      (Y.externalTensor X).mapCoalgebra (Coalgebra.TensorProduct.comm R D C).toCoalgHom :=
  externalTensor_comm_transport_symm Y X

/-- Two coefficient symmetries recover the original specified comodule. -/
theorem externalTensor_comm_mapCoalgebra_involutive :
    ((X.externalTensor Y).mapCoalgebra
        (Coalgebra.TensorProduct.comm R C D).toCoalgHom).mapCoalgebra
      (Coalgebra.TensorProduct.comm R D C).toCoalgHom = X.externalTensor Y := by
  have hcancel :
      (Coalgebra.TensorProduct.comm R D C).toCoalgHom.comp
          (Coalgebra.TensorProduct.comm R C D).toCoalgHom =
        CoalgHom.id R (C ⊗[R] D) := by
    apply CoalgHom.coe_linearMap_injective
    refine _root_.TensorProduct.ext' fun (c : C) (d : D) => ?_
    rfl
  rw [mapCoalgebra_comp, hcancel, mapCoalgebra_id]

/-- Reversing coefficient change and carrier transport recovers the original object. -/
theorem externalTensor_comm_involutive :
    ((((X.externalTensor Y).mapCoalgebra
          (Coalgebra.TensorProduct.comm R C D).toCoalgHom).transport
        (_root_.TensorProduct.comm R M N)).mapCoalgebra
      (Coalgebra.TensorProduct.comm R D C).toCoalgHom).transport
        (_root_.TensorProduct.comm R N M) = X.externalTensor Y := by
  rw [externalTensor_comm_transport, externalTensor_comm_transport]

/-- Carrier symmetry as a morphism after forward coefficient change. -/
def externalTensorCommHom :
    RightComoduleHom
      ((X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
      (Y.externalTensor X) where
  toLinearMap := (_root_.TensorProduct.comm R M N).toLinearMap
  colinear := externalTensor_comm_colinear X Y

/-- Inverse carrier symmetry as a morphism over the exchanged coefficient coalgebra. -/
def externalTensorCommInvHom :
    RightComoduleHom (Y.externalTensor X)
      ((X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom) where
  toLinearMap := (_root_.TensorProduct.comm R M N).symm.toLinearMap
  colinear := externalTensor_comm_symm_colinear X Y

/-- The forward symmetry morphism has the tensor permutation as underlying map. -/
@[simp] theorem externalTensorCommHom_toLinearMap :
    (externalTensorCommHom X Y).toLinearMap = (_root_.TensorProduct.comm R M N).toLinearMap := rfl

/-- The inverse symmetry morphism has the inverse tensor permutation as underlying map. -/
@[simp] theorem externalTensorCommInvHom_toLinearMap :
    (externalTensorCommInvHom X Y).toLinearMap =
      (_root_.TensorProduct.comm R M N).symm.toLinearMap := rfl

/-- Evaluate the forward symmetry morphism at an arbitrary tensor. -/
@[simp] theorem externalTensorCommHom_apply (z : M ⊗[R] N) :
    externalTensorCommHom X Y z = (_root_.TensorProduct.comm R M N) z := rfl

/-- Evaluate the inverse symmetry morphism at an arbitrary tensor. -/
@[simp] theorem externalTensorCommInvHom_apply (z : N ⊗[R] M) :
    externalTensorCommInvHom X Y z = (_root_.TensorProduct.comm R M N).symm z := rfl

/-- The forward symmetry morphism interchanges pure factors. -/
theorem externalTensorCommHom_tmul (m : M) (n : N) :
    externalTensorCommHom X Y (m ⊗ₜ[R] n) = n ⊗ₜ[R] m := rfl

/-- The inverse symmetry morphism interchanges pure factors. -/
theorem externalTensorCommInvHom_tmul (m : M) (n : N) :
    externalTensorCommInvHom X Y (n ⊗ₜ[R] m) = m ⊗ₜ[R] n := rfl

/-- Inverse symmetry after forward symmetry is the identity morphism. -/
@[simp] theorem externalTensorCommInvHom_comp_externalTensorCommHom :
    (externalTensorCommInvHom X Y).comp (externalTensorCommHom X Y) =
      RightComoduleHom.id
        ((X.externalTensor Y).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom) := by
  apply RightComoduleHom.ext
  intro z
  simp only [RightComoduleHom.comp_apply, externalTensorCommHom_apply,
    externalTensorCommInvHom_apply, LinearEquiv.symm_apply_apply,
    RightComoduleHom.id_apply]

/-- Forward symmetry after inverse symmetry is the identity morphism. -/
@[simp] theorem externalTensorCommHom_comp_externalTensorCommInvHom :
    (externalTensorCommHom X Y).comp (externalTensorCommInvHom X Y) =
      RightComoduleHom.id (Y.externalTensor X) := by
  apply RightComoduleHom.ext
  intro z
  simp only [RightComoduleHom.comp_apply, externalTensorCommHom_apply,
    externalTensorCommInvHom_apply, LinearEquiv.apply_symm_apply,
    RightComoduleHom.id_apply]

universe uM' uN'

variable {M' : Type uM'} {N' : Type uN'}
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N'] [Module R N']
variable {X0 : RightComodule R C M} {X1 : RightComodule R C M'}
variable {Y0 : RightComodule R D N} {Y1 : RightComodule R D N'}

/-- Forward symmetry commutes with the external tensor of two comodule morphisms. -/
theorem externalTensorCommHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1) :
    (externalTensorCommHom X1 Y1).comp
        ((f.externalTensor g).mapCoalgebra (Coalgebra.TensorProduct.comm R C D).toCoalgHom) =
      (g.externalTensor f).comp (externalTensorCommHom X0 Y0) := by
  apply RightComoduleHom.toLinearMap_injective
  exact (_root_.TensorProduct.map_comp_comm_eq g.toLinearMap f.toLinearMap).symm

/-- Inverse symmetry commutes with the same two comodule morphisms. -/
theorem externalTensorCommInvHom_naturality
    (f : RightComoduleHom X0 X1) (g : RightComoduleHom Y0 Y1) :
    (externalTensorCommInvHom X1 Y1).comp (g.externalTensor f) =
      ((f.externalTensor g).mapCoalgebra
        (Coalgebra.TensorProduct.comm R C D).toCoalgHom).comp
          (externalTensorCommInvHom X0 Y0) := by
  apply RightComoduleHom.toLinearMap_injective
  exact (_root_.TensorProduct.map_comp_comm_eq f.toLinearMap g.toLinearMap).symm

end Coalgebra.RightComodule
