/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport

/-!
# Unit laws for external tensor products of right comodules

The unit is the regular comodule of the canonical scalar coalgebra
`CommSemiring.toCoalgebra R`. Coefficients are changed along Mathlib's coalgebra
unitors before using its carrier unitors. No coalgebra structure on `R` is a
parameter, and no algebra structure on the coefficient coalgebra is required.
The inverse maps, transport equalities and naturality use the existing specified
comodule and morphism constructions.
-/

@[expose] public section

universe uR uC uD uM uN

open scoped TensorProduct

noncomputable section

namespace Coalgebra.RightComodule

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} [AddCommMonoid C] [Module R C]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

private theorem leftUnit_collapse (a : R) (t : M ⊗[R] C) :
    (_root_.TensorProduct.lid R M).toLinearMap.rTensor C
        ((_root_.TensorProduct.lid R C).toLinearMap.lTensor (R ⊗[R] M)
          (_root_.TensorProduct.tensorTensorTensorComm R R R M C
            (((1 : R) ⊗ₜ[R] a) ⊗ₜ[R] t))) = a • t := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul m c => simp
  | add x y hx hy => simp [_root_.TensorProduct.tmul_add, hx, hy, smul_add]

private theorem rightUnit_collapse (a : R) (t : M ⊗[R] C) :
    (_root_.TensorProduct.rid R M).toLinearMap.rTensor C
        ((_root_.TensorProduct.rid R C).toLinearMap.lTensor (M ⊗[R] R)
          (_root_.TensorProduct.tensorTensorTensorComm R M C R R
            (t ⊗ₜ[R] ((1 : R) ⊗ₜ[R] a)))) = a • t := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul m c => simp
  | add x y hx hy => simp [_root_.TensorProduct.add_tmul, hx, hy, smul_add]

variable [Coalgebra R C]

/-- Full colinearity of the left carrier unitor after forward coefficient change. -/
theorem externalTensorLeftUnit_colinear (X : RightComodule R C M) :
    X.coaction ∘ₗ (_root_.TensorProduct.lid R M).toLinearMap =
      (_root_.TensorProduct.lid R M).toLinearMap.rTensor C ∘ₗ
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom).coaction := by
  refine _root_.TensorProduct.ext' fun (a : R) (m : M) => ?_
  change X.coaction (a • m) =
    (_root_.TensorProduct.lid R M).toLinearMap.rTensor C
      ((_root_.TensorProduct.lid R C).toLinearMap.lTensor (R ⊗[R] M)
        (_root_.TensorProduct.tensorTensorTensorComm R R R M C
          (((1 : R) ⊗ₜ[R] a) ⊗ₜ[R] X.coaction m)))
  rw [map_smul]
  exact (leftUnit_collapse a (X.coaction m)).symm

/-- Full colinearity of the right carrier unitor after forward coefficient change. -/
theorem externalTensorRightUnit_colinear (X : RightComodule R C M) :
    X.coaction ∘ₗ (_root_.TensorProduct.rid R M).toLinearMap =
      (_root_.TensorProduct.rid R M).toLinearMap.rTensor C ∘ₗ
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom).coaction := by
  refine _root_.TensorProduct.ext' fun (m : M) (a : R) => ?_
  change X.coaction (a • m) =
    (_root_.TensorProduct.rid R M).toLinearMap.rTensor C
      ((_root_.TensorProduct.rid R C).toLinearMap.lTensor (M ⊗[R] R)
        (_root_.TensorProduct.tensorTensorTensorComm R M C R R
          (X.coaction m ⊗ₜ[R] ((1 : R) ⊗ₜ[R] a))))
  rw [map_smul]
  exact (rightUnit_collapse a (X.coaction m)).symm

/-- The left external tensor unitor, with canonical scalar regular unit. -/
def externalTensorLeftUnitor (X : RightComodule R C M) :
    RightComoduleHom (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom) X where
  toLinearMap := (_root_.TensorProduct.lid R M).toLinearMap
  colinear := externalTensorLeftUnit_colinear X

/-- The inverse left unitor uses the inverse carrier map, not inverse coefficient change. -/
def externalTensorLeftUnitorInv (X : RightComodule R C M) :
    RightComoduleHom X (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom) where
  toLinearMap := (_root_.TensorProduct.lid R M).symm.toLinearMap
  colinear := RightComoduleHom.colinear_symm (_root_.TensorProduct.lid R M)
    (externalTensorLeftUnit_colinear X)

/-- The right external tensor unitor, with canonical scalar regular unit. -/
def externalTensorRightUnitor (X : RightComodule R C M) :
    RightComoduleHom ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom) X where
  toLinearMap := (_root_.TensorProduct.rid R M).toLinearMap
  colinear := externalTensorRightUnit_colinear X

/-- The inverse right unitor, over the original coefficient coalgebra. -/
def externalTensorRightUnitorInv (X : RightComodule R C M) :
    RightComoduleHom X ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom) where
  toLinearMap := (_root_.TensorProduct.rid R M).symm.toLinearMap
  colinear := RightComoduleHom.colinear_symm (_root_.TensorProduct.rid R M)
    (externalTensorRightUnit_colinear X)

@[simp] theorem externalTensorLeftUnitor_toLinearMap (X : RightComodule R C M) :
    (externalTensorLeftUnitor X).toLinearMap =
      (_root_.TensorProduct.lid R M).toLinearMap := rfl

@[simp] theorem externalTensorLeftUnitorInv_toLinearMap (X : RightComodule R C M) :
    (externalTensorLeftUnitorInv X).toLinearMap =
      (_root_.TensorProduct.lid R M).symm.toLinearMap := rfl

@[simp] theorem externalTensorRightUnitor_toLinearMap (X : RightComodule R C M) :
    (externalTensorRightUnitor X).toLinearMap =
      (_root_.TensorProduct.rid R M).toLinearMap := rfl

@[simp] theorem externalTensorRightUnitorInv_toLinearMap (X : RightComodule R C M) :
    (externalTensorRightUnitorInv X).toLinearMap =
      (_root_.TensorProduct.rid R M).symm.toLinearMap := rfl

@[simp] theorem externalTensorLeftUnitor_apply (X : RightComodule R C M)
    (t : R ⊗[R] M) :
    externalTensorLeftUnitor X t = _root_.TensorProduct.lid R M t := rfl

@[simp] theorem externalTensorRightUnitor_apply (X : RightComodule R C M)
    (t : M ⊗[R] R) :
    externalTensorRightUnitor X t = _root_.TensorProduct.rid R M t := rfl

@[simp] theorem externalTensorLeftUnitor_tmul (X : RightComodule R C M)
    (a : R) (m : M) : externalTensorLeftUnitor X (a ⊗ₜ[R] m) = a • m := rfl

@[simp] theorem externalTensorRightUnitor_tmul (X : RightComodule R C M)
    (m : M) (a : R) : externalTensorRightUnitor X (m ⊗ₜ[R] a) = a • m := rfl

@[simp] theorem externalTensorLeftUnitorInv_apply (X : RightComodule R C M) (m : M) :
    externalTensorLeftUnitorInv X m = (1 : R) ⊗ₜ[R] m := rfl

@[simp] theorem externalTensorRightUnitorInv_apply (X : RightComodule R C M) (m : M) :
    externalTensorRightUnitorInv X m = m ⊗ₜ[R] (1 : R) := rfl

@[simp] theorem externalTensorLeftUnitorInv_comp (X : RightComodule R C M) :
    (externalTensorLeftUnitorInv X).comp (externalTensorLeftUnitor X) =
      RightComoduleHom.id (((regular R R).externalTensor X).mapCoalgebra
        (Coalgebra.TensorProduct.lid R C).toCoalgHom) := by
  apply RightComoduleHom.ext
  intro t
  change (_root_.TensorProduct.lid R M).symm (_root_.TensorProduct.lid R M t) = t
  exact LinearEquiv.symm_apply_apply _ _

@[simp] theorem externalTensorLeftUnitor_comp_inv (X : RightComodule R C M) :
    (externalTensorLeftUnitor X).comp (externalTensorLeftUnitorInv X) =
      RightComoduleHom.id X := by
  apply RightComoduleHom.ext
  intro m
  change _root_.TensorProduct.lid R M ((_root_.TensorProduct.lid R M).symm m) = m
  exact LinearEquiv.apply_symm_apply _ _

@[simp] theorem externalTensorRightUnitorInv_comp (X : RightComodule R C M) :
    (externalTensorRightUnitorInv X).comp (externalTensorRightUnitor X) =
      RightComoduleHom.id ((X.externalTensor (regular R R)).mapCoalgebra
        (Coalgebra.TensorProduct.rid R R C).toCoalgHom) := by
  apply RightComoduleHom.ext
  intro t
  change (_root_.TensorProduct.rid R M).symm (_root_.TensorProduct.rid R M t) = t
  exact LinearEquiv.symm_apply_apply _ _

@[simp] theorem externalTensorRightUnitor_comp_inv (X : RightComodule R C M) :
    (externalTensorRightUnitor X).comp (externalTensorRightUnitorInv X) =
      RightComoduleHom.id X := by
  apply RightComoduleHom.ext
  intro m
  change _root_.TensorProduct.rid R M ((_root_.TensorProduct.rid R M).symm m) = m
  exact LinearEquiv.apply_symm_apply _ _

/-- First change the coefficient coalgebra, then transport to the target carrier. -/
theorem externalTensorLeftUnit_transport (X : RightComodule R C M) :
    (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom).transport
        (_root_.TensorProduct.lid R M) = X :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensorLeftUnitor X).colinear

theorem externalTensorRightUnit_transport (X : RightComodule R C M) :
    ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom).transport
        (_root_.TensorProduct.rid R M) = X :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensorRightUnitor X).colinear

/-- Reverse carrier transport still has coefficient coalgebra `C`. -/
theorem externalTensorLeftUnit_transport_symm (X : RightComodule R C M) :
    X.transport (_root_.TensorProduct.lid R M).symm =
      ((regular R R).externalTensor X).mapCoalgebra
        (Coalgebra.TensorProduct.lid R C).toCoalgHom :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensorLeftUnitorInv X).colinear

theorem externalTensorRightUnit_transport_symm (X : RightComodule R C M) :
    X.transport (_root_.TensorProduct.rid R M).symm =
      (X.externalTensor (regular R R)).mapCoalgebra
        (Coalgebra.TensorProduct.rid R R C).toCoalgHom :=
  (transport_eq_iff_colinear _ _ _).2 (externalTensorRightUnitorInv X).colinear

/-- Reversing both arrows recovers the external tensor before coefficient change. -/
theorem externalTensorLeftUnit_mapCoalgebra_symm_transport (X : RightComodule R C M) :
    (X.mapCoalgebra (Coalgebra.TensorProduct.lid R C).symm.toCoalgHom).transport
      (_root_.TensorProduct.lid R M).symm = (regular R R).externalTensor X := by
  apply (transport_eq_iff_colinear _ _ _).2
  ext m
  change _root_.TensorProduct.tensorTensorTensorComm R R R M C
      (((1 : R) ⊗ₜ[R] (1 : R)) ⊗ₜ[R] X.coaction m) =
    (_root_.TensorProduct.lid R M).symm.toLinearMap.rTensor (R ⊗[R] C)
      ((_root_.TensorProduct.lid R C).symm.toLinearMap.lTensor M (X.coaction m))
  induction X.coaction m using _root_.TensorProduct.inductionOn with
  | tmul n c => simp
  | add x y hx hy => simp [_root_.TensorProduct.tmul_add, hx, hy]

theorem externalTensorRightUnit_mapCoalgebra_symm_transport (X : RightComodule R C M) :
    (X.mapCoalgebra (Coalgebra.TensorProduct.rid R R C).symm.toCoalgHom).transport
      (_root_.TensorProduct.rid R M).symm = X.externalTensor (regular R R) := by
  apply (transport_eq_iff_colinear _ _ _).2
  ext m
  change _root_.TensorProduct.tensorTensorTensorComm R M C R R
      (X.coaction m ⊗ₜ[R] ((1 : R) ⊗ₜ[R] (1 : R))) =
    (_root_.TensorProduct.rid R M).symm.toLinearMap.rTensor (C ⊗[R] R)
      ((_root_.TensorProduct.rid R C).symm.toLinearMap.lTensor M (X.coaction m))
  induction X.coaction m using _root_.TensorProduct.inductionOn with
  | tmul n c => simp
  | add x y hx hy => simp [_root_.TensorProduct.add_tmul, hx, hy]

/-- Read back the coefficient change without assuming a pure coaction value. -/
theorem externalTensorLeftUnit_coaction_apply (X : RightComodule R C M)
    (t : R ⊗[R] M) :
    (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom).coaction t =
      (Coalgebra.TensorProduct.lid R C).toCoalgHom.toLinearMap.lTensor (R ⊗[R] M)
        (((regular R R).externalTensor X).coaction t) := rfl

theorem externalTensorRightUnit_coaction_apply (X : RightComodule R C M)
    (t : M ⊗[R] R) :
    ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom).coaction t =
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom.toLinearMap.lTensor (M ⊗[R] R)
        ((X.externalTensor (regular R R)).coaction t) := rfl

/-- The adjusted coaction is the conjugate of the original one on every tensor. -/
theorem externalTensorLeftUnit_coaction_eq (X : RightComodule R C M)
    (t : R ⊗[R] M) :
    (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom).coaction t =
      (_root_.TensorProduct.lid R M).symm.toLinearMap.rTensor C
        (X.coaction (_root_.TensorProduct.lid R M t)) := by
  rw [← externalTensorLeftUnit_transport_symm X]
  simpa only [LinearEquiv.symm_symm] using
    transport_coaction_apply X (_root_.TensorProduct.lid R M).symm t

theorem externalTensorRightUnit_coaction_eq (X : RightComodule R C M)
    (t : M ⊗[R] R) :
    ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom).coaction t =
      (_root_.TensorProduct.rid R M).symm.toLinearMap.rTensor C
        (X.coaction (_root_.TensorProduct.rid R M t)) := by
  rw [← externalTensorRightUnit_transport_symm X]
  simpa only [LinearEquiv.symm_symm] using
    transport_coaction_apply X (_root_.TensorProduct.rid R M).symm t

theorem externalTensorLeftUnit_coaction_tmul (X : RightComodule R C M)
    (a : R) (m : M) :
    (((regular R R).externalTensor X).mapCoalgebra
      (Coalgebra.TensorProduct.lid R C).toCoalgHom).coaction (a ⊗ₜ[R] m) =
      (_root_.TensorProduct.lid R M).symm.toLinearMap.rTensor C
        (X.coaction (a • m)) :=
  externalTensorLeftUnit_coaction_eq X (a ⊗ₜ[R] m)

theorem externalTensorRightUnit_coaction_tmul (X : RightComodule R C M)
    (m : M) (a : R) :
    ((X.externalTensor (regular R R)).mapCoalgebra
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom).coaction (m ⊗ₜ[R] a) =
      (_root_.TensorProduct.rid R M).symm.toLinearMap.rTensor C
        (X.coaction (a • m)) :=
  externalTensorRightUnit_coaction_eq X (m ⊗ₜ[R] a)

variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

/-- The left unitor is natural in a specified comodule morphism. -/
theorem externalTensorLeftUnitor_naturality (f : RightComoduleHom X Y) :
    (externalTensorLeftUnitor Y).comp
        (((RightComoduleHom.id (regular R R)).externalTensor f).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) =
      f.comp (externalTensorLeftUnitor X) := by
  apply RightComoduleHom.toLinearMap_injective
  refine _root_.TensorProduct.ext' fun (a : R) (m : M) => ?_
  change a • f m = f (a • m)
  exact (map_smul f.toLinearMap a m).symm

/-- Naturality of the inverse left unitor. -/
theorem externalTensorLeftUnitorInv_naturality (f : RightComoduleHom X Y) :
    (externalTensorLeftUnitorInv Y).comp f =
      (((RightComoduleHom.id (regular R R)).externalTensor f).mapCoalgebra
        (Coalgebra.TensorProduct.lid R C).toCoalgHom).comp
          (externalTensorLeftUnitorInv X) := by
  apply RightComoduleHom.toLinearMap_injective
  ext m
  rfl

/-- The right unitor is natural in a specified comodule morphism. -/
theorem externalTensorRightUnitor_naturality (f : RightComoduleHom X Y) :
    (externalTensorRightUnitor Y).comp
        ((f.externalTensor (RightComoduleHom.id (regular R R))).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) =
      f.comp (externalTensorRightUnitor X) := by
  apply RightComoduleHom.toLinearMap_injective
  refine _root_.TensorProduct.ext' fun (m : M) (a : R) => ?_
  change a • f m = f (a • m)
  exact (map_smul f.toLinearMap a m).symm

/-- Naturality of the inverse right unitor. -/
theorem externalTensorRightUnitorInv_naturality (f : RightComoduleHom X Y) :
    (externalTensorRightUnitorInv Y).comp f =
      ((f.externalTensor (RightComoduleHom.id (regular R R))).mapCoalgebra
        (Coalgebra.TensorProduct.rid R R C).toCoalgHom).comp
          (externalTensorRightUnitorInv X) := by
  apply RightComoduleHom.toLinearMap_injective
  ext m
  rfl

variable {D : Type uD} [AddCommMonoid D] [Module R D] [Coalgebra R D]

/-- The coefficient left unitors are natural coalgebra morphisms. -/
theorem externalTensorLeftUnit_coefficient_naturality (h : C →ₗc[R] D) :
    (Coalgebra.TensorProduct.lid R D).toCoalgHom.comp
        (Coalgebra.TensorProduct.map (CoalgHom.id R R) h) =
      h.comp (Coalgebra.TensorProduct.lid R C).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  refine _root_.TensorProduct.ext' fun (a : R) (c : C) => ?_
  change a • h c = h (a • c)
  exact (map_smul h.toLinearMap a c).symm

/-- The coefficient right unitors are natural coalgebra morphisms. -/
theorem externalTensorRightUnit_coefficient_naturality (h : C →ₗc[R] D) :
    (Coalgebra.TensorProduct.rid R R D).toCoalgHom.comp
        (Coalgebra.TensorProduct.map h (CoalgHom.id R R)) =
      h.comp (Coalgebra.TensorProduct.rid R R C).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  refine _root_.TensorProduct.ext' fun (c : C) (a : R) => ?_
  change a • h c = h (a • c)
  exact (map_smul h.toLinearMap a c).symm

end Coalgebra.RightComodule
