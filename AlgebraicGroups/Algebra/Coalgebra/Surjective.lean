/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Equiv

/-!
# Coalgebra laws along surjective morphisms

The three coalgebra laws descend along a surjective linear map preserving
comultiplication and counit. The target needs only `CoalgebraStruct`, and the
map may belong to any `CoalgHomClass`. Cocommutativity descends separately
between full coalgebras. For a linear equivalence, the inverse of
`LinearEquiv.toCoalgEquiv` supplies the preserving surjection, and descent agrees
with `LinearEquiv.coalgebra` without any additional morphism hypothesis.
-/

@[expose] public section

open TensorProduct

universe uR uC uD uF

namespace Coalgebra

variable {R : Type uR} {C : Type uC} {D : Type uD} {F : Type uF}
  [CommSemiring R] [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]

section CoalgebraStruct

variable [Coalgebra R C] [CoalgebraStruct R D] [FunLike F C D]
  [CoalgHomClass F R C D]

/-- Coassociativity descends along a surjective coalgebra morphism. -/
theorem coassoc_of_surjective (f : F) (hf : Function.Surjective f) :
    TensorProduct.assoc R D D D ∘ₗ (comul (R := R) (A := D)).rTensor D ∘ₗ comul =
      comul.lTensor D ∘ₗ comul := by
  let g : C →ₗ[R] D := f
  have hcomul : comul (R := R) (A := D) ∘ₗ g =
      TensorProduct.map g g ∘ₗ comul :=
    (CoalgHomClass.map_comp_comul f).symm
  have hr : (comul (R := R) (A := D)).rTensor D ∘ₗ TensorProduct.map g g =
      TensorProduct.map (TensorProduct.map g g) g ∘ₗ
        (comul (R := R) (A := C)).rTensor C := by
    simp only [LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id, hcomul]
  have hl : (comul (R := R) (A := D)).lTensor D ∘ₗ TensorProduct.map g g =
      TensorProduct.map g (TensorProduct.map g g) ∘ₗ
        (comul (R := R) (A := C)).lTensor C := by
    simp only [LinearMap.lTensor_def, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id, hcomul]
  apply (LinearMap.cancel_right (g := g) hf).mp
  calc
    _ = TensorProduct.assoc R D D D ∘ₗ
        ((comul (R := R) (A := D)).rTensor D ∘ₗ TensorProduct.map g g) ∘ₗ
        comul (R := R) (A := C) := by
      simp only [LinearMap.comp_assoc, hcomul]
    _ = TensorProduct.assoc R D D D ∘ₗ
        (TensorProduct.map (TensorProduct.map g g) g ∘ₗ
          (comul (R := R) (A := C)).rTensor C) ∘ₗ comul := by
      rw [hr]
    _ = TensorProduct.map g (TensorProduct.map g g) ∘ₗ
        (TensorProduct.assoc R C C C ∘ₗ
          (comul (R := R) (A := C)).rTensor C ∘ₗ comul) := by
      simp only [← LinearMap.comp_assoc, ← TensorProduct.map_map_comp_assoc_eq]
    _ = TensorProduct.map g (TensorProduct.map g g) ∘ₗ
        ((comul (R := R) (A := C)).lTensor C ∘ₗ comul) := by
      rw [coassoc]
    _ = ((comul (R := R) (A := D)).lTensor D ∘ₗ TensorProduct.map g g) ∘ₗ
        comul := by
      simp only [← LinearMap.comp_assoc, hl]
    _ = _ := by
      simp only [LinearMap.comp_assoc, hcomul]

/-- Left counitality descends along a surjective coalgebra morphism. -/
theorem rTensor_counit_comp_comul_of_surjective (f : F) (hf : Function.Surjective f) :
    (counit (R := R) (A := D)).rTensor D ∘ₗ comul = TensorProduct.mk R _ _ 1 := by
  apply (LinearMap.cancel_right (g := (f : C →ₗ[R] D)) hf).mp
  calc
    ((counit (R := R) (A := D)).rTensor D ∘ₗ comul) ∘ₗ (f : C →ₗ[R] D) =
        TensorProduct.map (counit (R := R) (A := C)) (f : C →ₗ[R] D) ∘ₗ comul := by
      rw [LinearMap.comp_assoc, ← CoalgHomClass.map_comp_comul f,
        ← LinearMap.comp_assoc, LinearMap.rTensor_comp_map, CoalgHomClass.counit_comp]
    _ = (f : C →ₗ[R] D).lTensor R ∘ₗ
        ((counit (R := R) (A := C)).rTensor C ∘ₗ comul) := by
      rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor]
    _ = TensorProduct.mk R _ _ 1 ∘ₗ (f : C →ₗ[R] D) := by
      rw [rTensor_counit_comp_comul, LinearMap.lTensor_comp_mk]

/-- Right counitality descends along a surjective coalgebra morphism. -/
theorem lTensor_counit_comp_comul_of_surjective (f : F) (hf : Function.Surjective f) :
    (counit (R := R) (A := D)).lTensor D ∘ₗ comul = (TensorProduct.mk R _ _).flip 1 := by
  apply (LinearMap.cancel_right (g := (f : C →ₗ[R] D)) hf).mp
  calc
    ((counit (R := R) (A := D)).lTensor D ∘ₗ comul) ∘ₗ (f : C →ₗ[R] D) =
        TensorProduct.map (f : C →ₗ[R] D) (counit (R := R) (A := C)) ∘ₗ comul := by
      rw [LinearMap.comp_assoc, ← CoalgHomClass.map_comp_comul f,
        ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map, CoalgHomClass.counit_comp]
    _ = (f : C →ₗ[R] D).rTensor R ∘ₗ
        ((counit (R := R) (A := C)).lTensor C ∘ₗ comul) := by
      rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor]
    _ = (TensorProduct.mk R _ _).flip 1 ∘ₗ (f : C →ₗ[R] D) := by
      rw [lTensor_counit_comp_comul, LinearMap.rTensor_comp_flip_mk]

end CoalgebraStruct

section Coalgebra

variable [Coalgebra R C] [Coalgebra R D] [FunLike F C D]
  [CoalgHomClass F R C D] [IsCocomm R C]

/-- Cocommutativity descends along a surjective morphism of coalgebras. -/
theorem isCocomm_of_surjective (f : F) (hf : Function.Surjective f) : IsCocomm R D := by
  let g : C →ₗ[R] D := f
  have hcomul : comul (R := R) (A := D) ∘ₗ g =
      TensorProduct.map g g ∘ₗ comul :=
    (CoalgHomClass.map_comp_comul f).symm
  constructor
  apply (LinearMap.cancel_right (g := g) hf).mp
  calc
    _ = ((TensorProduct.comm R D D).toLinearMap ∘ₗ TensorProduct.map g g) ∘ₗ
        comul (R := R) (A := C) := by
      simp only [LinearMap.comp_assoc, hcomul]
    _ = TensorProduct.map g g ∘ₗ
        ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul) := by
      simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp_comm_eq]
    _ = TensorProduct.map g g ∘ₗ comul := by
      rw [comm_comp_comul]
    _ = comul ∘ₗ g := hcomul.symm

end Coalgebra

section OfSurjective

variable [c : Coalgebra R C] [d : CoalgebraStruct R D] [FunLike F C D]
  [CoalgHomClass F R C D]

/-- Equip the fixed target structure with the coalgebra laws descended along a surjection. -/
@[instance_reducible]
def ofSurjective (f : F) (hf : Function.Surjective f) : Coalgebra R D where
  toCoalgebraStruct := d
  coassoc := coassoc_of_surjective f hf
  rTensor_counit_comp_comul := rTensor_counit_comp_comul_of_surjective f hf
  lTensor_counit_comp_comul := lTensor_counit_comp_comul_of_surjective f hf

/-- Descent retains exactly the given target structure. -/
@[simp]
theorem ofSurjective_toCoalgebraStruct (f : F) (hf : Function.Surjective f) :
    (ofSurjective f hf).toCoalgebraStruct = d := rfl

/-- Descent does not change the target comultiplication. -/
@[simp]
theorem ofSurjective_comul (f : F) (hf : Function.Surjective f) :
    @CoalgebraStruct.comul R D _ _ _ (ofSurjective f hf).toCoalgebraStruct =
      comul (R := R) (A := D) := rfl

/-- Descent does not change the target counit. -/
@[simp]
theorem ofSurjective_counit (f : F) (hf : Function.Surjective f) :
    @CoalgebraStruct.counit R D _ _ _ (ofSurjective f hf).toCoalgebraStruct =
      counit (R := R) (A := D) := rfl

/-- The descended coalgebra is cocommutative when the source is cocommutative. -/
theorem ofSurjective_isCocomm [IsCocomm R C] (f : F) (hf : Function.Surjective f) :
    @IsCocomm R D _ _ _ (ofSurjective f hf) := by
  let : Coalgebra R D := ofSurjective f hf
  exact isCocomm_of_surjective f hf

end OfSurjective

section OfSurjectiveEq

variable [Coalgebra R C] [d : Coalgebra R D] [FunLike F C D]
  [CoalgHomClass F R C D]

/-- Descent agrees with any full target coalgebra whose parent is the fixed target structure. -/
@[simp]
theorem ofSurjective_eq (f : F) (hf : Function.Surjective f) :
    ofSurjective f hf = (inferInstance : Coalgebra R D) := rfl

end OfSurjectiveEq

/-- Descent along the inverse equivalence of pulled-back data agrees with
`LinearEquiv.coalgebra`. Only the given coalgebra and linear equivalence are required;
the target data are exactly `LinearEquiv.coalgebraStruct`. -/
@[simp]
theorem ofSurjective_coalgebra [c : Coalgebra R C] (e : D ≃ₗ[R] C) :
    @ofSurjective R C D
      (@CoalgHom R C D _ _ _ _ _ c.toCoalgebraStruct (e.coalgebraStruct R))
      _ _ _ _ _ c (e.coalgebraStruct R) _ _
      (↑(@CoalgEquiv.symm R D C _ _ _ _ _ (e.coalgebraStruct R) c.toCoalgebraStruct
          (@LinearEquiv.toCoalgEquiv R D C _ _ _ _ _ c.toCoalgebraStruct e)) :
        @CoalgHom R C D _ _ _ _ _ c.toCoalgebraStruct (e.coalgebraStruct R))
      e.symm.surjective = e.coalgebra R := rfl

end Coalgebra
