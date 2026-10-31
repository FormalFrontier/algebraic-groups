/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Equiv
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.NatInt

/-!
# Coalgebras on comultiplication-stable subalgebras

A subalgebra whose comultiplication lies in the image of its tensor square inherits a
coalgebra. The construction keeps the subalgebra's semiring, algebra and module structures.
Its comultiplication is characterized by the tensor inclusion, and its counit is the
restriction of the ambient counit.

## Implementation notes

The full coalgebra is obtained from `Subcoalgebra.coalgebra` by transport along the linear
equivalence between the subalgebra and its underlying submodule. Additive groups needed
for the subcoalgebra construction are derived locally from the field action; they retain
the given additive monoids. The full transport uses `CoalgEquiv.toCoalgebra`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Subalgebra

variable {K : Type u} {B : Type v}
variable [Field K] [Semiring B] [Algebra K B] [Coalgebra K B]

private theorem moduleAddCommGroup_toAddCommMonoid
    {M : Type*} [AddCommMonoid M] [Module K M] :
    (Module.addCommMonoidToAddCommGroup K (M := M)).toAddCommMonoid =
      (inferInstance : AddCommMonoid M) := rfl

private structure CoalgebraRestrictionData (S : Subalgebra K B) where
  coalgebra : Coalgebra K S
  counit_eq : @CoalgebraStruct.counit K S _ _ _ coalgebra.toCoalgebraStruct =
    Coalgebra.counit (R := K) (A := B) ∘ₗ S.val.toLinearMap
  comul_eq : TensorProduct.map S.val.toLinearMap S.val.toLinearMap ∘ₗ
      @CoalgebraStruct.comul K S _ _ _ coalgebra.toCoalgebraStruct =
    Coalgebra.comul (R := K) (A := B) ∘ₗ S.val.toLinearMap

private noncomputable def coalgebraRestrictionData (S : Subalgebra K B)
    (hΔ : ∀ s : S, Coalgebra.comul (R := K) (s : B) ∈
      LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)) :
    CoalgebraRestrictionData S := by
  let mB : Module K B := inferInstance
  let mS : Module K S := inferInstance
  have hB := moduleAddCommGroup_toAddCommMonoid (K := K) (M := B)
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  have hmB : (inferInstance : Module K B) = mB := rfl
  have hmS : (inferInstance : Module K S) = mS := rfl
  let D : Subcoalgebra K B :=
    { toSubmodule := S.toSubmodule
      comul_mem' := by
        intro x hx
        change Coalgebra.comul (R := K) x ∈
          LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)
        exact hΔ ⟨x, hx⟩ }
  have hD : D.toSubmodule = S.toSubmodule := rfl
  let e : S ≃ₗ[K] D.toSubmodule := S.toSubmoduleEquiv.symm
  have he (s : S) : ((e s : D.toSubmodule) : B) = (s : B) := rfl
  have hval : D.toSubmodule.subtype ∘ₗ e.toLinearMap = S.val.toLinearMap := by
    ext s
    exact he s
  letI : Coalgebra K D.toSubmodule := D.coalgebra
  let cS : CoalgebraStruct K S := e.coalgebraStruct K
  let q : @CoalgEquiv K _ S D.toSubmodule _ _ _ _
      cS D.coalgebra.toCoalgebraStruct :=
    @LinearEquiv.toCoalgEquiv K S D.toSubmodule _ _ mS _ D.module
      D.coalgebra.toCoalgebraStruct e
  let f : @CoalgHom K S D.toSubmodule _ _ mS _ D.module
      cS D.coalgebra.toCoalgebraStruct :=
    @CoalgEquiv.toCoalgHom K _ S D.toSubmodule _ _ mS D.module
      cS D.coalgebra.toCoalgebraStruct q
  -- Complete the coalgebra laws for the selected data on the original subalgebra.
  let c : Coalgebra K S :=
    @CoalgEquiv.toCoalgebra K D.toSubmodule S _ _ _ D.coalgebra _ _ cS
      (@CoalgEquiv.symm K S D.toSubmodule _ _ _ _ _
        cS D.coalgebra.toCoalgebraStruct q)
  have heΔ : TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
      @CoalgebraStruct.comul K S _ _ _ c.toCoalgebraStruct =
      D.comul ∘ₗ e.toLinearMap :=
    @CoalgHom.map_comp_comul K S D.toSubmodule _ _ mS _ D.module
      cS D.coalgebra.toCoalgebraStruct f
  have heε : @CoalgebraStruct.counit K S _ _ _ c.toCoalgebraStruct =
      D.counit ∘ₗ e.toLinearMap :=
    (@CoalgHom.counit_comp K S D.toSubmodule _ _ mS _ D.module
      cS D.coalgebra.toCoalgebraStruct f).symm
  have ht : TensorProduct.map S.val.toLinearMap S.val.toLinearMap =
      TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ
        TensorProduct.map e.toLinearMap e.toLinearMap := by
    rw [← TensorProduct.map_comp]
    rfl
  refine ⟨c, ?_, ?_⟩
  · calc
      @CoalgebraStruct.counit K S _ _ _ c.toCoalgebraStruct =
          D.counit ∘ₗ e.toLinearMap := heε
      _ = Coalgebra.counit (R := K) (A := B) ∘ₗ S.val.toLinearMap := by
        rw [← D.counit_comp_subtype, LinearMap.comp_assoc, hval]
  · calc
      TensorProduct.map S.val.toLinearMap S.val.toLinearMap ∘ₗ
          @CoalgebraStruct.comul K S _ _ _ c.toCoalgebraStruct =
          TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ
            (TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
              @CoalgebraStruct.comul K S _ _ _ c.toCoalgebraStruct) := by
        rw [ht, LinearMap.comp_assoc]
      _ = TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ
          (D.comul ∘ₗ e.toLinearMap) := by rw [heΔ]
      _ = Coalgebra.comul (R := K) (A := B) ∘ₗ S.val.toLinearMap := by
        rw [← LinearMap.comp_assoc, D.mapIncl_comp_comul, LinearMap.comp_assoc, hval]

/-- The coalgebra on a subalgebra whose comultiplication lies in its tensor square. -/
@[no_expose, instance_reducible]
noncomputable def coalgebraOfComulMem (S : Subalgebra K B)
    (hΔ : ∀ s : S, Coalgebra.comul (R := K) (s : B) ∈
      LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)) :
    Coalgebra K S :=
  (coalgebraRestrictionData S hΔ).coalgebra

variable (S : Subalgebra K B)
variable (hΔ : ∀ s : S, Coalgebra.comul (R := K) (s : B) ∈
  LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap))

/-- The induced counit is the ambient counit composed with the subalgebra inclusion. -/
theorem coalgebraOfComulMem_counit_comp_val :
    @CoalgebraStruct.counit K S _ _ _ (S.coalgebraOfComulMem hΔ).toCoalgebraStruct =
      Coalgebra.counit (R := K) (A := B) ∘ₗ S.val.toLinearMap :=
  (coalgebraRestrictionData S hΔ).counit_eq

/-- Tensor inclusion intertwines the induced and ambient comultiplications. -/
theorem coalgebraOfComulMem_map_comp_comul :
    TensorProduct.map S.val.toLinearMap S.val.toLinearMap ∘ₗ
        @CoalgebraStruct.comul K S _ _ _ (S.coalgebraOfComulMem hΔ).toCoalgebraStruct =
      Coalgebra.comul (R := K) (A := B) ∘ₗ S.val.toLinearMap :=
  (coalgebraRestrictionData S hΔ).comul_eq

/-- The induced counit agrees with the ambient counit on every member. -/
@[simp]
theorem coalgebraOfComulMem_counit (s : S) :
    @CoalgebraStruct.counit K S _ _ _ (S.coalgebraOfComulMem hΔ).toCoalgebraStruct s =
      Coalgebra.counit (R := K) (s : B) :=
  LinearMap.congr_fun (S.coalgebraOfComulMem_counit_comp_val hΔ) s

/-- The image of induced comultiplication under tensor inclusion is ambient comultiplication. -/
@[simp]
theorem coalgebraOfComulMem_comul (s : S) :
    TensorProduct.map S.val.toLinearMap S.val.toLinearMap
        (@CoalgebraStruct.comul K S _ _ _ (S.coalgebraOfComulMem hΔ).toCoalgebraStruct s) =
      Coalgebra.comul (R := K) (s : B) :=
  LinearMap.congr_fun (S.coalgebraOfComulMem_map_comp_comul hΔ) s

/-- The induced comultiplication is the unique linear map satisfying the tensor-inclusion
identity. -/
theorem coalgebraOfComulMem_comul_unique (d : S →ₗ[K] S ⊗[K] S)
    (hd : TensorProduct.map S.val.toLinearMap S.val.toLinearMap ∘ₗ d =
      Coalgebra.comul (R := K) (A := B) ∘ₗ S.val.toLinearMap) :
    d = @CoalgebraStruct.comul K S _ _ _ (S.coalgebraOfComulMem hΔ).toCoalgebraStruct := by
  let mB : Module K B := inferInstance
  let mS : Module K S := inferInstance
  have hB := moduleAddCommGroup_toAddCommMonoid (K := K) (M := B)
  have hS := moduleAddCommGroup_toAddCommMonoid (K := K) (M := S)
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup S := Module.addCommMonoidToAddCommGroup K
  have hmB : (inferInstance : Module K B) = mB := rfl
  have hmS : (inferInstance : Module K S) = mS := rfl
  have hi : Function.Injective (TensorProduct.map S.val.toLinearMap S.val.toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat S.val.toLinearMap S.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  ext s
  apply hi
  exact (LinearMap.congr_fun hd s).trans (S.coalgebraOfComulMem_comul hΔ s).symm

end Subalgebra
