/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# The coalgebra of a subcoalgebra

The comultiplication of a subcoalgebra is the unique lift of the ambient comultiplication
through the inclusion of its tensor square. Its counit is the restriction of the ambient
counit. These maps satisfy the coalgebra laws, by injectivity of tensor inclusions over a
field and naturality of tensor maps and the associator.

`Subcoalgebra.coalgebra` constructs the coalgebra on the underlying submodule subtype.
The characteristic inclusion equations describe its comultiplication and counit without
unfolding their definitions.

## References

The construction uses Mathlib's `LinearMap.codLift` and `LinearMap.comp_codLift`.
Injectivity follows from `Module.Free.of_divisionRing`, `Module.Flat.of_free`, and
`Module.Flat.tensorProduct_mapIncl_injective_of_right`. The proofs use the tensor-map
composition and associator naturality API from `Mathlib.LinearAlgebra.TensorProduct.Map`
and `Mathlib.LinearAlgebra.TensorProduct.Associator`, and the laws in
`Mathlib.RingTheory.Coalgebra.Basic`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The comultiplication restricted to the tensor square of a subcoalgebra. -/
noncomputable def comul (D : Subcoalgebra K C) :
    D.toSubmodule →ₗ[K] D.toSubmodule ⊗[K] D.toSubmodule :=
  ((Coalgebra.comul (R := K) (A := C)).domRestrict D.toSubmodule).codLift
    (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
    (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
    (fun x => D.comul_mem' x.property)

/-- The counit restricted to a subcoalgebra. -/
def counit (D : Subcoalgebra K C) : D.toSubmodule →ₗ[K] K :=
  (Coalgebra.counit (R := K) (A := C)).domRestrict D.toSubmodule

/-- Tensor inclusion intertwines the restricted and ambient comultiplications. -/
@[simp]
theorem mapIncl_comp_comul (D : Subcoalgebra K C) :
    TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ D.comul =
      Coalgebra.comul (R := K) (A := C) ∘ₗ D.toSubmodule.subtype := by
  simpa only [comul, LinearMap.domRestrict] using
    (LinearMap.comp_codLift
      ((Coalgebra.comul (R := K) (A := C)).domRestrict D.toSubmodule)
      (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
      (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
      (fun x => D.comul_mem' x.property))

/-- The ambient counit composed with inclusion is the restricted counit. -/
@[simp]
theorem counit_comp_subtype (D : Subcoalgebra K C) :
    Coalgebra.counit (R := K) (A := C) ∘ₗ D.toSubmodule.subtype = D.counit :=
  rfl

/-- The image of the restricted comultiplication is the ambient comultiplication. -/
@[simp]
theorem mapIncl_comul (D : Subcoalgebra K C) (x : D) :
    DFunLike.coe (F := D ⊗[K] D →ₗ[K] C ⊗[K] C)
      (α := D ⊗[K] D) (β := fun _ => C ⊗[K] C)
      (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
      (DFunLike.coe (F := D →ₗ[K] D ⊗[K] D)
        (α := D) (β := fun _ => D ⊗[K] D) D.comul x) =
      Coalgebra.comul (R := K) (A := C) (x : C) :=
  LinearMap.congr_fun D.mapIncl_comp_comul x

/-- The restricted counit agrees with the ambient counit on every member. -/
@[simp]
theorem counit_apply (D : Subcoalgebra K C) (x : D) :
    DFunLike.coe (F := D →ₗ[K] K) (α := D) (β := fun _ => K) D.counit x =
      Coalgebra.counit (R := K) (A := C) (x : C) :=
  rfl

private lemma map_rTensor_comul (D : Subcoalgebra K C)
    (z : D.toSubmodule ⊗[K] D.toSubmodule) :
    TensorProduct.map (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
        D.toSubmodule.subtype (D.comul.rTensor D.toSubmodule z) =
      (Coalgebra.comul (R := K) (A := C)).rTensor C
        (TensorProduct.mapIncl D.toSubmodule D.toSubmodule z) := by
  rw [LinearMap.map_rTensor, D.mapIncl_comp_comul, LinearMap.rTensor_map]

private lemma map_lTensor_comul (D : Subcoalgebra K C)
    (z : D.toSubmodule ⊗[K] D.toSubmodule) :
    TensorProduct.map D.toSubmodule.subtype
        (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
        (D.comul.lTensor D.toSubmodule z) =
      (Coalgebra.comul (R := K) (A := C)).lTensor C
        (TensorProduct.mapIncl D.toSubmodule D.toSubmodule z) := by
  rw [LinearMap.map_lTensor, D.mapIncl_comp_comul, LinearMap.lTensor_map]

private lemma lTensor_subtype_comp_rTensor_counit (D : Subcoalgebra K C) :
    D.toSubmodule.subtype.lTensor K ∘ₗ D.counit.rTensor D.toSubmodule =
      (Coalgebra.counit (R := K) (A := C)).rTensor C ∘ₗ
        TensorProduct.mapIncl D.toSubmodule D.toSubmodule := by
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_map, D.counit_comp_subtype]

private lemma rTensor_subtype_comp_lTensor_counit (D : Subcoalgebra K C) :
    D.toSubmodule.subtype.rTensor K ∘ₗ D.counit.lTensor D.toSubmodule =
      (Coalgebra.counit (R := K) (A := C)).lTensor C ∘ₗ
        TensorProduct.mapIncl D.toSubmodule D.toSubmodule := by
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_map, D.counit_comp_subtype]

/-- The restricted comultiplication is coassociative. -/
theorem coassoc (D : Subcoalgebra K C) :
    TensorProduct.assoc K D.toSubmodule D.toSubmodule D.toSubmodule ∘ₗ
        D.comul.rTensor D.toSubmodule ∘ₗ D.comul =
      D.comul.lTensor D.toSubmodule ∘ₗ D.comul := by
  apply LinearMap.ext
  intro x
  apply TensorProduct.map_injective_of_flat_flat D.toSubmodule.subtype
    (TensorProduct.mapIncl D.toSubmodule D.toSubmodule) D.toSubmodule.subtype_injective
    (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  calc
    TensorProduct.map D.toSubmodule.subtype
        (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
        (TensorProduct.assoc K D.toSubmodule D.toSubmodule D.toSubmodule
          (D.comul.rTensor D.toSubmodule (D.comul x))) =
        TensorProduct.assoc K C C C
          (TensorProduct.map (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
            D.toSubmodule.subtype (D.comul.rTensor D.toSubmodule (D.comul x))) :=
      TensorProduct.map_map_assoc D.toSubmodule.subtype D.toSubmodule.subtype
        D.toSubmodule.subtype _
    _ = TensorProduct.assoc K C C C
        ((Coalgebra.comul (R := K) (A := C)).rTensor C
          (Coalgebra.comul (R := K) (A := C) (x : C))) := by
      rw [map_rTensor_comul, D.mapIncl_comul]
    _ = (Coalgebra.comul (R := K) (A := C)).lTensor C
        (Coalgebra.comul (R := K) (A := C) (x : C)) :=
      Coalgebra.coassoc_apply (R := K) (A := C) (x : C)
    _ = TensorProduct.map D.toSubmodule.subtype
        (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
        (D.comul.lTensor D.toSubmodule (D.comul x)) := by
      rw [map_lTensor_comul, D.mapIncl_comul]

/-- The restricted counit satisfies the left counitality law. -/
theorem rTensor_counit_comp_comul (D : Subcoalgebra K C) :
    D.counit.rTensor D.toSubmodule ∘ₗ D.comul =
      TensorProduct.mk K K D.toSubmodule 1 := by
  apply LinearMap.ext
  intro x
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := K) D.toSubmodule.subtype D.toSubmodule.subtype_injective
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
  calc
    D.toSubmodule.subtype.lTensor K (D.counit.rTensor D.toSubmodule (D.comul x)) =
        (Coalgebra.counit (R := K) (A := C)).rTensor C
          (TensorProduct.mapIncl D.toSubmodule D.toSubmodule (D.comul x)) :=
      LinearMap.congr_fun (lTensor_subtype_comp_rTensor_counit D) (D.comul x)
    _ = 1 ⊗ₜ[K] (x : C) := by
      rw [D.mapIncl_comul, Coalgebra.rTensor_counit_comul]
    _ = D.toSubmodule.subtype.lTensor K (1 ⊗ₜ[K] x) := by
      rw [LinearMap.lTensor_tmul]
      rfl

/-- The restricted counit satisfies the right counitality law. -/
theorem lTensor_counit_comp_comul (D : Subcoalgebra K C) :
    D.counit.lTensor D.toSubmodule ∘ₗ D.comul =
      (TensorProduct.mk K D.toSubmodule K).flip 1 := by
  apply LinearMap.ext
  intro x
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (M := K) D.toSubmodule.subtype D.toSubmodule.subtype_injective
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  calc
    D.toSubmodule.subtype.rTensor K (D.counit.lTensor D.toSubmodule (D.comul x)) =
        (Coalgebra.counit (R := K) (A := C)).lTensor C
          (TensorProduct.mapIncl D.toSubmodule D.toSubmodule (D.comul x)) :=
      LinearMap.congr_fun (rTensor_subtype_comp_lTensor_counit D) (D.comul x)
    _ = (x : C) ⊗ₜ[K] 1 := by
      rw [D.mapIncl_comul, Coalgebra.lTensor_counit_comul]
    _ = D.toSubmodule.subtype.rTensor K (x ⊗ₜ[K] 1) := by
      rw [LinearMap.rTensor_tmul]
      rfl

/-- The coalgebra on the underlying submodule subtype of a subcoalgebra, with the restricted
comultiplication and counit. -/
@[instance_reducible]
noncomputable def coalgebra (D : Subcoalgebra K C) : Coalgebra K D.toSubmodule where
  comul := D.comul
  counit := D.counit
  coassoc := D.coassoc
  rTensor_counit_comp_comul := D.rTensor_counit_comp_comul
  lTensor_counit_comp_comul := D.lTensor_counit_comp_comul

/-- The restricted coalgebra structure on the subtype of a subcoalgebra. -/
noncomputable instance instCoalgebra (D : Subcoalgebra K C) : Coalgebra K D :=
  D.coalgebra

end Subcoalgebra
