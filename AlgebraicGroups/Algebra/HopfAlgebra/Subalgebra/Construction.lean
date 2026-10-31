/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subalgebra
public import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# The Hopf algebra structure on a stable subalgebra

A subalgebra closed under comultiplication and the antipode inherits a full Hopf
algebra structure on its original algebra and module. The inclusion is a bialgebra
homomorphism. All characteristic formulas use the original subtype inclusion.
-/

@[expose] public section

universe u v

open Coalgebra TensorProduct
open scoped TensorProduct

namespace Subalgebra

variable {K : Type u} {B : Type v} [Field K] [Semiring B] [HopfAlgebra K B]
variable (S : Subalgebra K B)

private def restrictedAntipode
    (hσ : ∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S) : S →ₗ[K] S :=
  LinearMap.codRestrict S.toSubmodule
    ((HopfAlgebra.antipode K).comp S.val.toLinearMap) hσ

private theorem restrictedAntipode_coe
    (hσ : ∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S) (s : S) :
    (restrictedAntipode S hσ s : B) = HopfAlgebra.antipode K (s : B) := rfl

private theorem tensorInclusion_one :
    TensorProduct.map S.val.toLinearMap S.val.toLinearMap (1 : S ⊗[K] S) = 1 :=
  (Algebra.TensorProduct.map S.val S.val).map_one

private theorem tensorInclusion_mul (x y : S ⊗[K] S) :
    TensorProduct.map S.val.toLinearMap S.val.toLinearMap (x * y) =
      TensorProduct.map S.val.toLinearMap S.val.toLinearMap x *
        TensorProduct.map S.val.toLinearMap S.val.toLinearMap y :=
  (Algebra.TensorProduct.map S.val S.val).map_mul x y

private theorem tensorInclusion_injective :
    Function.Injective (TensorProduct.map S.val.toLinearMap S.val.toLinearMap) := by
  let originalB : AddCommMonoid B := inferInstance
  let originalS : AddCommMonoid S := inferInstance
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup S := Module.addCommMonoidToAddCommGroup K
  have hB : (inferInstance : AddCommGroup B).toAddCommMonoid = originalB := rfl
  have hS : (inferInstance : AddCommGroup S).toAddCommMonoid = originalS := rfl
  cases hB
  cases hS
  exact TensorProduct.map_injective_of_flat_flat S.val.toLinearMap S.val.toLinearMap
    Subtype.val_injective Subtype.val_injective

private theorem restrictedAntipode_convMul_id [Coalgebra K S]
    (hΔ : ∀ s : S, TensorProduct.map S.val.toLinearMap S.val.toLinearMap
      (Coalgebra.comul (R := K) s) = Coalgebra.comul (R := K) (s : B))
    (hε : ∀ s : S, Coalgebra.counit (R := K) s = Coalgebra.counit (R := K) (s : B))
    (hσ : ∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S) :
    WithConv.toConv (restrictedAntipode S hσ) *
      WithConv.toConv (LinearMap.id : S →ₗ[K] S) = 1 := by
  have hm :
      S.val.toLinearMap ∘ₗ LinearMap.mul' K S ∘ₗ
          TensorProduct.map (restrictedAntipode S hσ) (LinearMap.id : S →ₗ[K] S) =
        LinearMap.mul' K B ∘ₗ
          TensorProduct.map (HopfAlgebra.antipode K) (LinearMap.id : B →ₗ[K] B) ∘ₗ
            TensorProduct.map S.val.toLinearMap S.val.toLinearMap := by
    ext a b
    rfl
  apply WithConv.ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change ((LinearMap.mul' K S
    (TensorProduct.map (restrictedAntipode S hσ) (LinearMap.id : S →ₗ[K] S)
      (Coalgebra.comul s)) : S) : B) =
        (algebraMap K S (Coalgebra.counit s) : B)
  calc
    _ = LinearMap.mul' K B
        (TensorProduct.map (HopfAlgebra.antipode K) (LinearMap.id : B →ₗ[K] B)
          (TensorProduct.map S.val.toLinearMap S.val.toLinearMap (Coalgebra.comul s))) :=
      LinearMap.congr_fun hm (Coalgebra.comul s)
    _ = algebraMap K B (Coalgebra.counit (R := K) (s : B)) := by
      rw [hΔ]
      exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := K) (s : B)
    _ = _ := by rw [hε]; rfl

private theorem id_convMul_restrictedAntipode [Coalgebra K S]
    (hΔ : ∀ s : S, TensorProduct.map S.val.toLinearMap S.val.toLinearMap
      (Coalgebra.comul (R := K) s) = Coalgebra.comul (R := K) (s : B))
    (hε : ∀ s : S, Coalgebra.counit (R := K) s = Coalgebra.counit (R := K) (s : B))
    (hσ : ∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S) :
    WithConv.toConv (LinearMap.id : S →ₗ[K] S) *
      WithConv.toConv (restrictedAntipode S hσ) = 1 := by
  have hm :
      S.val.toLinearMap ∘ₗ LinearMap.mul' K S ∘ₗ
          TensorProduct.map (LinearMap.id : S →ₗ[K] S) (restrictedAntipode S hσ) =
        LinearMap.mul' K B ∘ₗ
          TensorProduct.map (LinearMap.id : B →ₗ[K] B) (HopfAlgebra.antipode K) ∘ₗ
            TensorProduct.map S.val.toLinearMap S.val.toLinearMap := by
    ext a b
    rfl
  apply WithConv.ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change ((LinearMap.mul' K S
    (TensorProduct.map (LinearMap.id : S →ₗ[K] S) (restrictedAntipode S hσ)
      (Coalgebra.comul s)) : S) : B) =
        (algebraMap K S (Coalgebra.counit s) : B)
  calc
    _ = LinearMap.mul' K B
        (TensorProduct.map (LinearMap.id : B →ₗ[K] B) (HopfAlgebra.antipode K)
          (TensorProduct.map S.val.toLinearMap S.val.toLinearMap (Coalgebra.comul s))) :=
      LinearMap.congr_fun hm (Coalgebra.comul s)
    _ = algebraMap K B (Coalgebra.counit (R := K) (s : B)) := by
      rw [hΔ]
      exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) (s : B)
    _ = _ := by rw [hε]; rfl

/-- A subalgebra stable under comultiplication and the antipode inherits a Hopf algebra
structure on its inherited algebra and module. -/
@[instance_reducible]
noncomputable def hopfAlgebra (h : S.IsHopfSubalgebra) : HopfAlgebra K S := by
  letI : Coalgebra K S := S.coalgebraOfComulMem h.comul_mem
  letI : Bialgebra K S := Bialgebra.mk' K S
    (by
      rw [S.coalgebraOfComulMem_counit h.comul_mem]
      exact Bialgebra.counit_one)
    (by
      intro a b
      rw [S.coalgebraOfComulMem_counit h.comul_mem,
        S.coalgebraOfComulMem_counit h.comul_mem,
        S.coalgebraOfComulMem_counit h.comul_mem]
      exact Bialgebra.counit_mul (a : B) (b : B))
    (by
      apply tensorInclusion_injective S
      rw [S.coalgebraOfComulMem_comul h.comul_mem, tensorInclusion_one]
      exact Bialgebra.comul_one)
    (by
      intro a b
      apply tensorInclusion_injective S
      calc
        _ = Coalgebra.comul (R := K) ((a : B) * (b : B)) :=
          S.coalgebraOfComulMem_comul h.comul_mem (a * b)
        _ = Coalgebra.comul (R := K) (a : B) * Coalgebra.comul (R := K) (b : B) :=
          Bialgebra.comul_mul (a : B) (b : B)
        _ = _ := by
          rw [tensorInclusion_mul, S.coalgebraOfComulMem_comul h.comul_mem,
            S.coalgebraOfComulMem_comul h.comul_mem])
  exact HopfAlgebra.ofConvInverse
    (LinearMap.codRestrict S.toSubmodule
      ((HopfAlgebra.antipode K).comp S.val.toLinearMap) h.antipode_mem)
    (by
      exact restrictedAntipode_convMul_id S
        (S.coalgebraOfComulMem_comul h.comul_mem)
        (S.coalgebraOfComulMem_counit h.comul_mem) h.antipode_mem)
    (by
      exact id_convMul_restrictedAntipode S
        (S.coalgebraOfComulMem_comul h.comul_mem)
        (S.coalgebraOfComulMem_counit h.comul_mem) h.antipode_mem)

/-- The induced Hopf algebra retains the inherited algebra structure. -/
@[simp] theorem hopfAlgebra_toAlgebra (h : S.IsHopfSubalgebra) :
    (S.hopfAlgebra h).toBialgebra.toAlgebra = (inferInstance : Algebra K S) := rfl

/-- The induced Hopf algebra retains the inherited scalar action. -/
theorem hopfAlgebra_toModule (h : S.IsHopfSubalgebra) :
    @Algebra.toModule K S _ _ (S.hopfAlgebra h).toBialgebra.toAlgebra =
      (inferInstance : Module K S) := rfl

/-- The coalgebra parent is the one induced by comultiplication stability. -/
@[simp] theorem hopfAlgebra_toCoalgebra (h : S.IsHopfSubalgebra) :
    (S.hopfAlgebra h).toBialgebra.toCoalgebra =
      S.coalgebraOfComulMem h.comul_mem := rfl

/-- The antipode on the subalgebra is the restriction of the ambient antipode. -/
@[simp] theorem hopfAlgebra_antipode (h : S.IsHopfSubalgebra) (s : S) :
    ((@HopfAlgebra.antipode K S _ _
      (S.hopfAlgebra h).toHopfAlgebraStruct) s : B) =
        HopfAlgebra.antipode K (s : B) :=
  restrictedAntipode_coe S h.antipode_mem s

/-- The subtype inclusion of a Hopf-stable subalgebra as a bialgebra homomorphism. -/
noncomputable def inclusionBialgHom (h : S.IsHopfSubalgebra) :
    @BialgHom K S B _ _ _ _ _
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (inferInstance : CoalgebraStruct K B) := by
  let : Coalgebra K S := S.coalgebraOfComulMem h.comul_mem
  exact
    { __ := S.val
      map_smul' := map_smul S.val
      counit_comp := (S.coalgebraOfComulMem_counit_comp_val h.comul_mem).symm
      map_comp_comul := S.coalgebraOfComulMem_map_comp_comul h.comul_mem }

/-- The algebra homomorphism underlying the inclusion is the subtype inclusion. -/
@[simp] theorem inclusionBialgHom_toAlgHom (h : S.IsHopfSubalgebra) :
    @BialgHom.toAlgHom K S B _ _ _ _ _
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (inferInstance : CoalgebraStruct K B) (S.inclusionBialgHom h) = S.val := rfl

/-- The linear map underlying the inclusion is the subtype inclusion. -/
@[simp] theorem inclusionBialgHom_toLinearMap (h : S.IsHopfSubalgebra) :
    ((@BialgHom.toCoalgHom K S B _ _ _ _ _
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (inferInstance : CoalgebraStruct K B) (S.inclusionBialgHom h)) : S →ₗ[K] B) =
      S.val.toLinearMap := rfl

/-- The bialgebra inclusion sends a subalgebra element to its ambient value. -/
@[simp] theorem inclusionBialgHom_apply (h : S.IsHopfSubalgebra) (s : S) :
    S.inclusionBialgHom h s = (s : B) := rfl

/-- The opposite-valued antipode has the expected ambient value after taking `unop`. -/
theorem inclusionBialgHom_unop_antipodeAlgHomOp
    (h : S.IsHopfSubalgebra) (s : S) :
    ((MulOpposite.unop
      ((@HopfAlgebra.antipodeAlgHomOp K S _ _ (S.hopfAlgebra h)) s) : S) : B) =
        HopfAlgebra.antipode K (s : B) := by
  change ((@HopfAlgebra.antipode K S _ _
    (S.hopfAlgebra h).toHopfAlgebraStruct) s : B) = _
  exact S.hopfAlgebra_antipode h s

end Subalgebra
