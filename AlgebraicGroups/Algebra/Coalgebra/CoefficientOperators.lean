/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Composition of linear coefficient operators

Given an `R`-linear map `δ : M →ₗ[R] C ⊗[R] M` and a linear coefficient
`α : C →ₗ[R] A`, the tensor extension of `(TensorProduct.map α LinearMap.id).comp δ`
is an `A`-linear endomorphism of `A ⊗[R] M`. It sends `a ⊗ₜ m` to
`a • (TensorProduct.map α LinearMap.id) (δ m)`.

Relative coassociativity of `δ` with respect to an explicit linear map
`Δ : C →ₗ[R] C ⊗[R] C` implies a composition law: applying the operator for `α`
first and that for `β` second multiplies the outer coefficient `α` before the
inner coefficient `β`. The tester algebra `A` need not be commutative.

The construction and proof use Mathlib's tensor extension and tensor universal
properties. No multiplication on `C`, counit, or global coassociativity law on `Δ`
is required.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe uR uC uM uA

variable {R : Type uR} {C : Type uC} {M : Type uM} {A : Type uA}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid M] [Module R M] [Semiring A] [Algebra R A]

/-- Relative coassociativity of a given left linear coaction implies composition
of its tensor-extended coefficient operators. The operator for `β` is applied
after the operator for `α`, so their coefficient is
`(LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ)` in this order.
Only the displayed relative coassociativity equation is needed; neither a counit
nor a coalgebra structure on `C` is assumed. -/
theorem lift_toSpanSingleton_comp_map_of_coassoc
    (Δ : C →ₗ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M)
    (α β : C →ₗ[R] A)
    (hδ : (TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) :
    (lift
      (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
      (lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map α (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map
            ((LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ))
            (LinearMap.id : M →ₗ[R] M)).comp δ)) := by
  let F : (C ⊗[R] C) ⊗[R] M →ₗ[R] A ⊗[R] M :=
    TensorProduct.map ((LinearMap.mul' R A).comp (TensorProduct.map α β))
      (LinearMap.id : M →ₗ[R] M)
  -- Evaluate the two coefficients on a reassociated tensor, without choosing
  -- a decomposition of the given coaction.
  have hF (c : C) (x : C ⊗[R] M) :
      F ((TensorProduct.assoc R C C M).symm (c ⊗ₜ[R] x)) =
        α c • TensorProduct.map β (LinearMap.id : M →ₗ[R] M) x := by
    induction x using TensorProduct.inductionOn with
    | tmul d m =>
        simp only [F, TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
          LinearMap.comp_apply, LinearMap.id_apply, LinearMap.mul'_apply,
          TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy, smul_add]
  have hL (x : C ⊗[R] M) :
      lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))
          (TensorProduct.map α (LinearMap.id : M →ₗ[R] M) x) =
        F ((TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ x)) := by
    induction x using TensorProduct.inductionOn with
    | tmul c m =>
        simpa only [TensorProduct.map_tmul, LinearMap.id_apply, lift_tmul,
          LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
          LinearMap.comp_apply] using (hF c (δ m)).symm
    | add x y hx hy =>
        simp only [map_add, hx, hy]
  have hseed (m : M) :
      lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))
          (TensorProduct.map α (LinearMap.id : M →ₗ[R] M) (δ m)) =
        TensorProduct.map
          ((LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ))
          (LinearMap.id : M →ₗ[R] M) (δ m) := by
    have hδm : TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M) (δ m) =
        (TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ (δ m)) :=
      LinearMap.congr_fun hδ m
    calc
      _ = F ((TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ (δ m))) := hL (δ m)
      _ = F (TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M) (δ m)) :=
        congrArg F hδm.symm
      _ = _ := by
        simp only [F, TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_assoc]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simpa only [LinearMap.comp_apply, lift_tmul, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, map_smul] using
    congrArg (fun z : A ⊗[R] M => a • z) (hseed m)

end TensorProduct.AlgebraTensorModule
