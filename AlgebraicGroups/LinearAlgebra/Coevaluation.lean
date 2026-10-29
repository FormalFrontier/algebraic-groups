/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# Coevaluation for finite projective modules

The inverse of `dualTensorHomEquiv` sends the identity to an intrinsic tensor.
After interchanging its factors, this is the coevaluation tensor in `V ⊗ V*`.
Together with `contractLeft`, it satisfies both linear tensor triangles, so
`V*` is a left dual of `V`.

No basis, presentation, or finiteness assumption on a target module is needed.
This is an upstream generalization candidate for the field-valued construction
in `Mathlib.LinearAlgebra.Coevaluation`; the compatibility theorem is in
`AlgebraicGroups.LinearAlgebra.Coevaluation.Field`.
-/

@[expose] public section

noncomputable section

namespace Module

open TensorProduct

universe u v w

variable (R : Type u) [CommSemiring R]
variable (V : Type v) [AddCommMonoid V] [Module R V]

/-- Computing the first contraction of an arbitrary tensor uses the stock
map from a dual tensor product to linear maps. -/
private theorem left_contraction (t : V ⊗[R] Dual R V) (v : V) :
    TensorProduct.rid R V
        (TensorProduct.map (LinearMap.id : V →ₗ[R] V) (contractLeft R V)
          (TensorProduct.assoc R V (Dual R V) V (t ⊗ₜ[R] v))) =
      dualTensorHom R V V ((TensorProduct.comm R (Dual R V) V).symm t) v := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul x f => simp
  | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
      rw [h₁, h₂]

/-- The other contraction is obtained from the same tensor by functional
extensionality and commutativity of the scalar semiring. -/
private theorem right_contraction (t : V ⊗[R] Dual R V) (f : Dual R V) (v : V) :
    (TensorProduct.lid R (Dual R V)
        (TensorProduct.map (contractLeft R V) (LinearMap.id : Dual R V →ₗ[R] Dual R V)
          ((TensorProduct.assoc R (Dual R V) V (Dual R V)).symm
            (f ⊗ₜ[R] t)))) v =
      f (dualTensorHom R V V ((TensorProduct.comm R (Dual R V) V).symm t) v) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul x g => simp [mul_comm]
  | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
      rw [h₁, h₂]

variable [Module.Finite R V] [Module.Projective R V]

/-- The intrinsic coevaluation tensor of a finite projective module. -/
def coevaluationTensor : V ⊗[R] Dual R V :=
  TensorProduct.comm R (Dual R V) V
    ((dualTensorHomEquiv R V V).symm (LinearMap.id : V →ₗ[R] V))

/-- The intrinsic tensor represents the identity endomorphism. -/
theorem coevaluationTensor_characteristic :
    dualTensorHom R V V
        ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V)) =
      LinearMap.id := by
  rw [coevaluationTensor, LinearEquiv.symm_apply_apply]
  exact dualTensorHom_dualTensorHomEquiv_symm (LinearMap.id : V →ₗ[R] V)

/-- The characteristic identity in simp-normal form for tensor symmetry. -/
@[simp] theorem dualTensorHom_comm_coevaluationTensor :
    dualTensorHom R V V
        (TensorProduct.comm R V (Dual R V) (coevaluationTensor R V)) =
      LinearMap.id := by
  simpa only [TensorProduct.comm_symm] using (coevaluationTensor_characteristic R V)

/-- The characteristic identity holds at every vector. -/
theorem coevaluationTensor_characteristic_apply (v : V) :
    dualTensorHom R V V
        ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V)) v = v :=
  LinearMap.congr_fun (coevaluationTensor_characteristic R V) v

/-- The identity contraction determines the coevaluation tensor uniquely. -/
theorem coevaluationTensor_eq_of_contraction (t : V ⊗[R] Dual R V)
    (h : ∀ v : V, TensorProduct.rid R V
      (TensorProduct.map (LinearMap.id : V →ₗ[R] V) (contractLeft R V)
        (TensorProduct.assoc R V (Dual R V) V (t ⊗ₜ[R] v))) = v) :
    t = coevaluationTensor R V := by
  apply (TensorProduct.comm R (Dual R V) V).symm.injective
  apply (dualTensorHomEquiv R V V).injective
  ext v
  change dualTensorHom R V V ((TensorProduct.comm R (Dual R V) V).symm t) v =
    dualTensorHom R V V
      ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V)) v
  rw [coevaluationTensor_characteristic_apply, ← left_contraction]
  exact h v

/-- Any finite tensor presentation of the intrinsic tensor satisfies the
identity formula; no such presentation is selected as public data. -/
theorem coevaluationTensor_sum_characteristic {ι : Type*} (s : Finset ι)
    (x : ι → V) (f : ι → Dual R V)
    (h : (∑ i ∈ s, x i ⊗ₜ[R] f i) = coevaluationTensor R V) (v : V) :
    (∑ i ∈ s, f i v • x i) = v := by
  have h' := congrArg
    (fun t => dualTensorHom R V V ((TensorProduct.comm R (Dual R V) V).symm t) v) h
  simpa only [map_sum, LinearMap.sum_apply, TensorProduct.comm_symm_tmul,
    dualTensorHom_apply, coevaluationTensor_characteristic_apply] using h'

/-- Naturality of the stock contraction equivalence expresses every inverse
image using the identity tensor. The target module is arbitrary. -/
theorem dualTensorHomEquiv_symm_eq_coevaluationTensor
    {N : Type w} [AddCommMonoid N] [Module R N] (f : V →ₗ[R] N) :
    (dualTensorHomEquiv R V N).symm f =
      f.lTensor (Dual R V)
        ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V)) := by
  apply (dualTensorHomEquiv R V N).injective
  rw [LinearEquiv.apply_symm_apply]
  change f = dualTensorHom R V N
    (f.lTensor (Dual R V)
      ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V)))
  calc
    f = f.comp (dualTensorHom R V V
        ((TensorProduct.comm R (Dual R V) V).symm (coevaluationTensor R V))) := by
      rw [coevaluationTensor_characteristic]
      simp
    _ = _ := (LinearMap.congr_fun
      (dualTensorHom_comp_lTensor (R := R) (M := V) f) _).symm

/-- Coevaluation sends a scalar to its multiple of the intrinsic tensor. -/
def coevaluation : R →ₗ[R] V ⊗[R] Dual R V :=
  (LinearMap.id : R →ₗ[R] R).smulRight (coevaluationTensor R V)

@[simp] theorem coevaluation_apply (r : R) :
    coevaluation R V r = r • coevaluationTensor R V := rfl

theorem coevaluation_apply_one :
    coevaluation R V 1 = coevaluationTensor R V := by
  simp only [coevaluation_apply, one_smul]

/-- The triangle on `V`, using exactly the stock associator and unitors. -/
theorem coevaluation_triangle :
    (TensorProduct.rid R V).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.id : V →ₗ[R] V) (contractLeft R V) ∘ₗ
          (TensorProduct.assoc R V (Dual R V) V).toLinearMap ∘ₗ
            TensorProduct.map (coevaluation R V) (LinearMap.id : V →ₗ[R] V) ∘ₗ
              (TensorProduct.lid R V).symm.toLinearMap =
      LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.lid_symm_apply, TensorProduct.map_tmul,
    coevaluation_apply_one, LinearMap.id_apply]
  rw [left_contraction, coevaluationTensor_characteristic_apply]

/-- The triangle on `V*` follows from the same characteristic identity.
It does not assume separately that `V*` is finite or projective. -/
theorem coevaluation_dual_triangle :
    (TensorProduct.lid R (Dual R V)).toLinearMap ∘ₗ
        TensorProduct.map (contractLeft R V) (LinearMap.id : Dual R V →ₗ[R] Dual R V) ∘ₗ
          (TensorProduct.assoc R (Dual R V) V (Dual R V)).symm.toLinearMap ∘ₗ
            TensorProduct.map (LinearMap.id : Dual R V →ₗ[R] Dual R V) (coevaluation R V) ∘ₗ
              (TensorProduct.rid R (Dual R V)).symm.toLinearMap =
      LinearMap.id := by
  ext f v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.rid_symm_apply, TensorProduct.map_tmul,
    coevaluation_apply_one, LinearMap.id_apply]
  rw [right_contraction, coevaluationTensor_characteristic_apply]

end Module
