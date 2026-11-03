/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Antipode tensors on the linear dual

Represent contraction of the first comultiplication leg against a functional,
followed by the antipode on the second leg, as a tensor in the original dual
and the carrier. The tensor/endomorphism correspondence is Mathlib's
`dualTensorHomEquiv`.

## Implementation notes

This construction uses `HopfAlgebraStruct` data and does not assert comodule
laws for the linear dual. The dual retains its pointwise scalar action; no
algebra action on the dual is needed.
-/

public section

open scoped TensorProduct

universe uR uH

namespace HopfAlgebra

variable (R : Type uR) (H : Type uH)
  [CommSemiring R] [Semiring H] [HopfAlgebraStruct R H]

/-- Contraction against a functional on the first comultiplication leg,
followed by the antipode on the second leg. -/
private def antipodeDualEnd : Module.Dual R H →ₗ[R] Module.End R H where
  toFun φ :=
    (TensorProduct.lid R H).toLinearMap ∘ₗ
      TensorProduct.map φ (HopfAlgebra.antipode R) ∘ₗ
      Coalgebra.comul (R := R)
  map_add' φ ψ := by
    ext x
    simp only [LinearMap.comp_apply, TensorProduct.map_add_left,
      LinearMap.add_apply, map_add]
  map_smul' r φ := by
    ext x
    simp only [LinearMap.comp_apply, TensorProduct.map_smul_left,
      LinearMap.smul_apply, map_smul]
    rfl

/-- The tensor representing contraction against a functional on the first
comultiplication leg and the antipode on the second leg. -/
noncomputable def antipodeDualTensor
    [Module.Finite R H] [Module.Projective R H] :
    Module.Dual R H →ₗ[R] Module.Dual R H ⊗[R] H :=
  (dualTensorHomEquiv R H H).symm.toLinearMap ∘ₗ antipodeDualEnd R H

@[expose] public section

variable [Module.Finite R H] [Module.Projective R H]

/-- Applying the tensor/endomorphism correspondence to an antipode tensor
recovers contraction of comultiplication against the functional and antipode. -/
@[simp]
theorem dualTensorHom_antipodeDualTensor_apply (φ : Module.Dual R H) (x : H) :
    dualTensorHom R H H (antipodeDualTensor R H φ) x =
      (TensorProduct.lid R H)
        (TensorProduct.map φ (HopfAlgebra.antipode R) (Coalgebra.comul (R := R) x)) := by
  change dualTensorHom R H H
    ((dualTensorHomEquiv R H H).symm (antipodeDualEnd R H φ)) x = _
  rw [dualTensorHom_dualTensorHomEquiv_symm]
  rfl

/-- Evaluating the dual leg of an antipode tensor contracts the first
comultiplication leg and applies the antipode to the second leg. -/
@[simp]
theorem antipodeDualTensor_eval (φ : Module.Dual R H) (x : H) :
    (TensorProduct.lid R H)
        (TensorProduct.map (Module.Dual.eval R H x) (LinearMap.id : H →ₗ[R] H)
          (antipodeDualTensor R H φ)) =
      (TensorProduct.lid R H)
        (TensorProduct.map φ (HopfAlgebra.antipode R) (Coalgebra.comul (R := R) x)) := by
  have eval_eq (t : Module.Dual R H ⊗[R] H) :
      (TensorProduct.lid R H)
          (TensorProduct.map (Module.Dual.eval R H x) (LinearMap.id : H →ₗ[R] H) t) =
        dualTensorHom R H H t x := by
    induction t using TensorProduct.inductionOn with
    | tmul ψ h =>
        simp only [TensorProduct.map_tmul, Module.Dual.eval_apply,
          LinearMap.id_apply, TensorProduct.lid_tmul, dualTensorHom_apply]
    | add t u ht hu =>
        simp only [map_add, LinearMap.add_apply, ht, hu]
  rw [eval_eq, dualTensorHom_antipodeDualTensor_apply]

/-- An antipode tensor is uniquely determined by the evaluations of its
associated endomorphism. -/
theorem antipodeDualTensor_eq_iff (φ : Module.Dual R H)
    (t : Module.Dual R H ⊗[R] H) :
    antipodeDualTensor R H φ = t ↔
      ∀ x : H, dualTensorHom R H H t x =
        (TensorProduct.lid R H)
          (TensorProduct.map φ (HopfAlgebra.antipode R) (Coalgebra.comul (R := R) x)) := by
  constructor
  · rintro rfl x
    exact dualTensorHom_antipodeDualTensor_apply R H φ x
  · intro ht
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext x
    exact (dualTensorHom_antipodeDualTensor_apply R H φ x).trans (ht x).symm

end

end HopfAlgebra
