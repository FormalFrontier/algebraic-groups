/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct

/-!
# Regular and bottom-subcomodule tensor coactions

Two regular comodules over `ℕ` give the comultiplication of Mathlib's tensor
coalgebra on `ℕ ⊗[ℕ] ℕ`. Its value at `1 ⊗ₜ 1` is the nonzero tensor
`(1 ⊗ₜ 1) ⊗ₜ (1 ⊗ₜ 1)`. This example uses modules over a semiring without
requiring additive groups.

For the zero boundary, the existing bottom subcomodule of a regular comodule
is tensored with another regular comodule. Its subtype and tensor domain are
subsingletons, so the raw map vanishes while retaining the same coassociativity
and inverse-right-unitor counit contracts.

The regular and bottom-subcomodule values come from AlgebraicGroups' specified
right-comodule API; their definitions do not use external tensor coaction laws.
Mathlib supplies the scalar and tensor coalgebras, bottom submodule and tensor
products.
-/

@[expose] public section

universe uR uC uD

open scoped TensorProduct

open Coalgebra (RightComodule)
open Coalgebra.RightComodule (externalTensorCoaction)

noncomputable section

namespace CoalgebraExternalTensorCoactionExamples

private abbrev regularLeft : RightComodule ℕ ℕ ℕ :=
  Coalgebra.RightComodule.regular ℕ ℕ

private abbrev regularRight : RightComodule ℕ ℕ ℕ :=
  Coalgebra.RightComodule.regular ℕ ℕ

private abbrev regularTensor :
    @RightComodule ℕ (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) _ _ _
      (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ) (B := ℕ)) _ _ :=
  @Coalgebra.RightComodule.regular ℕ (ℕ ⊗[ℕ] ℕ) _ _ _
    (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ) (B := ℕ))

private abbrev regularCoaction :
    ℕ ⊗[ℕ] ℕ →ₗ[ℕ] (ℕ ⊗[ℕ] ℕ) ⊗[ℕ] (ℕ ⊗[ℕ] ℕ) :=
  externalTensorCoaction regularLeft regularRight

/-- All four raw coaction contracts on the same regular semiring model,
together with its identification and nonzero input and output. -/
private theorem regular_semiring_contract :
    (∀ v w : ℕ, regularCoaction (v ⊗ₜ[ℕ] w) =
      TensorProduct.tensorTensorTensorComm ℕ ℕ ℕ ℕ ℕ
        (regularLeft.coaction v ⊗ₜ[ℕ] regularRight.coaction w)) ∧
    (TensorProduct.assoc ℕ (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ)).toLinearMap ∘ₗ
        regularCoaction.rTensor (ℕ ⊗[ℕ] ℕ) ∘ₗ regularCoaction =
      (((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ)
        (B := ℕ)).toCoalgebraStruct).comul).lTensor (ℕ ⊗[ℕ] ℕ) ∘ₗ
        regularCoaction ∧
    (((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ)
      (B := ℕ)).toCoalgebraStruct).counit).lTensor (ℕ ⊗[ℕ] ℕ) ∘ₗ
        regularCoaction =
      (TensorProduct.rid ℕ (ℕ ⊗[ℕ] ℕ)).symm.toLinearMap ∧
    regularCoaction = ((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ)
      (B := ℕ)).toCoalgebraStruct).comul ∧
    ((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ)
      (B := ℕ)).toCoalgebraStruct).comul = regularTensor.coaction ∧
    ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 ∧
    regularCoaction ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) =
      ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ⊗ₜ[ℕ] ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ∧
    regularCoaction ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 := by
  have hinput : ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 := by
    intro h
    have hzero : (1 : ℕ) = 0 := by
      simpa using congrArg (TensorProduct.rid ℕ ℕ) h
    exact Nat.one_ne_zero hzero
  have hfour :
      (((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ⊗ₜ[ℕ] ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) ≠ 0 := by
    intro h
    apply hinput
    have hunit : (TensorProduct.rid ℕ ℕ).toLinearMap
        ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 1 :=
      (TensorProduct.rid_tmul (R := ℕ) (1 : ℕ) (1 : ℕ)).trans (one_smul ℕ (1 : ℕ))
    have hone :
        TensorProduct.map (TensorProduct.rid ℕ ℕ).toLinearMap
          (TensorProduct.rid ℕ ℕ).toLinearMap
          (((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ⊗ₜ[ℕ] ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) =
          ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) :=
      (TensorProduct.map_tmul (TensorProduct.rid ℕ ℕ).toLinearMap
        (TensorProduct.rid ℕ ℕ).toLinearMap
        ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))).trans
        (congrArg₂ (TensorProduct.tmul ℕ) hunit hunit)
    have hzero :
        TensorProduct.map (TensorProduct.rid ℕ ℕ).toLinearMap
          (TensorProduct.rid ℕ ℕ).toLinearMap
          (0 : (ℕ ⊗[ℕ] ℕ) ⊗[ℕ] (ℕ ⊗[ℕ] ℕ)) = 0 :=
      LinearMap.map_zero _
    exact hone.symm.trans ((congrArg
      (TensorProduct.map (TensorProduct.rid ℕ ℕ).toLinearMap
        (TensorProduct.rid ℕ ℕ).toLinearMap) h).trans hzero)
  have hvalue : regularCoaction ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) =
      ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ⊗ₜ[ℕ] ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) := by
    have hleft : regularLeft.coaction (1 : ℕ) = (1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) :=
      (Coalgebra.RightComodule.regular_coaction (R := ℕ) (C := ℕ) 1).trans
        (CommSemiring.comul_apply ℕ 1)
    have hright : regularRight.coaction (1 : ℕ) = (1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) :=
      (Coalgebra.RightComodule.regular_coaction (R := ℕ) (C := ℕ) 1).trans
        (CommSemiring.comul_apply ℕ 1)
    calc
      _ = TensorProduct.tensorTensorTensorComm ℕ ℕ ℕ ℕ ℕ
          (regularLeft.coaction (1 : ℕ) ⊗ₜ[ℕ] regularRight.coaction (1 : ℕ)) :=
        Coalgebra.RightComodule.externalTensorCoaction_tmul regularLeft regularRight 1 1
      _ = TensorProduct.tensorTensorTensorComm ℕ ℕ ℕ ℕ ℕ
          (((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ⊗ₜ[ℕ] ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) :=
        congrArg (TensorProduct.tensorTensorTensorComm ℕ ℕ ℕ ℕ ℕ)
          (congrArg₂ (TensorProduct.tmul ℕ) hleft hright)
      _ = _ := TensorProduct.tensorTensorTensorComm_tmul
        (R := ℕ) (1 : ℕ) (1 : ℕ) (1 : ℕ) (1 : ℕ)
  refine ⟨?_, ?_, ?_, ?_, rfl, hinput, hvalue, ?_⟩
  · intro v w
    exact Coalgebra.RightComodule.externalTensorCoaction_tmul regularLeft regularRight v w
  · exact Coalgebra.RightComodule.externalTensorCoaction_coassoc regularLeft regularRight
  · exact Coalgebra.RightComodule.externalTensorCoaction_counit_comp regularLeft regularRight
  · exact Coalgebra.RightComodule.externalTensorCoaction_regular
  · exact fun h ↦ hfour (hvalue.symm.trans h)

private abbrev regularBottom (R : Type uR) (C : Type uC)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    (Coalgebra.RightComodule.regular R C).Subcomodule :=
  Coalgebra.RightComodule.Subcomodule.bot (Coalgebra.RightComodule.regular R C)

private abbrev bottomCoaction (R : Type uR) (C : Type uC) (D : Type uD)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D] :
    (regularBottom R C).toSubmodule ⊗[R] D →ₗ[R]
      ((regularBottom R C).toSubmodule ⊗[R] D) ⊗[R] (C ⊗[R] D) :=
  externalTensorCoaction (regularBottom R C).comodule (Coalgebra.RightComodule.regular R D)

/-- The bottom-subcomodule boundary has zero raw tensor coaction and satisfies
the same coassociativity and right counit contracts. -/
private theorem bottom_regular_contract {R : Type uR} {C : Type uC} {D : Type uD}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D] :
    Subsingleton (regularBottom R C).toSubmodule ∧
    (regularBottom R C).comodule.coaction = 0 ∧
    Subsingleton ((regularBottom R C).toSubmodule ⊗[R] D) ∧
    bottomCoaction R C D = 0 ∧
    (TensorProduct.assoc R ((regularBottom R C).toSubmodule ⊗[R] D)
        (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        (bottomCoaction R C D).rTensor (C ⊗[R] D) ∘ₗ bottomCoaction R C D =
      (Coalgebra.comul (R := R) (A := C ⊗[R] D)).lTensor
        ((regularBottom R C).toSubmodule ⊗[R] D) ∘ₗ bottomCoaction R C D ∧
    (Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor
        ((regularBottom R C).toSubmodule ⊗[R] D) ∘ₗ bottomCoaction R C D =
      (TensorProduct.rid R ((regularBottom R C).toSubmodule ⊗[R] D)).symm.toLinearMap := by
  have hbot : Subsingleton (regularBottom R C).toSubmodule := by
    change Subsingleton (⊥ : Submodule R C)
    infer_instance
  have htensor : Subsingleton ((regularBottom R C).toSubmodule ⊗[R] D) := by
    change Subsingleton ((⊥ : Submodule R C) ⊗[R] D)
    infer_instance
  refine ⟨hbot, rfl, htensor, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro t
    rw [htensor.elim t 0]
    have hleft : bottomCoaction R C D 0 = 0 := LinearMap.map_zero _
    have hright :
        (0 : (regularBottom R C).toSubmodule ⊗[R] D →ₗ[R]
          ((regularBottom R C).toSubmodule ⊗[R] D) ⊗[R] (C ⊗[R] D)) 0 = 0 :=
      LinearMap.zero_apply _
    exact hleft.trans hright.symm
  · apply LinearMap.ext
    intro t
    rw [htensor.elim t 0]
    have hleft :
        ((TensorProduct.assoc R ((regularBottom R C).toSubmodule ⊗[R] D)
            (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
          (bottomCoaction R C D).rTensor (C ⊗[R] D) ∘ₗ bottomCoaction R C D) 0 = 0 :=
      LinearMap.map_zero _
    have hright :
        ((Coalgebra.comul (R := R) (A := C ⊗[R] D)).lTensor
          ((regularBottom R C).toSubmodule ⊗[R] D) ∘ₗ bottomCoaction R C D) 0 = 0 :=
      LinearMap.map_zero _
    exact hleft.trans hright.symm
  · apply LinearMap.ext
    intro t
    rw [htensor.elim t 0]
    have hleft :
        ((Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor
          ((regularBottom R C).toSubmodule ⊗[R] D) ∘ₗ bottomCoaction R C D) 0 = 0 :=
      LinearMap.map_zero _
    have hright :
        (TensorProduct.rid R ((regularBottom R C).toSubmodule ⊗[R] D)).symm.toLinearMap
          0 = 0 := LinearMap.map_zero _
    exact hleft.trans hright.symm

end CoalgebraExternalTensorCoactionExamples

end
