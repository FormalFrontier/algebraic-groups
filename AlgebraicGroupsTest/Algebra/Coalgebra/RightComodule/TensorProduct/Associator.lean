/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Associator

/-!
# A nonidentity naturality client over the natural numbers

Reassociation commutes with scaling the three regular scalar comodules by
2, 3 and 5. The resulting map sends the tensor of three ones to a tensor
whose scalar readout is 30, whereas the unscaled associator has readout 1.
This uses the associator through its characteristic and naturality API.
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra (RightComoduleHom)
open Coalgebra.RightComodule

noncomputable section

namespace CoalgebraExternalTensorAssociatorExamples

private abbrev A := regular ℕ ℕ
private abbrev assoc := externalTensorAssocHom A A A
private abbrev coeff := (Coalgebra.TensorProduct.assoc ℕ ℕ ℕ ℕ ℕ).toCoalgHom
private abbrev twice := (2 : ℕ) • RightComoduleHom.id A
private abbrev thrice := (3 : ℕ) • RightComoduleHom.id A
private abbrev fivefold := (5 : ℕ) • RightComoduleHom.id A
private abbrev leftScale := (twice.externalTensor thrice).externalTensor fivefold
private abbrev rightScale := twice.externalTensor (thrice.externalTensor fivefold)
-- Construct over general scalars so specialization retains the tensor module instances.
private abbrev input (R : Type*) [CommSemiring R] : (R ⊗[R] R) ⊗[R] R :=
  ((1 : R) ⊗ₜ[R] (1 : R)) ⊗ₜ[R] (1 : R)

private def readout (R : Type*) [CommSemiring R] : R ⊗[R] (R ⊗[R] R) →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.lid R R).toLinearMap

private theorem readout_tmul (R : Type*) [CommSemiring R] (a b c : R) :
    readout R (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = a * (b * c) := by
  simp only [readout, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul]

namespace Scalar

private abbrev A (R : Type*) [CommSemiring R] := regular R R
private abbrev assoc (R : Type*) [CommSemiring R] :=
  externalTensorAssocHom (A R) (A R) (A R)
private abbrev coeff (R : Type*) [CommSemiring R] :=
  (Coalgebra.TensorProduct.assoc R R R R R).toCoalgHom
private abbrev twice (R : Type*) [CommSemiring R] := (2 : R) • RightComoduleHom.id (A R)
private abbrev thrice (R : Type*) [CommSemiring R] := (3 : R) • RightComoduleHom.id (A R)
private abbrev fivefold (R : Type*) [CommSemiring R] := (5 : R) • RightComoduleHom.id (A R)
private abbrev leftScale (R : Type*) [CommSemiring R] :=
  ((twice R).externalTensor (thrice R)).externalTensor (fivefold R)
private abbrev rightScale (R : Type*) [CommSemiring R] :=
  (twice R).externalTensor ((thrice R).externalTensor (fivefold R))

private theorem scaled_associator_equalities (R : Type*) [CommSemiring R] :
    (rightScale R).comp (assoc R) =
        (assoc R).comp ((leftScale R).mapCoalgebra (coeff R)) ∧
      rightScale R (assoc R (input R)) = (2 : R) ⊗ₜ[R] ((3 : R) ⊗ₜ[R] (5 : R)) ∧
      readout R (rightScale R (assoc R (input R))) = 30 ∧
      readout R (assoc R (input R)) = 1 := by
  have hvalue : rightScale R (assoc R (input R)) =
      (2 : R) ⊗ₜ[R] ((3 : R) ⊗ₜ[R] (5 : R)) := by
    rw [externalTensorAssocHom_tmul, RightComoduleHom.externalTensor_tmul,
      RightComoduleHom.externalTensor_tmul]
    change ((2 : R) * 1) ⊗ₜ[R] (((3 : R) * 1) ⊗ₜ[R] ((5 : R) * 1)) = _
    simp only [mul_one]
  refine ⟨externalTensorAssocHom_naturality (twice R) (thrice R) (fivefold R),
    hvalue, ?_, ?_⟩
  · rw [hvalue, readout_tmul]
    have h := congrArg (fun n : ℕ => (n : R)) (show (2 : ℕ) * (3 * 5) = 30 from rfl)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  · simp only [input, externalTensorAssocHom_tmul, readout_tmul, mul_one]

private theorem scaled_associator_eq_readout (R : Type*) [CommSemiring R]
    (heq : (rightScale R).comp (assoc R) = assoc R) : (30 : R) = 1 := by
  have heval := congrArg
    (fun k : RightComoduleHom
        ((((A R).externalTensor (A R)).externalTensor (A R)).mapCoalgebra (coeff R))
        ((A R).externalTensor ((A R).externalTensor (A R))) =>
      readout R (k (input R))) heq
  simp only [RightComoduleHom.comp_apply] at heval
  have h := scaled_associator_equalities R
  exact h.2.2.1.symm.trans (heval.trans h.2.2.2)

end Scalar

/-- Naturality gives the two scaling paths, and this is not the unscaled associator. -/
private theorem scaled_associator_contract :
    rightScale.comp assoc = assoc.comp (leftScale.mapCoalgebra coeff) ∧
      rightScale (assoc (input ℕ)) = (2 : ℕ) ⊗ₜ[ℕ] ((3 : ℕ) ⊗ₜ[ℕ] (5 : ℕ)) ∧
      rightScale.comp assoc ≠ assoc := by
  -- These expected types check specialization against the original Nat maps.
  have hnatural : rightScale.comp assoc = assoc.comp (leftScale.mapCoalgebra coeff) :=
    (Scalar.scaled_associator_equalities ℕ).1
  have hvalue : rightScale (assoc (input ℕ)) =
      (2 : ℕ) ⊗ₜ[ℕ] ((3 : ℕ) ⊗ₜ[ℕ] (5 : ℕ)) :=
    (Scalar.scaled_associator_equalities ℕ).2.1
  have hseparate : rightScale.comp assoc = assoc → (30 : ℕ) = 1 :=
    Scalar.scaled_associator_eq_readout ℕ
  refine ⟨hnatural, hvalue, ?_⟩
  intro heq
  exact (by decide : (30 : ℕ) ≠ 1) (hseparate heq)

end CoalgebraExternalTensorAssociatorExamples

end
