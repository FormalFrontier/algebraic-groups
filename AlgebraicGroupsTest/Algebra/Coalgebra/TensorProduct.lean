/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.TensorProduct

/-!
# A fixed-data semiring witness for weak tensor maps

On the ordinary `ℕ`-module `ℕ`, choose zero comultiplication and zero counit.
Doubling and the identity preserve these weak data. Their tensor map takes
`1 ⊗ₜ 1` to `2 ⊗ₜ 1`; Mathlib's ordinary linear left unitor detects that the
input and output are nonzero and different.

The same fixed data fail the left counit law at `1`. This is not a claim that
`ℕ` admits no full coalgebra: its stock scalar coalgebra has different data.
The local tensor dictionary below is Mathlib's canonical weak tensor structure,
formed from the selected zero data, not from a full coalgebra instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

noncomputable section

namespace CoalgebraTensorMapTest

/-- The one primitive weak-data fixture, shared by all four factor endpoints. -/
@[instance_reducible]
def zeroData : CoalgebraStruct ℕ ℕ where
  comul := 0
  counit := 0

attribute [local instance] zeroData

/-- Fix the two tensor endpoints to the canonical structure on these zero data. -/
local instance canonicalTensorData : CoalgebraStruct ℕ (ℕ ⊗[ℕ] ℕ) :=
  TensorProduct.instCoalgebraStruct (R := ℕ) (S := ℕ) (A := ℕ) (B := ℕ)

/-- Doubling preserves the selected zero comultiplication and counit. -/
def twice : ℕ →ₗc[ℕ] ℕ where
  toLinearMap := (2 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ)
  counit_comp := by
    change (0 : ℕ →ₗ[ℕ] ℕ) ∘ₗ _ = 0
    simp only [LinearMap.zero_comp]
  map_comp_comul := by
    apply LinearMap.ext
    intro n
    change TensorProduct.map
      ((2 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ))
      ((2 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ)) (0 : ℕ ⊗[ℕ] ℕ) = 0
    exact (TensorProduct.map
      ((2 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ))
      ((2 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ))).map_zero

/-- The actual weak tensor-map API applied to doubling and the weak identity. -/
def tensorMap : ℕ ⊗[ℕ] ℕ →ₗc[ℕ] ℕ ⊗[ℕ] ℕ :=
  TensorProduct.mapCoalgHom twice (CoalgHom.id ℕ ℕ)

/-- One nontrivial tensor-map witness together with failure of the fixed-data counit law. -/
theorem zero_data_semiring_witness :
    tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = (2 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) ∧
    TensorProduct.lid ℕ ℕ ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 1 ∧
    TensorProduct.lid ℕ ℕ (tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) = 2 ∧
    ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 ∧
    tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 ∧
    tensorMap.toLinearMap ≠ 0 ∧
    tensorMap ≠ CoalgHom.id ℕ (ℕ ⊗[ℕ] ℕ) ∧
    zeroData.counit.rTensor ℕ ∘ₗ zeroData.comul ≠ TensorProduct.mk ℕ ℕ ℕ 1 := by
  have htmul :
      tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = (2 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) := by
    calc
      tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) =
          twice 1 ⊗ₜ[ℕ] (CoalgHom.id ℕ ℕ) 1 :=
        TensorProduct.mapCoalgHom_tmul twice (CoalgHom.id ℕ ℕ) 1 1
      _ = (2 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) := by simp [twice]
  have hinput : TensorProduct.lid ℕ ℕ ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 1 := by
    simp
  have houtput :
      TensorProduct.lid ℕ ℕ (tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) = 2 := by
    rw [htmul]
    simp
  have hinput_ne : ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 := by
    intro h
    have h10 : (1 : ℕ) = 0 := by
      simpa only [hinput, map_zero] using congrArg (TensorProduct.lid ℕ ℕ) h
    exact (by decide : (1 : ℕ) ≠ 0) h10
  have houtput_ne : tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 := by
    intro h
    have h20 : (2 : ℕ) = 0 := by
      simpa only [houtput, map_zero] using congrArg (TensorProduct.lid ℕ ℕ) h
    exact (by decide : (2 : ℕ) ≠ 0) h20
  refine ⟨htmul, hinput, houtput, hinput_ne, houtput_ne, ?_, ?_, ?_⟩
  · intro hzero
    apply houtput_ne
    exact LinearMap.congr_fun hzero ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))
  · intro hid
    have heq : tensorMap ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = (1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) :=
      CoalgHom.congr_fun hid ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))
    have h21 : (2 : ℕ) = 1 := by
      simpa only [houtput, hinput] using congrArg (TensorProduct.lid ℕ ℕ) heq
    exact (by decide : (2 : ℕ) ≠ 1) h21
  · intro hcounit
    have h01 : (0 : ℕ) = 1 := by
      have hat := LinearMap.congr_fun hcounit (1 : ℕ)
      change (0 : ℕ →ₗ[ℕ] ℕ).rTensor ℕ
          ((0 : ℕ →ₗ[ℕ] ℕ ⊗[ℕ] ℕ) (1 : ℕ)) =
        (1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) at hat
      rw [LinearMap.zero_apply, map_zero] at hat
      simpa only [map_zero, TensorProduct.lid_tmul, one_smul] using
        congrArg (TensorProduct.lid ℕ ℕ) hat
    exact zero_ne_one h01

end CoalgebraTensorMapTest

end
