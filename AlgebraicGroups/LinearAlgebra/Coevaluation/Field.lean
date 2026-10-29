/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.Coevaluation
public import Mathlib.LinearAlgebra.Coevaluation

/-!
# Compatibility with vector-space coevaluation

The finite-projective construction specializes to the existing coevaluation
of finite-dimensional vector spaces. The proof uses the existing tensor
triangle of Jakob von Raumer's construction, not a second basis computation.
-/

@[expose] public section

noncomputable section

namespace Module

open TensorProduct

universe u v

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The intrinsic construction agrees with the original Mathlib declaration. -/
theorem coevaluation_eq_mathlib :
    Module.coevaluation K V = _root_.coevaluation K V := by
  apply LinearMap.ext_ring
  rw [Module.coevaluation_apply_one]
  symm
  apply Module.coevaluationTensor_eq_of_contraction
  intro v
  have h := congrArg (TensorProduct.rid K V)
    (LinearMap.congr_fun (_root_.contractLeft_assoc_coevaluation' K V) (1 ⊗ₜ[K] v))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.rTensor_tmul, LinearMap.lTensor_def, TensorProduct.lid_tmul, one_smul,
    LinearEquiv.apply_symm_apply] using h

end Module
