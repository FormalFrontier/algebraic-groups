/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.CanonicalPointOperators
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Tactic.NormNum

/-!
# Linear maps failing the canonical point tests

The zero map on the nonzero rational module with coefficients in the monoid
bialgebra of the free monoid on two generators is not a counital coaction.
This uses a noncommutative coefficient bialgebra with its augmentation counit.
The canonical-point criterion detects this without assuming any coaction laws
on the given map. In particular, arbitrary linear maps are not silently replaced
by lawful coactions. A twice-scaled unit map also fails the coassociativity
test: its two sides have coefficients `2` and `4`.
-/

open scoped TensorProduct

example :
    ¬ (∀ (A : Type) [CommSemiring A] [Algebra ℚ A],
      TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (ℚ →ₗ[ℚ] A ⊗[ℚ] ℚ)
            ((TensorProduct.map
              (1 : WithConv (MonoidAlgebra ℚ (FreeMonoid (Fin 2)) →ₐ[ℚ] A)).ofConv.toLinearMap
              (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp
                (0 : ℚ →ₗ[ℚ] MonoidAlgebra ℚ (FreeMonoid (Fin 2)) ⊗[ℚ] ℚ))) =
        (LinearMap.id : A ⊗[ℚ] ℚ →ₗ[A] A ⊗[ℚ] ℚ)) := by
  intro h
  have hδ :=
    (TensorProduct.AlgebraTensorModule.counit_iff_forall_lift_toSpanSingleton_one
      (0 : ℚ →ₗ[ℚ] MonoidAlgebra ℚ (FreeMonoid (Fin 2)) ⊗[ℚ] ℚ)).mpr h
  have h1 := LinearMap.congr_fun hδ (1 : ℚ)
  simp at h1

/-- The canonical composition law detects a non-coassociative given map. -/
private theorem twice_unit_fails_composition :
    let δ : ℚ →ₗ[ℚ] ℚ ⊗[ℚ] ℚ := TensorProduct.mk ℚ ℚ ℚ (2 : ℚ)
    ¬ (∀ (A : Type) [CommSemiring A] [Algebra ℚ A]
        (α β : ℚ →ₐ[ℚ] A),
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton A (ℚ →ₗ[ℚ] A ⊗[ℚ] ℚ)
          ((TensorProduct.map β.toLinearMap
            (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp δ))).comp
        (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (ℚ →ₗ[ℚ] A ⊗[ℚ] ℚ)
            ((TensorProduct.map α.toLinearMap
              (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp δ))) =
      TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton A (ℚ →ₗ[ℚ] A ⊗[ℚ] ℚ)
          ((TensorProduct.map
            (WithConv.toConv α * WithConv.toConv β).ofConv.toLinearMap
            (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp δ))) := by
  dsimp only
  intro h
  let δ : ℚ →ₗ[ℚ] ℚ ⊗[ℚ] ℚ := TensorProduct.mk ℚ ℚ ℚ (2 : ℚ)
  have hδ :=
    (TensorProduct.AlgebraTensorModule.coassoc_iff_forall_lift_toSpanSingleton_comp_map
      δ).mpr h
  have h1 := congrArg
    (fun z : (ℚ ⊗[ℚ] ℚ) ⊗[ℚ] ℚ =>
      (TensorProduct.lid ℚ ℚ)
        ((TensorProduct.lid ℚ (ℚ ⊗[ℚ] ℚ)) ((TensorProduct.assoc ℚ ℚ ℚ ℚ) z)))
    (LinearMap.congr_fun hδ (1 : ℚ))
  norm_num [δ, LinearMap.comp_apply, TensorProduct.map_tmul,
    Bialgebra.comulAlgHom_apply, CommSemiring.comul_apply,
    TensorProduct.assoc_symm_tmul, TensorProduct.assoc_tmul,
    TensorProduct.lid_tmul] at h1
