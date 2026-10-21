/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Matrix-valued coefficients on the scalar coalgebra

For the canonical scalar comultiplication on `ℕ`, the linear coefficient maps
`n ↦ n E₁₂` and `n ↦ n E₂₁` give right multiplication by the two matrix units
under the `Matrix (Fin 2) (Fin 2) ℕ`-linear tensor right unitor. Applying the
second operator after the first gives `E₁₁`; reversing them gives `E₂₂`.
Thus the coefficient algebra need not be commutative, and the order matters.
The coefficient maps are linear maps, not algebra homomorphisms.

The relative coassociativity hypothesis is proved for the given scalar
comultiplication. It is what permits reassociating the two successive
applications; arbitrary linear coaction data need not satisfy it. This scalar
coalgebra is cocommutative, so the example tests noncommutativity of the
coefficient algebra, not noncocommutativity of the coefficient coalgebra.

The constructions used here are Mathlib's tensor extension, scalar coalgebra,
matrix units and tensor unitor; no action on the original scalar module by the
matrix algebra is required.

## References

Mathlib's scalar coalgebra is by Ali Ramsey and Eric Wieser; its tensor scalar
extension and unitor APIs are by Kim Morrison, Johan Commelin and Eric Wieser.
The matrix-unit API is by Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash
and Wen Yang. The coefficient-composition theorem is an AlgebraicGroups
construction by Formal Frontier Agents.
-/

open scoped TensorProduct

private abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℕ

private abbrev scalarComul : ℕ →ₗ[ℕ] ℕ ⊗[ℕ] ℕ :=
  Coalgebra.comul (R := ℕ) (A := ℕ)

private abbrev upperCoefficient : ℕ →ₗ[ℕ] Mat₂ :=
  Matrix.singleLinearMap ℕ (0 : Fin 2) (1 : Fin 2)

private abbrev lowerCoefficient : ℕ →ₗ[ℕ] Mat₂ :=
  Matrix.singleLinearMap ℕ (1 : Fin 2) (0 : Fin 2)

private theorem scalarComul_coassoc :
    (TensorProduct.map scalarComul (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul =
      (TensorProduct.assoc ℕ ℕ ℕ ℕ).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : ℕ →ₗ[ℕ] ℕ) scalarComul).comp scalarComul) := by
  apply LinearMap.ext
  intro n
  change
    TensorProduct.map scalarComul (LinearMap.id : ℕ →ₗ[ℕ] ℕ) (scalarComul n) =
      (TensorProduct.assoc ℕ ℕ ℕ ℕ).symm
        (TensorProduct.map (LinearMap.id : ℕ →ₗ[ℕ] ℕ) scalarComul (scalarComul n))
  exact (Coalgebra.coassoc_symm_apply (R := ℕ) (A := ℕ) n).symm

example :
    (TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map lowerCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))).comp
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
          ((TensorProduct.map upperCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))) =
      TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
          ((TensorProduct.map
            ((LinearMap.mul' ℕ Mat₂).comp
              ((TensorProduct.map upperCoefficient lowerCoefficient).comp scalarComul))
            (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul)) := by
  exact TensorProduct.AlgebraTensorModule.lift_toSpanSingleton_comp_map_of_coassoc
    (R := ℕ) (C := ℕ) (M := ℕ) (A := Mat₂)
    scalarComul scalarComul upperCoefficient lowerCoefficient scalarComul_coassoc

private theorem lift_comul_tmul_one (γ : ℕ →ₗ[ℕ] Mat₂) (a : Mat₂) :
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map γ (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))
      (a ⊗ₜ[ℕ] 1) = (a * γ 1) ⊗ₜ[ℕ] 1 := by
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  -- Expose the rank-one map before evaluating the scalar comultiplication.
  change a • (TensorProduct.map γ (LinearMap.id : ℕ →ₗ[ℕ] ℕ) (scalarComul 1)) =
    (a * γ 1) ⊗ₜ[ℕ] 1
  rw [show scalarComul 1 = (1 : ℕ) ⊗ₜ[ℕ] 1 from
    CommSemiring.comul_apply (R := ℕ) 1,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul]

example (a : Mat₂) :
    let ρ := TensorProduct.AlgebraTensorModule.rid ℕ Mat₂ Mat₂
    ρ (TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map upperCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))
      (ρ.symm a)) = a * Matrix.single (0 : Fin 2) (1 : Fin 2) 1 ∧
    ρ (TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map lowerCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))
      (ρ.symm a)) = a * Matrix.single (1 : Fin 2) (0 : Fin 2) 1 := by
  dsimp only
  constructor <;>
    rw [TensorProduct.AlgebraTensorModule.rid_symm_apply, lift_comul_tmul_one,
      TensorProduct.AlgebraTensorModule.rid_tmul, one_smul] <;> rfl

example :
    let Tα := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map upperCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))
    let Tβ := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ)
        ((TensorProduct.map lowerCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul))
    let ρ := TensorProduct.AlgebraTensorModule.rid ℕ Mat₂ Mat₂
    ρ (Tβ (Tα (ρ.symm 1))) = Matrix.single (0 : Fin 2) (0 : Fin 2) 1 ∧
      ρ (Tα (Tβ (ρ.symm 1))) = Matrix.single (1 : Fin 2) (1 : Fin 2) 1 ∧
      Tβ.comp Tα ≠ Tα.comp Tβ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [TensorProduct.AlgebraTensorModule.rid_symm_apply,
      lift_comul_tmul_one upperCoefficient, lift_comul_tmul_one lowerCoefficient,
      TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
    change (1 : Mat₂) * Matrix.single 0 1 1 * Matrix.single 1 0 1 =
      Matrix.single 0 0 1
    simp only [one_mul, Matrix.single_mul_single_same]
  · rw [TensorProduct.AlgebraTensorModule.rid_symm_apply,
      lift_comul_tmul_one lowerCoefficient, lift_comul_tmul_one upperCoefficient,
      TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
    change (1 : Mat₂) * Matrix.single 1 0 1 * Matrix.single 0 1 1 =
      Matrix.single 1 1 1
    simp only [one_mul, Matrix.single_mul_single_same]
  · intro h
    have h00 := congrArg
      (fun f : Mat₂ ⊗[ℕ] ℕ →ₗ[Mat₂] Mat₂ ⊗[ℕ] ℕ =>
        (TensorProduct.AlgebraTensorModule.rid ℕ Mat₂ Mat₂
          (f ((1 : Mat₂) ⊗ₜ[ℕ] (1 : ℕ)))) (0 : Fin 2) (0 : Fin 2)) h
    simp only [LinearMap.comp_apply, lift_comul_tmul_one,
      TensorProduct.AlgebraTensorModule.rid_tmul, one_smul] at h00
    change ((1 : Mat₂) * Matrix.single 0 1 1 * Matrix.single 1 0 1 : Mat₂) 0 0 =
      ((1 : Mat₂) * Matrix.single 1 0 1 * Matrix.single 0 1 1 : Mat₂) 0 0 at h00
    simp only [one_mul, Matrix.single_mul_single_same] at h00
    change (1 : ℕ) = 0 at h00
    cases h00
