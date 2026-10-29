/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Coefficient operators and scalar transport

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

Coefficient transport is also tested along the noninjective evaluation-at-two
map from `ℕ[Multiplicative ℕ]` to `ℕ`. The generator and the constant two have
the same image, while their tensor-extended operator has transported value
`4 ⊗ₜ 1`, nonzero by the left unitor. Transport of the matrix coefficient operator
to `ULift` preserves the value `E₁₁ ⊗ₜ 1`, with the lift universe independent of
the original matrix and scalar universes.

## References

Mathlib's scalar coalgebra is by Ali Ramsey and Eric Wieser; its tensor scalar
extension and unitor APIs are by Kim Morrison, Johan Commelin and Eric Wieser.
The matrix-unit API is by Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash
and Wen Yang. The coefficient-composition theorem is an AlgebraicGroups
construction by Formal Frontier Agents. Mathlib also supplies the monoid-algebra
lifting, `powersHom` and `ULift` algebra-equivalence APIs used in the transport
examples.
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

-- Evaluation at two is genuinely noninjective, and both routes through the
-- tensor-extension square give the same nonzero tensor with the original Nat actions.
example :
    let A := MonoidAlgebra ℕ (Multiplicative ℕ)
    let φ : A →ₐ[ℕ] ℕ :=
      MonoidAlgebra.lift ℕ ℕ (Multiplicative ℕ) (powersHom ℕ 2)
    let X : A := MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
    let c : A := MonoidAlgebra.single (1 : Multiplicative ℕ) 2
    let F : ℕ →ₗ[ℕ] A ⊗[ℕ] ℕ := TensorProduct.mk ℕ A ℕ X
    let P := TensorProduct.map φ.toLinearMap (LinearMap.id : ℕ →ₗ[ℕ] ℕ)
    let T := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton A (ℕ →ₗ[ℕ] A ⊗[ℕ] ℕ) F)
    let T' := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton ℕ (ℕ →ₗ[ℕ] ℕ ⊗[ℕ] ℕ) (P.comp F))
    X ≠ c ∧ φ X = 2 ∧ φ c = 2 ∧ ¬ Function.Injective φ ∧
      P (T (X ⊗ₜ[ℕ] 1)) = (4 : ℕ) ⊗ₜ[ℕ] 1 ∧
      T' (P (X ⊗ₜ[ℕ] 1)) = (4 : ℕ) ⊗ₜ[ℕ] 1 ∧
      ((4 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) : ℕ ⊗[ℕ] ℕ) ≠ 0 := by
  intro A φ X c F P T T'
  have hne : X ≠ c := by
    intro h
    have hcoeff := congrArg
      (fun f : MonoidAlgebra ℕ (Multiplicative ℕ) =>
        f.coeff (Multiplicative.ofAdd 1)) h
    simp [X, c] at hcoeff
  have hφX : φ X = 2 := by
    exact (MonoidAlgebra.lift_single (R := ℕ) (A := ℕ)
      (powersHom ℕ 2) (Multiplicative.ofAdd 1) 1).trans (by rfl)
  have hφc : φ c = 2 := by
    exact (MonoidAlgebra.lift_single (R := ℕ) (A := ℕ)
      (powersHom ℕ 2) (1 : Multiplicative ℕ) 2).trans (by rfl)
  have hnoninj : ¬ Function.Injective φ := by
    intro h
    exact hne (h (hφX.trans hφc.symm))
  have hPX : P (X ⊗ₜ[ℕ] 1) = (2 : ℕ) ⊗ₜ[ℕ] 1 := by
    dsimp only [P]
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hφX]
  have hright : T' (P (X ⊗ₜ[ℕ] 1)) = (4 : ℕ) ⊗ₜ[ℕ] 1 := by
    rw [hPX]
    dsimp only [T']
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    -- Expose the rank-one map with the given Nat module structures before rewriting.
    change (2 : ℕ) • P (F 1) = (4 : ℕ) ⊗ₜ[ℕ] 1
    rw [show F 1 = X ⊗ₜ[ℕ] 1 from rfl, hPX,
      TensorProduct.smul_tmul', smul_eq_mul]
  have htransport : P (T (X ⊗ₜ[ℕ] 1)) = T' (P (X ⊗ₜ[ℕ] 1)) :=
    TensorProduct.AlgebraTensorModule.map_lift_toSpanSingleton_apply φ F (X ⊗ₜ[ℕ] 1)
  refine ⟨hne, hφX, hφc, hnoninj, htransport.trans hright, hright, ?_⟩
  intro h
  have h4 : (4 : ℕ) = 0 := by
    simpa only [TensorProduct.lid_tmul, smul_eq_mul, mul_one, map_zero] using
      congrArg (TensorProduct.lid ℕ ℕ) h
  exact (by decide : (4 : ℕ) ≠ 0) h4

universe u

-- Reuse the original lower-coefficient operator: E12 * E21 = E11 before and
-- after transport to an independently lifted coefficient universe.
example :
    let e : Mat₂ ≃ₐ[ℕ] ULift.{u} Mat₂ :=
      (ULift.algEquiv (R := ℕ) (A := Mat₂)).symm
    let F : ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ :=
      (TensorProduct.map lowerCoefficient (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp scalarComul
    let P := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℕ ℕ)
    let T := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton Mat₂ (ℕ →ₗ[ℕ] Mat₂ ⊗[ℕ] ℕ) F)
    let T' := TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton (ULift.{u} Mat₂)
        (ℕ →ₗ[ℕ] ULift.{u} Mat₂ ⊗[ℕ] ℕ) (P.toLinearMap.comp F))
    P (T ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)) =
        (ULift.up (Matrix.single (0 : Fin 2) 0 1 : Mat₂) : ULift.{u} Mat₂) ⊗ₜ[ℕ] 1 ∧
      T' (P ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)) =
        (ULift.up (Matrix.single (0 : Fin 2) 0 1 : Mat₂) : ULift.{u} Mat₂) ⊗ₜ[ℕ] 1 := by
  intro e F P T T'
  have hT : T ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1) =
      (Matrix.single (0 : Fin 2) 0 1 : Mat₂) ⊗ₜ[ℕ] 1 := by
    dsimp only [T, F]
    rw [lift_comul_tmul_one]
    change ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) * Matrix.single 1 0 1) ⊗ₜ[ℕ] 1 =
      (Matrix.single (0 : Fin 2) 0 1 : Mat₂) ⊗ₜ[ℕ] 1
    simp only [Matrix.single_mul_single_same, one_mul]
  have hP : P (T ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)) =
      (ULift.up (Matrix.single (0 : Fin 2) 0 1 : Mat₂) : ULift.{u} Mat₂) ⊗ₜ[ℕ] 1 := by
    rw [hT]
    dsimp only [P]
    rw [TensorProduct.congr_tmul]
    rfl
  refine ⟨hP, ?_⟩
  have htransport :
      P (T ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)) =
        T' (P ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)) :=
    LinearMap.congr_fun
      (TensorProduct.AlgebraTensorModule.congr_comp_lift_toSpanSingleton e F)
      ((Matrix.single (0 : Fin 2) 1 1 : Mat₂) ⊗ₜ[ℕ] 1)
  exact htransport.symm.trans hP
