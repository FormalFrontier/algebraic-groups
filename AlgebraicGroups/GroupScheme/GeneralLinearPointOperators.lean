/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators
public import AlgebraicGroups.GroupScheme.GeneralLinear
import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.Tactic.NormNum

/-!
# Ordered coefficient operators of general-linear points

For the regular left coaction of the general-linear coordinate coalgebra,
applying the point operator for `h` after that for `g` corresponds to the matrix
product `g * h`. The operators are Mathlib's tensor extensions of the displayed
first-factor coefficient maps; no additional action is introduced.

The counit readback retains both the left unitor and its inverse. Over `ℚ`,
two different product entries distinguish the raw lifted endomorphisms for
arbitrary supplied points, not only their conjugates by the unitor.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8: the ordered matrix
  coproduct on the general-linear coordinate ring.
* Mathlib, `RingTheory/Bialgebra/Convolution`, `RingTheory/Coalgebra/Convolution`
  and `LinearAlgebra/TensorProduct`: convolution, its right unit and unitors.
* The general-linear coordinate-ring formalization and its rational unipotent
  point-operator calculation: first-factor contraction and counit recovery.
-/

@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Reading the operator for `h` after that for `g` through the registered counit
and both left unitors gives the coordinate evaluation at `g * h`. This is the
left-coaction order. The supplied map is identified with the registered
comultiplication by the given equality. -/
theorem generalLinearGroupMulEquivAlgHom_counit_lift_comp_apply
    (g h : Matrix.GeneralLinearGroup n K)
    (δ : CoordinateRing K n →ₗ[K] CoordinateRing K n ⊗[K] CoordinateRing K n)
    (hδ : δ = (Bialgebra.comulAlgHom K (CoordinateRing K n)).toLinearMap)
    (c : CoordinateRing K n) :
    ((Bialgebra.counitAlgHom K (CoordinateRing K n)).toLinearMap.comp
      ((TensorProduct.lid K (CoordinateRing K n)).toLinearMap.comp
        (((TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton K
            (CoordinateRing K n →ₗ[K] K ⊗[K] CoordinateRing K n)
            ((TensorProduct.map
              (generalLinearGroupMulEquivAlgHom K n K h).ofConv.toLinearMap
              (LinearMap.id : CoordinateRing K n →ₗ[K] CoordinateRing K n)).comp
                δ))).comp
          (TensorProduct.AlgebraTensorModule.lift
            (LinearMap.toSpanSingleton K
              (CoordinateRing K n →ₗ[K] K ⊗[K] CoordinateRing K n)
              ((TensorProduct.map
                (generalLinearGroupMulEquivAlgHom K n K g).ofConv.toLinearMap
                (LinearMap.id : CoordinateRing K n →ₗ[K] CoordinateRing K n)).comp
                  δ)))).comp
          (TensorProduct.lid K (CoordinateRing K n)).symm.toLinearMap))) c =
      (generalLinearGroupMulEquivAlgHom K n K (g * h)).ofConv c := by
  subst δ
  have hCoefficient :
      (generalLinearGroupMulEquivAlgHom K n K (g * h)).ofConv.toLinearMap =
        (WithConv.toConv
            (generalLinearGroupMulEquivAlgHom K n K g).ofConv.toLinearMap *
          WithConv.toConv
            (generalLinearGroupMulEquivAlgHom K n K h).ofConv.toLinearMap).ofConv := by
    calc
      _ = (generalLinearGroupMulEquivAlgHom K n K g *
          generalLinearGroupMulEquivAlgHom K n K h).ofConv.toLinearMap :=
        congrArg (fun p : WithConv (CoordinateRing K n →ₐ[K] K) =>
          p.ofConv.toLinearMap) ((generalLinearGroupMulEquivAlgHom K n K).map_mul g h)
      _ = _ := congrArg WithConv.ofConv
        (AlgHom.toLinearMap_convMul
          (generalLinearGroupMulEquivAlgHom K n K g)
          (generalLinearGroupMulEquivAlgHom K n K h))
  calc
    _ = (WithConv.toConv
          (generalLinearGroupMulEquivAlgHom K n K g).ofConv.toLinearMap *
        WithConv.toConv
          (generalLinearGroupMulEquivAlgHom K n K h).ofConv.toLinearMap).ofConv c := by
      simpa only [Bialgebra.toLinearMap_comulAlgHom,
        Bialgebra.toLinearMap_counitAlgHom, WithConv.ofConv_toConv] using
        LinearMap.congr_fun
          (TensorProduct.AlgebraTensorModule.counit_comp_lid_comp_lift_toSpanSingleton_comp_comul
            (WithConv.toConv
              (generalLinearGroupMulEquivAlgHom K n K g).ofConv.toLinearMap)
            (WithConv.toConv
              (generalLinearGroupMulEquivAlgHom K n K h).ofConv.toLinearMap)) c
    _ = _ := LinearMap.congr_fun hCoefficient.symm c

end AlgebraicGeometry

namespace GeneralLinearCoordinateRing

/-- For arbitrary rational `GL₂` points with the two specified product entries,
the registered-counit readbacks of the two raw operator compositions are `2` and
`1`. In particular, `β` after `α` reads the entry of `U * V`. -/
theorem rational_point_operator_counit_values :
    (∀ (U V : Matrix.GeneralLinearGroup (Fin 2) ℚ),
    (U * V) (0 : Fin 2) (0 : Fin 2) = 2 →
    (V * U) (0 : Fin 2) (0 : Fin 2) = 1 →
    let C := GeneralLinearCoordinateRing.CoordinateRing ℚ (Fin 2)
    let α : C →ₐ[ℚ] ℚ :=
      (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom ℚ (Fin 2) ℚ U).ofConv
    let β : C →ₐ[ℚ] ℚ :=
      (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom ℚ (Fin 2) ℚ V).ofConv
    ∀ (δ : C →ₗ[ℚ] C ⊗[ℚ] C),
      δ = (Bialgebra.comulAlgHom ℚ C).toLinearMap →
      ((Bialgebra.counitAlgHom ℚ C).toLinearMap.comp
        ((TensorProduct.lid ℚ C).toLinearMap.comp
          (((TensorProduct.AlgebraTensorModule.lift
            (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
              ((TensorProduct.map β.toLinearMap
                (LinearMap.id : C →ₗ[ℚ] C)).comp δ))).comp
            (TensorProduct.AlgebraTensorModule.lift
              (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
                ((TensorProduct.map α.toLinearMap
                  (LinearMap.id : C →ₗ[ℚ] C)).comp δ)))).comp
            (TensorProduct.lid ℚ C).symm.toLinearMap)))
        (GeneralLinearCoordinateRing.matrix ℚ (Fin 2) 0 0) = 2 ∧
      ((Bialgebra.counitAlgHom ℚ C).toLinearMap.comp
        ((TensorProduct.lid ℚ C).toLinearMap.comp
          (((TensorProduct.AlgebraTensorModule.lift
            (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
              ((TensorProduct.map α.toLinearMap
                (LinearMap.id : C →ₗ[ℚ] C)).comp δ))).comp
            (TensorProduct.AlgebraTensorModule.lift
              (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
                ((TensorProduct.map β.toLinearMap
                  (LinearMap.id : C →ₗ[ℚ] C)).comp δ)))).comp
            (TensorProduct.lid ℚ C).symm.toLinearMap)))
        (GeneralLinearCoordinateRing.matrix ℚ (Fin 2) 0 0) = 1) := by
  intro U V hUV hVU
  dsimp only
  intro δ hδ
  constructor
  · exact (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom_counit_lift_comp_apply
      ℚ (Fin 2) U V δ hδ (matrix ℚ (Fin 2) 0 0)).trans
        ((AlgebraicGeometry.generalLinearGroupMulEquivAlgHom_apply_matrix
          ℚ (Fin 2) ℚ (U * V) 0 0).trans hUV)
  · exact (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom_counit_lift_comp_apply
      ℚ (Fin 2) V U δ hδ (matrix ℚ (Fin 2) 0 0)).trans
        ((AlgebraicGeometry.generalLinearGroupMulEquivAlgHom_apply_matrix
          ℚ (Fin 2) ℚ (V * U) 0 0).trans hVU)

/-- Rational `GL₂` points whose ordered product entries are `2` and `1` give
different raw tensor-extended coefficient-operator compositions. The supplied
map and its equality to the registered comultiplication are retained. -/
theorem rational_point_operators_comp_ne :
    (∀ (U V : Matrix.GeneralLinearGroup (Fin 2) ℚ),
    (U * V) (0 : Fin 2) (0 : Fin 2) = 2 →
    (V * U) (0 : Fin 2) (0 : Fin 2) = 1 →
    let C := GeneralLinearCoordinateRing.CoordinateRing ℚ (Fin 2)
    let α : C →ₐ[ℚ] ℚ :=
      (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom ℚ (Fin 2) ℚ U).ofConv
    let β : C →ₐ[ℚ] ℚ :=
      (AlgebraicGeometry.generalLinearGroupMulEquivAlgHom ℚ (Fin 2) ℚ V).ofConv
    ∀ (δ : C →ₗ[ℚ] C ⊗[ℚ] C),
      δ = (Bialgebra.comulAlgHom ℚ C).toLinearMap →
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
          ((TensorProduct.map β.toLinearMap
            (LinearMap.id : C →ₗ[ℚ] C)).comp δ))).comp
        (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
            ((TensorProduct.map α.toLinearMap
              (LinearMap.id : C →ₗ[ℚ] C)).comp δ))) ≠
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
          ((TensorProduct.map α.toLinearMap
            (LinearMap.id : C →ₗ[ℚ] C)).comp δ))).comp
        (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton ℚ (C →ₗ[ℚ] ℚ ⊗[ℚ] C)
            ((TensorProduct.map β.toLinearMap
              (LinearMap.id : C →ₗ[ℚ] C)).comp δ)))) := by
  intro U V hUV hVU
  dsimp only
  intro δ hδ heq
  have hvalues := rational_point_operator_counit_values U V hUV hVU δ hδ
  have hsame := congrArg
    (fun T : ℚ ⊗[ℚ] CoordinateRing ℚ (Fin 2) →ₗ[ℚ]
        ℚ ⊗[ℚ] CoordinateRing ℚ (Fin 2) =>
      ((Bialgebra.counitAlgHom ℚ (CoordinateRing ℚ (Fin 2))).toLinearMap.comp
        ((TensorProduct.lid ℚ (CoordinateRing ℚ (Fin 2))).toLinearMap.comp
          (T.comp (TensorProduct.lid ℚ (CoordinateRing ℚ (Fin 2))).symm.toLinearMap)))
        (matrix ℚ (Fin 2) 0 0)) heq
  have htwo_one : (2 : ℚ) = 1 := hvalues.1.symm.trans (hsame.trans hvalues.2)
  norm_num at htwo_one

end GeneralLinearCoordinateRing
