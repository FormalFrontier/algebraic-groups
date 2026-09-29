/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.DiagonalProduct
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import tests for the finite diagonal group-scheme product -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

universe u

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n] :
    diagonalGroupScheme K n ≅ (∏ᶜ fun _ : n ↦ multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K n

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) :
    (diagonalGroupSchemeProductIso K n).hom ≫
      Limits.Pi.π (fun _ : n ↦ multiplicativeGroupScheme K) j =
        diagonalGroupProjection K n j :=
  diagonalGroupSchemeProductIso_hom_π K n j

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) :
    (diagonalGroupSchemeProductIso K n).inv ≫ diagonalGroupProjection K n j =
      Limits.Pi.π (fun _ : n ↦ multiplicativeGroupScheme K) j :=
  diagonalGroupSchemeProductIso_inv_projection K n j

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) (X : Over (Spec (.of K))) (hom : X ⟶ (diagonalGroupScheme K n).X) :
    multiplicativeGroupHomUnits K X (hom ≫ (diagonalGroupProjection K n j).hom.hom) =
      diagonalGroupHomUnits K n X hom j :=
  diagonalGroupProjection_globalUnit K n j X hom

example (K : Type) [CommRing K] :
    Limits.IsTerminal (diagonalGroupScheme K (Fin 0)) :=
  diagonalGroupSchemeFin0IsTerminal K

example (K : Type) [CommRing K] :
    diagonalGroupScheme K (Fin 0) ≅
      (∏ᶜ fun _ : Fin 0 ↦ multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 0)

example (K : Type) [CommRing K] :
    diagonalGroupScheme K (Fin 1) ≅
      (∏ᶜ fun _ : Fin 1 ↦ multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 1)

example (K : Type) [CommRing K] (j : Fin 1) :
    (diagonalGroupSchemeProductIso K (Fin 1)).hom ≫
      Limits.Pi.π (fun _ : Fin 1 ↦ multiplicativeGroupScheme K) j =
        diagonalGroupProjection K (Fin 1) j :=
  diagonalGroupSchemeProductIso_hom_π K (Fin 1) j

example (K : Type) [CommRing K] :
    diagonalGroupScheme K (Fin 2) ≅
      (∏ᶜ fun _ : Fin 2 ↦ multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 2)

example (K : Type) [CommRing K] (j : Fin 2) :
    (diagonalGroupSchemeProductIso K (Fin 2)).inv ≫
      diagonalGroupProjection K (Fin 2) j =
        Limits.Pi.π (fun _ : Fin 2 ↦ multiplicativeGroupScheme K) j :=
  diagonalGroupSchemeProductIso_inv_projection K (Fin 2) j

example : Limits.IsTerminal (diagonalGroupScheme (ZMod 1) (Fin 0)) :=
  diagonalGroupSchemeFin0IsTerminal (ZMod 1)

example (j : Fin 2) :
    diagonalGroupProjectionCoordinateMap (ZMod 1) (Fin 2) j
      (multiplicativeGroupCoordinate (ZMod 1)) =
    DiagonalCoordinateRing.quotient (ZMod 1) (Fin 2)
      (GeneralLinearCoordinateRing.matrix (ZMod 1) (Fin 2) j j) :=
  diagonalGroupProjection_coordinate (ZMod 1) (Fin 2) j

example (j : Fin 2) :
    diagonalGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1) 1 ≫
      (diagonalGroupProjection (ZMod 1) (Fin 2) j).hom.hom =
      multiplicativeGroupMulEquivPoints (ZMod 1) (ZMod 1) 1 := by
  simpa only [map_one, Pi.one_apply] using
    diagonalGroupProjection_point (ZMod 1) (Fin 2) (ZMod 1) 1 j

private def dualNumberUnit : (DualNumber ℤ)ˣ :=
  ⟨1 + DualNumber.eps, 1 - DualNumber.eps,
    by
      calc
        (1 + DualNumber.eps) * (1 - DualNumber.eps) =
          (1 : DualNumber ℤ) - DualNumber.eps * DualNumber.eps := by ring
        _ = 1 := by simp,
    by
      calc
        (1 - DualNumber.eps) * (1 + DualNumber.eps) =
          (1 : DualNumber ℤ) - DualNumber.eps * DualNumber.eps := by ring
        _ = 1 := by simp⟩

private def dualNumberDiagonal : Matrix.DiagonalGroup (Fin 2) (DualNumber ℤ) :=
  (Matrix.DiagonalGroup.unitsEquiv).symm
    (fun j => if j = 0 then dualNumberUnit else 1)

example : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro assumption
  have hs := congrArg TrivSqZeroExt.snd assumption
  norm_num at hs

example : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by simp

example : diagonalGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ) dualNumberDiagonal ≫
    (diagonalGroupProjection ℤ (Fin 2) 0).hom.hom =
    multiplicativeGroupMulEquivPoints ℤ (DualNumber ℤ) dualNumberUnit := by
  simpa [dualNumberDiagonal] using
    diagonalGroupProjection_point ℤ (Fin 2) (DualNumber ℤ) dualNumberDiagonal 0

example : diagonalGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ) dualNumberDiagonal ≫
    (diagonalGroupProjection ℤ (Fin 2) 1).hom.hom =
    multiplicativeGroupMulEquivPoints ℤ (DualNumber ℤ) 1 := by
  simpa [dualNumberDiagonal] using
    diagonalGroupProjection_point ℤ (Fin 2) (DualNumber ℤ) dualNumberDiagonal 1
