/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates
public import Mathlib.Data.ZMod.Basic

/-!
# Positive-stage coordinate clients

The rank-three first and second stages read their respective superdiagonals.
The integer matrix calculation exhibits the cross term in the upper-right
entry of a product, ruling out an additive coordinate homomorphism in that
direction on the whole first stage.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry
open scoped CategoryTheory CategoryTheory.MonObj

private def index01 : Matrix.UnitriangularGroup.superdiagonalIndex 3 1 :=
  ⟨(0, 1), by decide⟩

private def index12 : Matrix.UnitriangularGroup.superdiagonalIndex 3 1 :=
  ⟨(1, 2), by decide⟩

private def index02 : Matrix.UnitriangularGroup.superdiagonalIndex 3 2 :=
  ⟨(0, 2), by decide⟩

variable (K R : Type) [CommRing K] [CommRing R] [Algebra K R]

example (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 1) :
    unitriangularStagePointMulEquiv K 3 1 R s ≫
        (unitriangularStageCoordinateMap K 3 1 (by omega)).hom.hom ≫
        (CategoryTheory.Limits.Pi.π
          (fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 1 =>
            additiveGroupScheme K) index01).hom.hom =
      additiveGroupMulEquivPoints K R
        (.ofAdd ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 1)) := by
  have h := unitriangularStageCoordinateMap_point K 3 1 R (by omega) s index01
  rw [Matrix.UnitriangularGroup.superdiagonalCoordinateHom_apply] at h
  exact h

example (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 1) :
    unitriangularStagePointMulEquiv K 3 1 R s ≫
        (unitriangularStageCoordinateMap K 3 1 (by omega)).hom.hom ≫
        (CategoryTheory.Limits.Pi.π
          (fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 1 =>
            additiveGroupScheme K) index12).hom.hom =
      additiveGroupMulEquivPoints K R
        (.ofAdd ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 1 2)) := by
  have h := unitriangularStageCoordinateMap_point K 3 1 R (by omega) s index12
  rw [Matrix.UnitriangularGroup.superdiagonalCoordinateHom_apply] at h
  exact h

example (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2) :
    unitriangularStagePointMulEquiv K 3 2 R s ≫
        (unitriangularStageCoordinateMap K 3 2 (by omega)).hom.hom ≫
        (CategoryTheory.Limits.Pi.π
          (fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 2 =>
            additiveGroupScheme K) index02).hom.hom =
      additiveGroupMulEquivPoints K R
        (.ofAdd ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2)) := by
  have h := unitriangularStageCoordinateMap_point K 3 2 R (by omega) s index02
  rw [Matrix.UnitriangularGroup.superdiagonalCoordinateHom_apply] at h
  exact h

example : unitriangularStageSuccessor K 3 1 ≫
    unitriangularStageCoordinateMap K 3 1 (by omega) = 0 :=
  unitriangularStageCoordinateMap_successor_zero K 3 1 (by omega)

example (x y : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 ℤ 1) :
    ((x * y).1.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 2 =
      (x.1.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 2 +
        (y.1.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 2 +
        (x.1.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 1 *
          (y.1.1 : Matrix (Fin 3) (Fin 3) ℤ) 1 2 := by
  change ((x.1.1 : Matrix (Fin 3) (Fin 3) ℤ) *
    (y.1.1 : Matrix (Fin 3) (Fin 3) ℤ)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [x.1.2.2 0, y.1.2.2 2, one_mul, mul_one]
  ring

private def firstMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  1 + Matrix.single 0 1 1

private def secondMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  1 + Matrix.single 1 2 1

example : (firstMatrix * secondMatrix) 0 2 = 1 ∧
    firstMatrix 0 2 = 0 ∧ secondMatrix 0 2 = 0 := by
  constructor
  · rw [Matrix.mul_apply, Fin.sum_univ_three]
    norm_num [firstMatrix, secondMatrix, Matrix.one_apply, Matrix.single_apply]
  · constructor <;>
      norm_num [firstMatrix, secondMatrix, Matrix.one_apply, Matrix.single_apply]

example : Matrix.UnitriangularGroup.superdiagonalIndex 0 1 → (ZMod 1) :=
  fun ij => Fin.elim0 ij.1.1

example : IsEmpty (Matrix.UnitriangularGroup.superdiagonalIndex 1 1) := by
  constructor
  intro ij
  have h := ij.2
  have hi := ij.1.1.isLt
  have hj := ij.1.2.isLt
  omega

example : IsEmpty (Matrix.UnitriangularGroup.superdiagonalIndex 3 3) := by
  constructor
  intro ij
  have h := ij.2
  have hi := ij.1.1.isLt
  have hj := ij.1.2.isLt
  omega

example : unitriangularStageScheme ℤ 0 1 ⟶
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 0 1 =>
      additiveGroupScheme ℤ) :=
  unitriangularStageCoordinateMap ℤ 0 1 (by omega)

example : unitriangularStageScheme ℤ 1 1 ⟶
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 1 1 =>
      additiveGroupScheme ℤ) :=
  unitriangularStageCoordinateMap ℤ 1 1 (by omega)

example : unitriangularStageScheme ℤ 3 3 ⟶
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 3 =>
      additiveGroupScheme ℤ) :=
  unitriangularStageCoordinateMap ℤ 3 3 (by omega)

example : unitriangularStageScheme (ZMod 1) 0 2 ⟶
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 0 2 =>
      additiveGroupScheme (ZMod 1)) :=
  unitriangularStageCoordinateMap (ZMod 1) 0 2 (by omega)
