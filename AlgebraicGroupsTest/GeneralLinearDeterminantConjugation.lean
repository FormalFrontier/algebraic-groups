/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation
public import Mathlib.Data.ZMod.Basic

/-!
# An ordinary-import diagonal conjugation client

The upper unipotent in rank two over `ZMod 5` distinguishes a unit from its
inverse: conjugation at the column pivot by `2` scales the upper-right entry
by `3`, not by `2`.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGroupsTest.GeneralLinearDeterminantConjugation

open AlgebraicGeometry

def unitTwo : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

def upperUnipotent : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1

example :
    lift (multiplicativeGroupMulEquivPoints (ZMod 5) (ZMod 5) unitTwo)
      (specialLinearGroupMulEquivPoints (ZMod 5) (Fin 2) (ZMod 5) upperUnipotent) ≫
        generalLinearDeterminantConj (ZMod 5) (Fin 2) 1 =
      specialLinearGroupMulEquivPoints (ZMod 5) (Fin 2) (ZMod 5)
        (generalLinearDiagonalConjSL (Fin 2) 1 unitTwo upperUnipotent) :=
  generalLinearDeterminantConj_point (ZMod 5) (Fin 2) 1 unitTwo upperUnipotent

theorem columnPivotUpperEntry :
    generalLinearDiagonalConjSL (Fin 2) 1 unitTwo upperUnipotent 0 1 = 3 := by
  rw [generalLinearDiagonalConjSL_apply]
  norm_num [generalLinearConjDiagonalUnit, unitTwo, upperUnipotent,
    Matrix.SpecialLinearGroup.transvection_coe]

theorem rowPivotUpperEntry :
    generalLinearDiagonalConjSL (Fin 2) 0 unitTwo upperUnipotent 0 1 = 2 := by
  rw [generalLinearDiagonalConjSL_apply]
  norm_num [generalLinearConjDiagonalUnit, unitTwo, upperUnipotent,
    Matrix.SpecialLinearGroup.transvection_coe]

theorem columnPivot_detectsInverse :
    generalLinearDiagonalConjSL (Fin 2) 1 unitTwo upperUnipotent 0 1 ≠ 2 := by
  rw [columnPivotUpperEntry]
  decide

end AlgebraicGroupsTest.GeneralLinearDeterminantConjugation
