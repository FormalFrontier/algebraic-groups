/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct
public import Mathlib.Data.ZMod.Basic

/-!
# Ordinary-import clients of the actual determinant product and smoothness

These checks use the public producer with no additional field, characteristic,
nontriviality or reducedness assumptions.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGroupsTest.GeneralLinearDeterminantProduct

open AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
  (pivot : n) (T : Over (Spec (.of K)))

example (s : T ⟶ specialLinearGroupUnderlyingScheme K n)
    (unit : T ⟶ multiplicativeGroupUnderlyingScheme K) :
    lift s unit ≫ (generalLinearDeterminantProductIso K n pivot).hom =
      (unit ≫ (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) *
        (s ≫ (specialLinearInclusion K n).hom.hom) := by
  rw [generalLinearDeterminantProductIso_hom]
  simp [MonObj.comp_mul]

/-- An arbitrary test scheme sees the actual determinant projection triangle. -/
theorem determinantTriangle_onTestScheme (point : T ⟶ specialLinearGroupUnderlyingScheme K n ⊗
    multiplicativeGroupUnderlyingScheme K) :
    (point ≫ (generalLinearDeterminantProductIso K n pivot).hom) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
        point ≫ snd (specialLinearGroupUnderlyingScheme K n)
          (multiplicativeGroupUnderlyingScheme K) := by
  rw [Category.assoc, generalLinearDeterminantProductIso_hom_comp_det]

/-- The product's inverse recovers the determinant from any test-scheme point. -/
theorem determinantInverseReadback_onTestScheme
    (point : T ⟶ generalLinearGroupUnderlyingScheme K n) :
    point ≫ (generalLinearDeterminantProductIso K n pivot).inv ≫
      snd (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) =
          point ≫ (generalLinearDeterminantSchemeHom K n).hom.hom := by
  rw [generalLinearDeterminantProductIso_inv_comp_snd]

example (point : T ⟶ generalLinearGroupUnderlyingScheme K n) :
    (point ≫ (generalLinearDeterminantProductIso K n pivot).inv ≫
      fst (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K)) ≫
          (specialLinearInclusion K n).hom.hom =
            (point ≫ (generalLinearDeterminantSchemeHom K n).hom.hom ≫
              (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom)⁻¹ *
                point := by
  have h := congrArg (fun f : generalLinearGroupUnderlyingScheme K n ⟶
    generalLinearGroupUnderlyingScheme K n ↦ point ≫ f)
    (generalLinearDeterminantProductIso_inv_fst_comp_inclusion K n pivot)
  simpa only [Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id] using h

example : Smooth (generalLinearDeterminantSchemeHom K n).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth K n pivot

/-- A rank-one integer GL point has its genuine unit-valued determinant as inverse projection. -/
theorem rankOneDeterminantPointRecovery (matrix : Matrix.GeneralLinearGroup (Fin 1) ℤ) :
    generalLinearGroupMulEquivPoints ℤ (Fin 1) ℤ matrix ≫
      (generalLinearDeterminantProductIso ℤ (Fin 1) 0).inv ≫
        snd (specialLinearGroupUnderlyingScheme ℤ (Fin 1))
          (multiplicativeGroupUnderlyingScheme ℤ) =
            multiplicativeGroupMulEquivPoints ℤ ℤ (Matrix.GeneralLinearGroup.det matrix) := by
  rw [generalLinearDeterminantProductIso_inv_comp_snd]
  exact generalLinearDeterminant_point ℤ (Fin 1) ℤ matrix

example (special : Matrix.SpecialLinearGroup (Fin 1) ℤ) :
    (lift (specialLinearGroupMulEquivPoints ℤ (Fin 1) ℤ special)
      (multiplicativeGroupMulEquivPoints ℤ ℤ (-1 : ℤˣ)) ≫
        (generalLinearDeterminantProductIso ℤ (Fin 1) 0).hom) ≫
          (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom =
            multiplicativeGroupMulEquivPoints ℤ ℤ (-1 : ℤˣ) := by
  rw [Category.assoc, generalLinearDeterminantProductIso_hom_comp_det]
  simp

example : Smooth (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth ℤ (Fin 1) 0

example : Smooth (generalLinearDeterminantSchemeHom (ZMod 1) (Fin 1)).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth (ZMod 1) (Fin 1) 0

end AlgebraicGroupsTest.GeneralLinearDeterminantProduct
