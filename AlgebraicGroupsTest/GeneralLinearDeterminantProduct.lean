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

open AlgebraicGeometry TauCeti.DiagonalizableGroup

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
  (pivot : n) (T : Over (Spec (.of K)))

example (s : T ⟶ (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
    (unit : T ⟶ (multiplicativeGroupScheme K).X) :
    lift s unit ≫ (generalLinearDeterminantProductIso K n pivot).hom =
      (unit ≫ (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) *
        (s ≫ (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom) := by
  rw [generalLinearDeterminantProductIso_hom]
  simp [MonObj.comp_mul]

/-- An arbitrary test scheme sees the actual determinant projection triangle. -/
theorem determinantTriangle_onTestScheme
    (point : T ⟶ (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X ⊗
    (multiplicativeGroupScheme K).X) :
    (point ≫ (generalLinearDeterminantProductIso K n pivot).hom) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
        point ≫ snd ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
          ((multiplicativeGroupScheme K).X) := by
  rw [Category.assoc, generalLinearDeterminantProductIso_hom_comp_det]

/-- The product's inverse recovers the determinant from any test-scheme point. -/
theorem determinantInverseReadback_onTestScheme
    (point : T ⟶ (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X) :
    point ≫ (generalLinearDeterminantProductIso K n pivot).inv ≫
      snd ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
        ((multiplicativeGroupScheme K).X) =
          point ≫ (generalLinearDeterminantSchemeHom K n).hom.hom := by
  rw [generalLinearDeterminantProductIso_inv_comp_snd]

example (point : T ⟶ (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X) :
    (point ≫ (generalLinearDeterminantProductIso K n pivot).inv ≫
      fst ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
        ((multiplicativeGroupScheme K).X)) ≫
          (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom =
            (point ≫ (generalLinearDeterminantSchemeHom K n).hom.hom ≫
              (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom)⁻¹ *
                point := by
  have h := congrArg (fun f : (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X ⟶
    (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X ↦ point ≫ f)
    (generalLinearDeterminantProductIso_inv_fst_comp_inclusion K n pivot)
  simpa only [Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id] using h

example : Smooth (generalLinearDeterminantSchemeHom K n).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth K n pivot

/-- A rank-one integer GL point has its genuine unit-valued determinant as inverse projection. -/
theorem rankOneDeterminantPointRecovery (matrix : Matrix.GeneralLinearGroup (Fin 1) ℤ) :
    TauCeti.GeneralLinear.groupSchemePointMulEquiv (Fintype.card (Fin 1)) ℤ
      ((TauCeti.GeneralLinear.reindexedPointsMulEquiv ℤ (Fin 1) ℤ).symm matrix) ≫
      (generalLinearDeterminantProductIso ℤ (Fin 1) 0).inv ≫
        snd ((TauCeti.SpecialLinear.groupScheme ℤ (Fintype.card (Fin 1))).X)
          ((multiplicativeGroupScheme ℤ).X) =
            (multiplicativeGroupSchemePointsMulEquiv (R := ℤ) (A := ℤ)).symm
              (Matrix.GeneralLinearGroup.det matrix) := by
  rw [generalLinearDeterminantProductIso_inv_comp_snd]
  exact generalLinearDeterminant_point ℤ (Fin 1) ℤ matrix

example (special : Matrix.SpecialLinearGroup (Fin 1) ℤ) :
    (lift (TauCeti.SpecialLinear.groupSchemePointMulEquiv (Fintype.card (Fin 1)) ℤ
      ((TauCeti.SpecialLinear.reindexedPointsMulEquiv ℤ (Fin 1) ℤ).symm special))
      ((multiplicativeGroupSchemePointsMulEquiv
        (R := ℤ) (A := ℤ)).symm (-1 : ℤˣ)) ≫
        (generalLinearDeterminantProductIso ℤ (Fin 1) 0).hom) ≫
          (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom =
            (multiplicativeGroupSchemePointsMulEquiv (R := ℤ) (A := ℤ)).symm (-1 : ℤˣ) := by
  rw [Category.assoc, generalLinearDeterminantProductIso_hom_comp_det]
  simp

example : Smooth (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth ℤ (Fin 1) 0

example : Smooth (generalLinearDeterminantSchemeHom (ZMod 1) (Fin 1)).hom.hom.left :=
  generalLinearDeterminantSchemeHom_smooth (ZMod 1) (Fin 1) 0

end AlgebraicGroupsTest.GeneralLinearDeterminantProduct
