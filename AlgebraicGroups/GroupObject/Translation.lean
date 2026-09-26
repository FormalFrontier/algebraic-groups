/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Translations in group objects

This file supplies the left-translation isomorphism complementary to
`CategoryTheory.GrpObj.mulRight`.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.GrpObj

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The left-translation isomorphism `(f * ·)` of a group object. -/
@[to_additive /-- The left-translation isomorphism `(f + ·)` of an additive group object. -/]
def mulLeft {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A :=
  asIso ι[A] ≪≫ mulRight (f ≫ ι[A]) ≪≫ asIso ι[A]

@[to_additive (attr := simp)]
lemma mulLeft_hom {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) :
    (mulLeft f).hom = lift (toUnit _ ≫ f) (𝟙 _) ≫ μ := by
  let _ : BraidedCategory C := .ofCartesianMonoidalCategory
  simp only [mulLeft, Iso.trans_hom, mulRight, asIso_hom, Category.assoc]
  rw [CategoryTheory.GrpObj.mul_inv_rev]
  simp [comp_lift_assoc]

/-- Left translation acts on points by left multiplication. -/
@[to_additive (attr := simp) /-- Additive left translation acts on points by addition. -/]
lemma comp_mulLeft_hom {A : C} [GrpObj A] (a x : 𝟙_ C ⟶ A) :
    x ≫ (mulLeft a).hom = a * x := by
  rw [mulLeft_hom, ← Category.assoc]
  simp [CategoryTheory.Hom.mul_def]

/-- Left translation by `a` sends the unit point to `a`. -/
@[to_additive unit_comp_addLeft_hom
  /-- Additive left translation by `a` sends the zero point to `a`. -/]
lemma unit_comp_mulLeft_hom {A : C} [GrpObj A] (a : 𝟙_ C ⟶ A) :
    η[A] ≫ (mulLeft a).hom = a := by
  rw [mulLeft_hom, ← Category.assoc]
  simp only [comp_lift, Category.comp_id]
  simpa only [comp_toUnit_assoc, toUnit_unit, Category.id_comp,
    CategoryTheory.Hom.mul_def, CategoryTheory.Hom.one_def] using (mul_one a)

/-- Composing left translation by `b` with left translation by `a` is left
translation by `a * b`. -/
@[to_additive
  /-- Composing additive left translation by `b` with additive left translation
  by `a` is additive left translation by `a + b`. -/]
lemma mulLeft_trans_mulLeft {A : C} [GrpObj A] (a b : 𝟙_ C ⟶ A) :
    mulLeft b ≪≫ mulLeft a = mulLeft (a * b) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [mulLeft_hom, mulLeft_hom, mulLeft_hom]
  rw [← Category.assoc, comp_lift]
  simp only [Category.comp_id, comp_toUnit_assoc]
  change (toUnit A ≫ a) * ((toUnit A ≫ b) * 𝟙 A) =
    (toUnit A ≫ (a * b)) * 𝟙 A
  rw [← _root_.mul_assoc, ← MonObj.comp_mul]

@[to_additive (attr := simp)]
lemma mulLeft_one (A : C) [GrpObj A] : mulLeft η[A] = Iso.refl A := by
  ext
  simp

end CategoryTheory.GrpObj
