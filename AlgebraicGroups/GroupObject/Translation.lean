/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Translations in group objects

This file supplies the left-translation isomorphism complementary to
`CategoryTheory.GrpObj.mulRight` and the characteristic composition formulas for both
translations. A global point `a : 𝟙_ C ⟶ A` acts on every generalized point `f : T ⟶ A`;
`T` is arbitrary and `f` need not preserve multiplication. The left-composition simp
normal form is `(toUnit T ≫ a) * f`, with the analogous additive formula.
The structural formula for the naked translation morphism and the terminal-point
specialization remain available as explicit rewrite lemmas, not simp rules.

## References

* J. S. Milne, *Algebraic Groups* (2017), items 1.7–1.8, for rational
  group points and the left-translation isomorphism of algebraic groups.
  The translator is a global point `𝟙_ C ⟶ A` of an arbitrary group object,
  acting on generalized points with arbitrary domain; no closed-point transitivity
  is asserted.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, especially
  `GrpObj.mulRight` and inversion, for the group-object translation API.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.GrpObj

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Right translation acts on morphisms by right multiplication by the constant point. -/
@[to_additive
  /-- Right translation acts on morphisms by addition of the constant point. -/]
lemma comp_mulRight_hom {A T : C} [GrpObj A] (f : T ⟶ A) (g : 𝟙_ C ⟶ A) :
    f ≫ (mulRight g).hom = f * (toUnit T ≫ g) := by
  change f ≫ ((𝟙 A) * (toUnit A ≫ g)) = _
  simp only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

/-- The left-translation isomorphism `(f * ·)` of a group object.
For algebraic groups and rational points, see Milne, *Algebraic Groups* (2017), item 1.8. -/
@[to_additive /-- The left-translation isomorphism `(f + ·)` of an additive group object. -/]
def mulLeft {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A :=
  asIso ι[A] ≪≫ mulRight (f ≫ ι[A]) ≪≫ asIso ι[A]

@[to_additive]
lemma mulLeft_hom {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) :
    (mulLeft f).hom = lift (toUnit _ ≫ f) (𝟙 _) ≫ μ := by
  let _ : BraidedCategory C := .ofCartesianMonoidalCategory
  simp only [mulLeft, Iso.trans_hom, mulRight, asIso_hom, Category.assoc]
  rw [CategoryTheory.GrpObj.mul_inv_rev]
  simp [comp_lift_assoc]

/-- Left translation acts on generalized points by left multiplication by the constant point.
The translating point is global, while the generalized point need not be multiplicative. -/
@[to_additive (attr := simp)
  /-- Additive left translation acts on generalized points by addition of the constant point.
  The translating point is global, while the generalized point need not be additive. -/, simp]
lemma comp_mulLeft_hom_eq_mul {A T : C} [GrpObj A]
    (f : T ⟶ A) (a : 𝟙_ C ⟶ A) :
    f ≫ (mulLeft a).hom = (toUnit T ≫ a) * f := by
  rw [mulLeft_hom, ← CategoryTheory.Hom.mul_def, MonObj.comp_mul]
  simp only [comp_toUnit_assoc, Category.comp_id]

/-- Left translation acts on points by left multiplication. -/
@[to_additive /-- Additive left translation acts on points by addition. -/]
lemma comp_mulLeft_hom {A : C} [GrpObj A] (a x : 𝟙_ C ⟶ A) :
    x ≫ (mulLeft a).hom = a * x := by
  simpa only [toUnit_unit, Category.id_comp] using comp_mulLeft_hom_eq_mul x a

/-- Left translation by `a` sends the unit point to `a`. -/
@[to_additive unit_comp_addLeft_hom
  /-- Additive left translation by `a` sends the zero point to `a`. -/]
lemma unit_comp_mulLeft_hom {A : C} [GrpObj A] (a : 𝟙_ C ⟶ A) :
    η[A] ≫ (mulLeft a).hom = a := by
  rw [comp_mulLeft_hom]
  simpa only [CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp] using
    (_root_.mul_one a)

/-- Composing left translation by `b` with left translation by `a` is left
translation by `a * b`. This is the categorical composition order of the
identity `lₐ ∘ lᵦ = lₐᵦ` in Milne, *Algebraic Groups* (2017), item 1.8. -/
@[to_additive
  /-- Composing additive left translation by `b` with additive left translation
  by `a` is additive left translation by `a + b`. -/]
lemma mulLeft_trans_mulLeft {A : C} [GrpObj A] (a b : 𝟙_ C ⟶ A) :
    mulLeft b ≪≫ mulLeft a = mulLeft (a * b) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [comp_mulLeft_hom_eq_mul, mulLeft_hom, mulLeft_hom]
  change (toUnit A ≫ a) * ((toUnit A ≫ b) * 𝟙 A) =
    (toUnit A ≫ (a * b)) * 𝟙 A
  rw [← _root_.mul_assoc, ← MonObj.comp_mul]

@[to_additive (attr := simp)]
lemma mulLeft_one (A : C) [GrpObj A] : mulLeft η[A] = Iso.refl A := by
  apply Iso.ext
  simpa only [Category.id_comp, ← CategoryTheory.Hom.one_def, _root_.one_mul,
    Iso.refl_hom] using comp_mulLeft_hom_eq_mul (𝟙 A) η[A]

end CategoryTheory.GrpObj
