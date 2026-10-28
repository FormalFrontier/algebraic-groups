/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grp.Translation

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

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.AddMonObj

noncomputable section

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Left translation by `a` sends the unit point to `a`. -/
lemma unit_comp_leftTranslation_hom {A : C} [GrpObj A] (a : 𝟙_ C ⟶ A) :
    η[A] ≫ (leftTranslation a).hom = a := by
  rw [comp_leftTranslation_hom, toUnit_unit, Category.id_comp]
  rw [MonObj.one_eq_one]
  exact mul_one a

/-- Composing left translation by `b` with left translation by `a` is left
translation by `a * b`. This is the categorical composition order of the
identity `lₐ ∘ lᵦ = lₐᵦ` in Milne, *Algebraic Groups* (2017), item 1.8. -/
lemma leftTranslation_trans_leftTranslation {A : C} [GrpObj A] (a b : 𝟙_ C ⟶ A) :
    leftTranslation b ≪≫ leftTranslation a = leftTranslation (a * b) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [comp_leftTranslation_hom, leftTranslation_hom, leftTranslation_hom]
  rw [← _root_.mul_assoc, ← MonObj.comp_mul]

@[simp]
lemma leftTranslation_one (A : C) [GrpObj A] : leftTranslation η[A] = Iso.refl A := by
  apply Iso.ext
  rw [leftTranslation_hom]
  change 1 * (𝟙 A) = 𝟙 A
  exact one_mul _

@[simp]
lemma rightTranslation_one (A : C) [GrpObj A] : rightTranslation η[A] = Iso.refl A := by
  apply Iso.ext
  rw [rightTranslation_hom]
  change (𝟙 A) * 1 = 𝟙 A
  exact mul_one _

/-- Additive left translation on an additive group object, by a global point. -/
def leftAddTranslation {A : C} [AddGrpObj A] (a : 𝟙_ C ⟶ A) : A ≅ A where
  hom := (toUnit A ≫ a) + 𝟙 A
  inv := (toUnit A ≫ (-a)) + 𝟙 A
  hom_inv_id := by simp [AddMonObj.comp_add, AddGrpObj.comp_neg, ← add_assoc]
  inv_hom_id := by simp [AddMonObj.comp_add, AddGrpObj.comp_neg, ← add_assoc]

/-- Additive left translation acts on generalized points by addition of the constant point. -/
@[simp]
lemma comp_leftAddTranslation_hom {A T : C} [AddGrpObj A]
    (f : T ⟶ A) (a : 𝟙_ C ⟶ A) :
    f ≫ (leftAddTranslation a).hom = (toUnit T ≫ a) + f := by
  simp [leftAddTranslation, AddMonObj.comp_add]

end TauCeti
