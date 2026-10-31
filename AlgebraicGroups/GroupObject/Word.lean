/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Word morphisms for internal group objects

The canonical group structure on morphisms into an internal group object lets
`FreeGroup.lift` evaluate a word on any family of morphisms. Evaluation commutes with
arbitrary precomposition and with postcomposition by a group-object morphism.

For a given limiting fan, evaluating its projections represents word evaluation on
all tuples, uniquely. The index type and the category's object and morphism universes
are independent; no group-object structure is required on the fan's vertex or on test
objects.

This AI-assisted formalization uses Mathlib's free-group, Cartesian group-object,
and fan APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u v w

namespace CategoryTheory.GrpObj

/-- Word evaluation commutes with arbitrary precomposition. -/
theorem comp_freeGroup_lift
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {G P Q : C} [GrpObj G] {I : Type w}
    (p : I → (Q ⟶ G)) (a : P ⟶ Q) (wrd : FreeGroup I) :
    a ≫ FreeGroup.lift p wrd = FreeGroup.lift (fun i ↦ a ≫ p i) wrd := by
  induction wrd using FreeGroup.induction_on with
  | one =>
      simp only [map_one, MonObj.comp_one]
  | of i =>
      simp only [FreeGroup.lift_apply_of]
  | inv_of i hi =>
      simpa only [map_inv, comp_inv] using
        congrArg (fun b : P ⟶ G ↦ b⁻¹) hi
  | mul x y hx hy =>
      simp only [map_mul, MonObj.comp_mul, hx, hy]

/-- Word evaluation commutes with postcomposition by a group-object morphism. -/
theorem freeGroup_lift_comp
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {G H P : C} [GrpObj G] [GrpObj H] {I : Type w}
    (p : I → (P ⟶ G)) (f : G ⟶ H) [IsMonHom f] (wrd : FreeGroup I) :
    FreeGroup.lift p wrd ≫ f = FreeGroup.lift (fun i ↦ p i ≫ f) wrd := by
  induction wrd using FreeGroup.induction_on with
  | one =>
      simp only [map_one, MonObj.one_comp]
  | of i =>
      simp only [FreeGroup.lift_apply_of]
  | inv_of i hi =>
      simpa only [map_inv, inv_comp] using
        congrArg (fun b : P ⟶ H ↦ b⁻¹) hi
  | mul x y hx hy =>
      simp only [map_mul, MonObj.mul_comp, hx, hy]

/-- A component-compatible comparison intertwines word evaluation. -/
theorem freeGroup_lift_naturality
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {G H P Q : C} [GrpObj G] [GrpObj H] {I : Type w}
    (p : I → (P ⟶ G)) (q : I → (Q ⟶ H))
    (t : P ⟶ Q) (f : G ⟶ H) [IsMonHom f]
    (h : ∀ i, t ≫ q i = p i ≫ f) (wrd : FreeGroup I) :
    FreeGroup.lift p wrd ≫ f = t ≫ FreeGroup.lift q wrd := by
  rw [freeGroup_lift_comp, comp_freeGroup_lift]
  exact congrArg (fun r : I → (P ⟶ H) ↦ FreeGroup.lift r wrd)
    (funext fun i ↦ (h i).symm)

/-- Evaluating the projections of a limiting fan agrees with evaluating any tuple. -/
theorem lift_comp_freeGroup_lift
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {G : C} [GrpObj G] {I : Type w}
    (F : Fan (fun _ : I ↦ G)) (hF : IsLimit F)
    (wrd : FreeGroup I) {T : C} (a : I → (T ⟶ G)) :
    Fan.IsLimit.lift hF a ≫ FreeGroup.lift F.proj wrd = FreeGroup.lift a wrd := by
  simpa only [Fan.IsLimit.fac] using
    comp_freeGroup_lift F.proj (Fan.IsLimit.lift hF a) wrd

/-- A given limiting fan uniquely represents word evaluation on all tuples.

The representing morphism is `FreeGroup.lift F.proj wrd`.
-/
theorem existsUnique_word_morphism
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {G : C} [GrpObj G] {I : Type w}
    (F : Fan (fun _ : I ↦ G)) (hF : IsLimit F) (wrd : FreeGroup I) :
    ∃! m : F.pt ⟶ G, ∀ (T : C) (a : I → (T ⟶ G)),
      Fan.IsLimit.lift hF a ≫ m = FreeGroup.lift a wrd := by
  refine ⟨FreeGroup.lift F.proj wrd, ?_, ?_⟩
  · intro T a
    exact lift_comp_freeGroup_lift F hF wrd a
  · intro m hm
    have hid : Fan.IsLimit.lift hF F.proj = 𝟙 F.pt := by
      apply Fan.IsLimit.hom_ext hF
      intro i
      rw [Fan.IsLimit.fac, Category.id_comp]
    simpa only [hid, Category.id_comp] using hm F.pt F.proj

end CategoryTheory.GrpObj
