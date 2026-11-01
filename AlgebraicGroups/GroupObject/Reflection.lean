/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Homomorphisms between pulled-back monoid objects

A fully faithful Oplax monoidal functor pulls a morphism preserving supplied target monoid
structures back to a morphism preserving their pulled-back monoid structures.

Mathlib's monoid-image construction recovers the supplied target structure from its pullback
along a fully faithful monoidal functor.

This uses Mathlib's existing `CategoryTheory.Functor.FullyFaithful.monObj` construction and
its formalization of fully faithful pullback of monoid objects.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe uC vC uD vD

/-- A homomorphism between supplied target monoid structures pulls back to a homomorphism
between their fully faithful monoid pullbacks along an Oplax monoidal functor. -/
theorem CategoryTheory.Functor.FullyFaithful.isMonHom_preimage_monObj
    {C : Type uC} [cC : Category.{vC} C]
    [mC : MonoidalCategory.{vC} C]
    {D : Type uD} [cD : Category.{vD} D]
    [mD : MonoidalCategory.{vD} D]
    {F : C ⥤ D} [oF : F.OplaxMonoidal]
    (hF : F.FullyFaithful) {X Y : C}
    [tX : MonObj (F.obj X)] [tY : MonObj (F.obj Y)]
    (f : F.obj X ⟶ F.obj Y)
    [hf : @CategoryTheory.IsMonHom
      D cD mD (F.obj X) (F.obj Y) tX tY f] :
    @CategoryTheory.IsMonHom C cC mC X Y
      (@CategoryTheory.Functor.FullyFaithful.monObj
        C cC mC D cD mD F oF hF X tX)
      (@CategoryTheory.Functor.FullyFaithful.monObj
        C cC mC D cD mD F oF hF Y tY)
      (hF.preimage (X := X) (Y := Y) f) := by
  let : MonObj X :=
    @CategoryTheory.Functor.FullyFaithful.monObj
      C cC mC D cD mD F oF hF X tX
  let : MonObj Y :=
    @CategoryTheory.Functor.FullyFaithful.monObj
      C cC mC D cD mD F oF hF Y tY
  refine { one_hom := ?_, mul_hom := ?_ }
  · change
      hF.preimage (Functor.OplaxMonoidal.η F ≫ tX.one) ≫
          hF.preimage (X := X) (Y := Y) f =
        hF.preimage (Functor.OplaxMonoidal.η F ≫ tY.one)
    apply hF.map_injective
    simp only [Functor.map_comp, hF.map_preimage]
    rw [Category.assoc,
      @CategoryTheory.IsMonHom.one_hom
        D cD mD (F.obj X) (F.obj Y) tX tY f hf]
  · change
      hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ tX.mul) ≫
          hF.preimage (X := X) (Y := Y) f =
        (hF.preimage (X := X) (Y := Y) f ⊗ₘ
            hF.preimage (X := X) (Y := Y) f) ≫
          hF.preimage (Functor.OplaxMonoidal.δ F Y Y ≫ tY.mul)
    apply hF.map_injective
    simp only [Functor.map_comp, hF.map_preimage]
    have hδ :
        Functor.OplaxMonoidal.δ F X X ≫ (f ⊗ₘ f) =
          F.map (hF.preimage (X := X) (Y := Y) f ⊗ₘ
              hF.preimage (X := X) (Y := Y) f) ≫
            Functor.OplaxMonoidal.δ F Y Y := by
      simpa only [hF.map_preimage] using
        (Functor.OplaxMonoidal.δ_natural F
          (hF.preimage (X := X) (Y := Y) f)
          (hF.preimage (X := X) (Y := Y) f))
    calc
      (Functor.OplaxMonoidal.δ F X X ≫ tX.mul) ≫ f =
          Functor.OplaxMonoidal.δ F X X ≫ ((f ⊗ₘ f) ≫ tY.mul) := by
        rw [Category.assoc,
          @CategoryTheory.IsMonHom.mul_hom
            D cD mD (F.obj X) (F.obj Y) tX tY f hf]
      _ = (Functor.OplaxMonoidal.δ F X X ≫ (f ⊗ₘ f)) ≫ tY.mul :=
        (Category.assoc _ _ _).symm
      _ = (F.map (hF.preimage (X := X) (Y := Y) f ⊗ₘ
              hF.preimage (X := X) (Y := Y) f) ≫
            Functor.OplaxMonoidal.δ F Y Y) ≫ tY.mul := by
        rw [hδ]
      _ = F.map (hF.preimage (X := X) (Y := Y) f ⊗ₘ
            hF.preimage (X := X) (Y := Y) f) ≫
          (Functor.OplaxMonoidal.δ F Y Y ≫ tY.mul) :=
        Category.assoc _ _ _

/-- The image of a fully faithful monoid pullback along a monoidal functor is the supplied
target monoid structure. -/
theorem CategoryTheory.Functor.FullyFaithful.monObjObj_monObj
    {C : Type uC} [cC : Category.{vC} C]
    [mC : MonoidalCategory.{vC} C]
    {D : Type uD} [cD : Category.{vD} D]
    [mD : MonoidalCategory.{vD} D]
    {F : C ⥤ D} [mF : F.Monoidal]
    (hF : F.FullyFaithful) (X : C)
    [tX : MonObj (F.obj X)] :
    @CategoryTheory.Functor.monObjObj
      C cC mC D cD mD F mF.toLaxMonoidal X
      (@CategoryTheory.Functor.FullyFaithful.monObj
        C cC mC D cD mD F mF.toOplaxMonoidal hF X tX) = tX := by
  apply CategoryTheory.MonObj.ext
  change
    @CategoryTheory.Functor.LaxMonoidal.μ
        C cC mC D cD mD F mF.toLaxMonoidal X X ≫
      F.map (hF.preimage
        (@CategoryTheory.Functor.OplaxMonoidal.δ
          C cC mC D cD mD F mF.toOplaxMonoidal X X ≫ tX.mul)) =
      tX.mul
  rw [hF.map_preimage, ← Category.assoc,
    @CategoryTheory.Functor.Monoidal.μ_δ
      C cC mC D cD mD F mF X X,
    Category.id_comp]
