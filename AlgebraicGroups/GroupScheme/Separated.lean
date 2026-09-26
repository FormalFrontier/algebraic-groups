/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Separated group schemes

This file proves that a group scheme is separated when its unit section is a
closed immersion. In particular, every group scheme over a field is separated.

## Main results

- `AlgebraicGeometry.isSeparated_of_isClosedImmersion_unit`
- `AlgebraicGeometry.isSeparated_of_grpObj`
-/

public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The automorphism `(x, y) ↦ (x, x⁻¹y)` of the product of a group object with itself. -/
def leftDivIso (G : C) [GrpObj G] : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G) (lift (fst G G ≫ ι) (snd G G) ≫ μ)
  inv := lift (fst G G) (lift (fst G G) (snd G G) ≫ μ)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst, lift_snd]
      rw [← GrpObj.eq_lift_inv_left]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst_assoc, lift_snd]
      rw [GrpObj.lift_inv_left_eq]

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- A group scheme whose unit section is a closed immersion is separated. -/
theorem isSeparated_of_isClosedImmersion_unit (G : Over S) [GrpObj G]
    (hunit : IsClosedImmersion η[G].left) : IsSeparated G.hom := by
  constructor
  change IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left
  have hP : IsPullback
      (fst G (𝟙_ (Over S))).left
      (snd G (𝟙_ (Over S))).left
      G.hom (𝟙_ (Over S)).hom :=
    Over.isPullback_of_binaryFan_isLimit _
      (tensorProductIsBinaryProduct G (𝟙_ (Over S)))
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct G G)
  have hi_fst : (G ◁ η[G]).left ≫ (fst G G).left =
      (fst G (𝟙_ (Over S))).left := by
    simpa only [← Over.comp_left] using congrArg Over.Hom.left (whiskerLeft_fst G η[G])
  have hi_snd : (G ◁ η[G]).left ≫ (snd G G).left =
      (snd G (𝟙_ (Over S))).left ≫ η[G].left := by
    simpa only [← Over.comp_left] using congrArg Over.Hom.left (whiskerLeft_snd G η[G])
  have hi : IsPullback
      (G ◁ η[G]).left
      (snd G (𝟙_ (Over S))).left
      (snd G G).left η[G].left :=
    IsPullback.mk' hi_snd
      (by
        intro T φ φ' h₁ h₂
        exact hP.hom_ext
          (by simpa only [Category.assoc, hi_fst] using
            congrArg (fun q ↦ q ≫ (fst G G).left) h₁)
          h₂)
      (by
        intro T a b hab
        have w : (a ≫ (fst G G).left) ≫ G.hom = b ≫ (𝟙_ (Over S)).hom := by
          rw [Category.assoc, hB.w, ← Category.assoc, hab, Category.assoc, η[G].w]
        let l := hP.lift (a ≫ (fst G G).left) b w
        refine ⟨l, ?_, hP.lift_snd _ _ _⟩
        apply hB.hom_ext
        · rw [Category.assoc, hi_fst, hP.lift_fst]
        · rw [Category.assoc, hi_snd, ← Category.assoc, hP.lift_snd, hab])
  have hη : IsClosedImmersion (G ◁ η[G]).left :=
    MorphismProperty.of_isPullback hi.flip hunit
  rw [show lift (𝟙 G) (𝟙 G) =
      (ρ_ G).inv ≫ (G ◁ η[G]) ≫ (GrpObj.leftDivIso G).inv by
    ext <;> simp [GrpObj.leftDivIso]]
  dsimp only [Over.comp_left]
  have hρ : IsClosedImmersion (ρ_ G).inv.left := by
    change IsClosedImmersion ((Over.forget _).mapIso (ρ_ G)).inv
    infer_instance
  have hdiv : IsClosedImmersion (GrpObj.leftDivIso G).inv.left := by
    change IsClosedImmersion ((Over.forget _).mapIso (GrpObj.leftDivIso G)).inv
    infer_instance
  have hηdiv : IsClosedImmersion ((G ◁ η[G]).left ≫ (GrpObj.leftDivIso G).inv.left) :=
    @IsClosedImmersion.comp _ _ _ _ _ hη hdiv
  exact @IsClosedImmersion.comp _ _ _ _ _ hρ hηdiv

variable {K : Type u} [Field K]

/-- Every group scheme over a field is separated. -/
theorem isSeparated_of_grpObj (G : Over (Spec (.of K))) [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_isClosedImmersion_unit G <|
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom η[G].left (by simp)

end AlgebraicGeometry
