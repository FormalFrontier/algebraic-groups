/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Translation

/-!
# Family translations in group objects

For a group object `G` in a Cartesian monoidal category and an arbitrary morphism
`i : P ⟶ G`, the isomorphisms `GrpObj.mulLeftFamily i` and `GrpObj.mulRightFamily i`
are the shears `(p, g) ↦ (p, i(p)g)` and `(g, p) ↦ (gi(p), p)`. Their inverses
multiply by `i(p)⁻¹` on the same respective side. The parameter `P` needs no group
structure, and `i` need not preserve multiplication. These are isomorphisms of
underlying objects, not isomorphisms of group objects.

The projection and pairing formulas characterize the maps on arbitrary test
objects. The API also gives inversion, unit and composition laws, naturality in
the parameter and under group-object morphisms, and compatibility with global
translations. The theorem `GrpObj.mulLeftFamily_hom_comp_snd_comp` factors a
translated multiplication followed by a group-object morphism through the right
family translation in its target.

## Implementation notes

All products, projections and pairings use the given Cartesian monoidal
structure. The inverse identities are the group laws in Mathlib's canonical
group on morphisms into `G`, followed by the product universal property. No
pullbacks, braiding or group structure on the parameter are required.

## References

* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Basic` and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for the product universal
  property and group laws on morphisms into a group object.
* `AlgebraicGroups.GroupObject.Translation`, for global left and right
  translations, recovered here when the parameter is the tensor unit.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section Family

variable {P G : C} [GrpObj G]

/-- The left family translation `(p, g) ↦ (p, i(p)g)`.
Its inverse sends `(p, g)` to `(p, i(p)⁻¹g)`. The projection and generalized-pair
formulas below characterize both maps without a group structure on `P`. -/
def mulLeftFamily (i : P ⟶ G) : P ⊗ G ≅ P ⊗ G where
  hom := lift (fst P G) ((fst P G ≫ i) * snd P G)
  inv := lift (fst P G) ((fst P G ≫ i)⁻¹ * snd P G)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul]

/-- The right family translation `(g, p) ↦ (gi(p), p)`.
Its inverse sends `(g, p)` to `(gi(p)⁻¹, p)`. Only the codomain `G` of the family
needs a group structure; multiplication order is not exchanged by a braiding. -/
def mulRightFamily (i : P ⟶ G) : G ⊗ P ≅ G ⊗ P where
  hom := lift (fst G P * (snd G P ≫ i)) (snd G P)
  inv := lift (fst G P * (snd G P ≫ i)⁻¹) (snd G P)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul]

@[reassoc (attr := simp)]
lemma mulLeftFamily_hom_fst (i : P ⟶ G) :
    (mulLeftFamily i).hom ≫ fst P G = fst P G := by
  simp [mulLeftFamily]

@[reassoc (attr := simp)]
lemma mulLeftFamily_hom_snd (i : P ⟶ G) :
    (mulLeftFamily i).hom ≫ snd P G = (fst P G ≫ i) * snd P G := by
  simp [mulLeftFamily]

@[reassoc (attr := simp)]
lemma mulLeftFamily_inv_fst (i : P ⟶ G) :
    (mulLeftFamily i).inv ≫ fst P G = fst P G := by
  simp [mulLeftFamily]

@[reassoc (attr := simp)]
lemma mulLeftFamily_inv_snd (i : P ⟶ G) :
    (mulLeftFamily i).inv ≫ snd P G = (fst P G ≫ i)⁻¹ * snd P G := by
  simp [mulLeftFamily]

@[reassoc (attr := simp)]
lemma mulRightFamily_hom_fst (i : P ⟶ G) :
    (mulRightFamily i).hom ≫ fst G P = fst G P * (snd G P ≫ i) := by
  simp [mulRightFamily]

@[reassoc (attr := simp)]
lemma mulRightFamily_hom_snd (i : P ⟶ G) :
    (mulRightFamily i).hom ≫ snd G P = snd G P := by
  simp [mulRightFamily]

@[reassoc (attr := simp)]
lemma mulRightFamily_inv_fst (i : P ⟶ G) :
    (mulRightFamily i).inv ≫ fst G P = fst G P * (snd G P ≫ i)⁻¹ := by
  simp [mulRightFamily]

@[reassoc (attr := simp)]
lemma mulRightFamily_inv_snd (i : P ⟶ G) :
    (mulRightFamily i).inv ≫ snd G P = snd G P := by
  simp [mulRightFamily]

/-- Left family translation on an arbitrary generalized pair. -/
@[reassoc (attr := simp)]
lemma lift_comp_mulLeftFamily_hom {T : C}
    (i : P ⟶ G) (p : T ⟶ P) (g : T ⟶ G) :
    lift p g ≫ (mulLeftFamily i).hom = lift p ((p ≫ i) * g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul]

/-- Right family translation on an arbitrary generalized pair. -/
@[reassoc (attr := simp)]
lemma lift_comp_mulRightFamily_hom {T : C}
    (i : P ⟶ G) (g : T ⟶ G) (p : T ⟶ P) :
    lift g p ≫ (mulRightFamily i).hom = lift (g * (p ≫ i)) p := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul]

/-- Inverting a left family translation inverts its translating family. -/
@[simp]
lemma mulLeftFamily_symm (i : P ⟶ G) :
    (mulLeftFamily i).symm = mulLeftFamily i⁻¹ := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;> simp [GrpObj.comp_inv]

/-- Inverting a right family translation inverts its translating family. -/
@[simp]
lemma mulRightFamily_symm (i : P ⟶ G) :
    (mulRightFamily i).symm = mulRightFamily i⁻¹ := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;> simp [GrpObj.comp_inv]

/-- The unit family acts identically by left translation. -/
@[simp]
lemma mulLeftFamily_one :
    mulLeftFamily (1 : P ⟶ G) = Iso.refl (P ⊗ G) := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;> simp [Iso.refl_hom]

/-- The unit family acts identically by right translation. -/
@[simp]
lemma mulRightFamily_one :
    mulRightFamily (1 : P ⟶ G) = Iso.refl (G ⊗ P) := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;> simp [Iso.refl_hom]

/-- Applying left translation by `j` and then by `i` multiplies by `i * j`.
The reversed composition order is essential for noncommutative groups. -/
lemma mulLeftFamily_trans_mulLeftFamily (i j : P ⟶ G) :
    mulLeftFamily j ≪≫ mulLeftFamily i = mulLeftFamily (i * j) := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Iso.trans_hom, Category.assoc, MonObj.comp_mul, _root_.mul_assoc]

/-- Applying right translation by `i` and then by `j` multiplies by `i * j`. -/
lemma mulRightFamily_trans_mulRightFamily (i j : P ⟶ G) :
    mulRightFamily i ≪≫ mulRightFamily j = mulRightFamily (i * j) := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Iso.trans_hom, Category.assoc, MonObj.comp_mul, _root_.mul_assoc]

end Family

section Naturality

/-- Left family translation commutes with arbitrary change of parameter. -/
@[reassoc]
lemma mulLeftFamily_param_naturality {Q P G : C} [GrpObj G]
    (a : Q ⟶ P) (i : P ⟶ G) :
    (a ⊗ₘ 𝟙 G) ≫ (mulLeftFamily i).hom =
      (mulLeftFamily (a ≫ i)).hom ≫ (a ⊗ₘ 𝟙 G) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul]

/-- Right family translation commutes with arbitrary change of parameter. -/
@[reassoc]
lemma mulRightFamily_param_naturality {Q P G : C} [GrpObj G]
    (a : Q ⟶ P) (i : P ⟶ G) :
    (𝟙 G ⊗ₘ a) ≫ (mulRightFamily i).hom =
      (mulRightFamily (a ≫ i)).hom ≫ (𝟙 G ⊗ₘ a) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul]

/-- Left family translation is natural under group-object morphisms. -/
@[reassoc]
lemma mulLeftFamily_hom_naturality {P G H : C} [GrpObj G] [GrpObj H]
    (i : P ⟶ G) (f : G ⟶ H) [IsMonHom f] :
    (mulLeftFamily i).hom ≫ (𝟙 P ⊗ₘ f) =
      (𝟙 P ⊗ₘ f) ≫ (mulLeftFamily (i ≫ f)).hom := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul, MonObj.mul_comp]

/-- Right family translation is natural under group-object morphisms. -/
@[reassoc]
lemma mulRightFamily_hom_naturality {P G H : C} [GrpObj G] [GrpObj H]
    (i : P ⟶ G) (f : G ⟶ H) [IsMonHom f] :
    (mulRightFamily i).hom ≫ (f ⊗ₘ 𝟙 P) =
      (f ⊗ₘ 𝟙 P) ≫ (mulRightFamily (i ≫ f)).hom := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [Category.assoc, MonObj.comp_mul, MonObj.mul_comp]

/-- A translated product followed by a group-object morphism factors through the
right family translation in the target. Both sides send a generalized pair
`(p, g)` to `f(i(p))f(g)`. In `mulRightFamily f`, the source `G` is only the
parameter: that isomorphism itself needs only the group structure on `H`. -/
@[reassoc]
lemma mulLeftFamily_hom_comp_snd_comp {P G H : C} [GrpObj G] [GrpObj H]
    (i : P ⟶ G) (f : G ⟶ H) [IsMonHom f] :
    (mulLeftFamily i).hom ≫ snd P G ≫ f =
      ((i ≫ f) ⊗ₘ 𝟙 G) ≫ (mulRightFamily f).hom ≫ fst H G := by
  simp [Category.assoc, MonObj.comp_mul, MonObj.mul_comp]

end Naturality

section GlobalTranslation

variable {G : C} [GrpObj G]

/-- With tensor-unit parameter, left family translation agrees with global left
translation through the left unitor. -/
lemma mulLeftFamily_unit_hom (i : 𝟙_ C ⟶ G) :
    (mulLeftFamily i).hom ≫ (λ_ G).hom = (λ_ G).hom ≫ (mulLeft i).hom := by
  simp only [leftUnitor_hom, mulLeftFamily_hom_snd, comp_mulLeft_hom_eq_mul]
  rw [toUnit_unique (fst (𝟙_ C) G) (toUnit ((𝟙_ C) ⊗ G))]

/-- With tensor-unit parameter, right family translation agrees with Mathlib's
global right translation through the right unitor. -/
lemma mulRightFamily_unit_hom (i : 𝟙_ C ⟶ G) :
    (mulRightFamily i).hom ≫ (ρ_ G).hom = (ρ_ G).hom ≫ (mulRight i).hom := by
  simp only [rightUnitor_hom, mulRightFamily_hom_fst, comp_mulRight_hom]
  rw [toUnit_unique (snd G (𝟙_ C)) (toUnit (G ⊗ (𝟙_ C)))]

end GlobalTranslation

end CategoryTheory.GrpObj
