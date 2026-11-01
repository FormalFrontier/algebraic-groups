/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group structures and effective epimorphisms

This file transfers effective epimorphisms to over-categories and constructs a group object
structure on a subobject of a group object when multiplication and inversion restrict and the
subobject covers the terminal object by an effective epimorphism.

It also constructs a group structure on a supplied monoid object from an effective-epimorphic
monoid morphism out of a group object. `CategoryTheory.GrpObj.ofEffectiveEpiHom` retains the
entire supplied monoid structure and descends only inversion. Its inverse is characterized by
commuting with the original morphism, and is the unique arrow with that property.

The inverse descends because two generalized points agreeing after the monoid morphism have
inverses agreeing after it: both images are inverses of the same element of the target Hom
monoid. The inverse laws then follow by cancelling the effective epimorphism itself; no
product-epimorphism or pullback hypothesis is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.3 and the following
  subgroup assertion, for the nonempty, multiplication- and inversion-stable
  subscheme case. The categorical construction uses an effective epimorphism
  to obtain the unit.
* Mathlib, `EffectiveEpi.desc`, the cartesian group-object API in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, and
  `Mathlib.AlgebraicGeometry.Sites.Fpqc` for the descent and scheme instances.
* Mathlib's Hom monoid and group structures, `MonObj.mul_comp`, `MonObj.one_comp`,
  and `left_inv_eq_right_inv` for the inverse-compatibility argument; `EffectiveEpi.fac`
  characterizes the descended inverse.
-/

public section

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

private lemma overDescends {X Y W : Over S} (f : X ⟶ Y) (e : X ⟶ W)
    (h : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    ∀ {Z : C} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left →
      g₁ ≫ e.left = g₂ ≫ e.left := by
  intro Z g₁ g₂ hgf
  have hx : g₁ ≫ X.hom = g₂ ≫ X.hom := by
    rw [← f.w, ← Category.assoc, hgf, Category.assoc, f.w]
  let Z' : Over S := Over.mk (g₁ ≫ X.hom)
  let g₁' : Z' ⟶ X := Over.homMk g₁
  let g₂' : Z' ⟶ X := Over.homMk g₂ hx.symm
  have h' : g₁' ≫ f = g₂' ≫ f := by
    ext
    exact hgf
  exact congrArg CommaMorphism.left (h g₁' g₂' h')

/-- A morphism in an over-category is an effective epimorphism when its underlying morphism is. -/
noncomputable instance Over.effectiveEpi_of_effectiveEpi_left {X Y : Over S} (f : X ⟶ Y)
    [EffectiveEpi f.left] : EffectiveEpi f :=
  ⟨⟨
    { desc := fun e h ↦ Over.homMk
        (EffectiveEpi.desc f.left e.left (overDescends f e h)) (by
          apply (cancel_epi f.left).1
          simp only [← Category.assoc, EffectiveEpi.fac, e.w, f.w])
      fac := fun e h ↦ by
        ext
        exact EffectiveEpi.fac f.left e.left (overDescends f e h)
      uniq := fun e h m hm ↦ by
        ext
        exact EffectiveEpi.uniq f.left e.left (overDescends f e h) m.left
          (congrArg CommaMorphism.left hm) }⟩⟩

namespace GrpObj

variable [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj G]

/-- A subobject of a group object that is stable under multiplication and inversion is a group
object when its map to the terminal object is an effective epimorphism. Compare the
nonempty stable-subscheme assertion after Definition 1.3 of Milne, *Algebraic Groups*
(2017); effective epimorphy replaces the nonemptiness argument in this categorical setting. -/
@[instance_reducible]
noncomputable def ofEffectiveEpi (i : H ⟶ G) [Mono i]
    (mul : H ⊗ H ⟶ H) (inv : H ⟶ H)
    (mul_i : mul ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (inv_i : inv ≫ i = i ≫ ι[G])
    [EffectiveEpi (toUnit H)] : GrpObj H := by
  let localOne : H ⟶ H := lift (𝟙 H) inv ≫ mul
  have localOne_i : localOne ≫ i = toUnit H ≫ η[G] := by
    dsimp [localOne]
    rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
    simp only [Category.id_comp, inv_i]
    exact lift_comp_inv_right i
  let descends : ∀ {Z : C} (f g : Z ⟶ H), f ≫ toUnit H = g ≫ toUnit H →
      f ≫ localOne = g ≫ localOne := by
    intro Z f g hfg
    apply (cancel_mono i).1
    calc
      (f ≫ localOne) ≫ i = f ≫ toUnit H ≫ η[G] := by simp only [Category.assoc, localOne_i]
      _ = g ≫ toUnit H ≫ η[G] := by rw [← Category.assoc, hfg, Category.assoc]
      _ = (g ≫ localOne) ≫ i := by simp only [Category.assoc, localOne_i]
  let one : 𝟙_ C ⟶ H := EffectiveEpi.desc (toUnit H) localOne descends
  have one_i : one ≫ i = η[G] := by
    apply (cancel_epi (toUnit H)).1
    calc
      toUnit H ≫ (one ≫ i) = (toUnit H ≫ one) ≫ i := Category.assoc _ _ _ |>.symm
      _ = localOne ≫ i := by rw [EffectiveEpi.fac]
      _ = toUnit H ≫ η[G] := localOne_i
  letI : MonObj H :=
    { one := one
      mul := mul
      one_mul := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.id_comp η[G], ← Category.comp_id i]
        rw [← tensorHom_comp_tensorHom_assoc (𝟙 (𝟙_ C)) i η[G] (𝟙 G) μ[G]]
        simp
      mul_one := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.comp_id i, ← Category.id_comp η[G]]
        rw [← tensorHom_comp_tensorHom_assoc i (𝟙 (𝟙_ C)) (𝟙 G) η[G] μ[G]]
        simp
      mul_assoc := by
        apply (cancel_mono i).1
        simp only [Category.assoc, mul_i]
        calc
          mul ▷ H ≫ (i ⊗ₘ i) ≫ μ[G] =
              ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[G] ▷ G) ≫ μ[G] := by
            rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
            simpa only [Category.comp_id, tensorHom_id, Category.assoc] using
              (tensorHom_comp_tensorHom_assoc (i ⊗ₘ i) i μ[G] (𝟙 G) μ[G]).symm
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ G G G).hom ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [MonObj.mul_assoc]
          _ = (α_ H H H).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [associator_naturality_assoc]
          _ = (α_ H H H).hom ≫ H ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] := by
            have hright : H ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] =
                (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
              rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
              simpa only [Category.comp_id, id_tensorHom, Category.assoc] using
                (tensorHom_comp_tensorHom_assoc i (i ⊗ₘ i) (𝟙 G) μ[G] μ[G]).symm
            simp only [hright] }
  exact
    { inv := inv
      left_inv := by
        apply (cancel_mono i).1
        change (lift inv (𝟙 H) ≫ mul) ≫ i = (toUnit H ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i]
      right_inv := by
        apply (cancel_mono i).1
        change (lift (𝟙 H) inv ≫ mul) ≫ i = (toUnit H ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i] }

end GrpObj

end CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory

variable {K : Type u} [Field K]

/-- The map from a nonempty quasi-compact scheme over a field to the terminal object of the
over-category is an effective epimorphism. -/
noncomputable instance effectiveEpi_toUnit_of_nonempty (H : Over (Spec (.of K)))
    [Nonempty H.left] [QuasiCompact H.hom] : EffectiveEpi (toUnit H) := by
  let _ : Surjective H.hom :=
    ⟨Function.surjective_to_subsingleton (α := H.left) (β := Spec (.of K)) _⟩
  have : EffectiveEpi (toUnit H).left := by
    change EffectiveEpi H.hom
    infer_instance
  infer_instance

end AlgebraicGeometry

namespace CategoryTheory.GrpObj

open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
variable {G H : C} [gG : GrpObj G] [mH : MonObj H]

private lemma effectiveEpiHom_inv_compatible (q : G ⟶ H) [IsMonHom q]
    {T : C} (a b : T ⟶ G) (h : a ≫ q = b ≫ q) :
    a ≫ (ι[G] ≫ q) = b ≫ (ι[G] ≫ q) := by
  have hleft : (a⁻¹ ≫ q) * (a ≫ q) = 1 := by
    rw [← MonObj.mul_comp]
    simp
  have hright : (a ≫ q) * (b⁻¹ ≫ q) = 1 := by
    rw [h, ← MonObj.mul_comp]
    simp
  have hinv : a⁻¹ ≫ q = b⁻¹ ≫ q := left_inv_eq_right_inv hleft hright
  simpa only [Hom.inv_def, Category.assoc] using hinv

private noncomputable def effectiveEpiHom_inv
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] : H ⟶ H :=
  EffectiveEpi.desc q (ι[G] ≫ q) (effectiveEpiHom_inv_compatible q)

private lemma effectiveEpiHom_inv_fac
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] :
    q ≫ effectiveEpiHom_inv q = ι[G] ≫ q :=
  EffectiveEpi.fac q (ι[G] ≫ q) (effectiveEpiHom_inv_compatible q)

private lemma left_inv_of_epi
    (q : G ⟶ H) [IsMonHom q] [Epi q]
    (j : H ⟶ H) (hj : q ≫ j = gG.inv ≫ q) :
    lift j (𝟙 H) ≫ mH.mul = toUnit H ≫ mH.one := by
  rw [← Hom.mul_def j (𝟙 H), ← Hom.one_def]
  apply (cancel_epi q).1
  calc
    q ≫ (j * 𝟙 H) = (q ≫ j) * (q ≫ 𝟙 H) := MonObj.comp_mul q j (𝟙 H)
    _ = (gG.inv ≫ q) * q := by rw [hj, Category.comp_id]
    _ = (gG.inv * 𝟙 G) ≫ q := by
      rw [MonObj.mul_comp, Category.id_comp]
    _ = (1 : G ⟶ G) ≫ q := by
      rw [Hom.mul_def, GrpObj.left_inv G, ← Hom.one_def]
    _ = q ≫ (1 : H ⟶ H) := by
      rw [MonObj.one_comp, MonObj.comp_one]

private lemma right_inv_of_epi
    (q : G ⟶ H) [IsMonHom q] [Epi q]
    (j : H ⟶ H) (hj : q ≫ j = gG.inv ≫ q) :
    lift (𝟙 H) j ≫ mH.mul = toUnit H ≫ mH.one := by
  rw [← Hom.mul_def (𝟙 H) j, ← Hom.one_def]
  apply (cancel_epi q).1
  calc
    q ≫ (𝟙 H * j) = (q ≫ 𝟙 H) * (q ≫ j) := MonObj.comp_mul q (𝟙 H) j
    _ = q * (gG.inv ≫ q) := by rw [Category.comp_id, hj]
    _ = (𝟙 G * gG.inv) ≫ q := by
      rw [MonObj.mul_comp, Category.id_comp]
    _ = (1 : G ⟶ G) ≫ q := by
      rw [Hom.mul_def, GrpObj.right_inv G, ← Hom.one_def]
    _ = q ≫ (1 : H ⟶ H) := by
      rw [MonObj.one_comp, MonObj.comp_one]

/-- Extend a supplied monoid object to a group object along an effective-epimorphic monoid
morphism from a group object. The entire monoid structure is retained definitionally, and
inversion is the unique arrow commuting with inversion on the source. -/
@[expose, instance_reducible]
noncomputable def ofEffectiveEpiHom
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] : GrpObj H where
  toMonObj := mH
  inv := EffectiveEpi.desc q (ι[G] ≫ q) (by exact effectiveEpiHom_inv_compatible q)
  left_inv := by
    exact left_inv_of_epi q (effectiveEpiHom_inv q) (effectiveEpiHom_inv_fac q)
  right_inv := by
    exact right_inv_of_epi q (effectiveEpiHom_inv q) (effectiveEpiHom_inv_fac q)

/-- The group structure descended along an effective epimorphism retains the entire supplied
monoid structure. -/
@[simp]
theorem ofEffectiveEpiHom_toMonObj
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] :
    (ofEffectiveEpiHom q).toMonObj = mH := rfl

/-- Inversion on the descended group object commutes with the effective-epimorphic monoid
morphism from the original group object. -/
theorem ofEffectiveEpiHom_inv
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] :
    q ≫ (ofEffectiveEpiHom q).inv = gG.inv ≫ q :=
  effectiveEpiHom_inv_fac q

/-- The inverse on the descended group object is the unique arrow commuting with inversion
on the original group object. -/
theorem ofEffectiveEpiHom_inv_unique
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q]
    (j : H ⟶ H) (hj : q ≫ j = gG.inv ≫ q) :
    j = (ofEffectiveEpiHom q).inv :=
  (cancel_epi q).1 (hj.trans (ofEffectiveEpiHom_inv q).symm)

end CategoryTheory.GrpObj
