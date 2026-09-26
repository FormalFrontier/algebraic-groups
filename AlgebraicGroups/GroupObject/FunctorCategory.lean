/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp

/-!
# Group objects and pointwise subgroups in functor categories

This file supplies the group analogue of the existing monoid-functor-category
constructions and uses it to lift an injective natural transformation whose
component ranges are subgroups to a morphism of group objects.

## Main definitions

- `CategoryTheory.Monoidal.GrpFunctorCategory.functorObj`
- `CategoryTheory.Monoidal.GrpFunctorCategory.inverseObj`
- `CategoryTheory.Monoidal.GrpFunctorCategory.pointwiseGrp`
- `CategoryTheory.NatTrans.IsPointwiseSubgroup`
- `CategoryTheory.NatTrans.IsPointwiseSubgroup.grpObj`
- `CategoryTheory.NatTrans.IsPointwiseSubgroup.isMonHom`
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonObj

universe v₁ v₂ u₁ u₂ v u w

namespace CategoryTheory.Monoidal.GrpFunctorCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation turns a group object in a functor category into a group object
at each object of the source category. -/
def functorObjObj (A : C ⥤ D) [GrpObj A] (X : C) : Grp D where
  X := A.obj X
  grp :=
    { (MonFunctorCategoryEquivalence.functorObjObj A X).mon with
      inv := ι[A].app X
      left_inv := by
        rw [← show (CartesianMonoidalCategory.lift ι[A] (𝟙 A)).app X =
            CartesianMonoidalCategory.lift (ι[A].app X) (𝟙 (A.obj X)) by
              apply CartesianMonoidalCategory.hom_ext
              · rw [CartesianMonoidalCategory.lift_fst]
                simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app] using
                  congr_app (CartesianMonoidalCategory.lift_fst ι[A] (𝟙 A)) X
              · rw [CartesianMonoidalCategory.lift_snd]
                simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app,
                  NatTrans.id_app] using
                  congr_app (CartesianMonoidalCategory.lift_snd ι[A] (𝟙 A)) X]
        rw [← show (SemiCartesianMonoidalCategory.toUnit A).app X =
            SemiCartesianMonoidalCategory.toUnit (A.obj X) by
              simpa only [Monoidal.tensorUnit_obj] using
                (SemiCartesianMonoidalCategory.toUnit_unique
                  ((SemiCartesianMonoidalCategory.toUnit A).app X)
                  (SemiCartesianMonoidalCategory.toUnit (A.obj X)))]
        exact congr_app (GrpObj.left_inv A) X
      right_inv := by
        rw [← show (CartesianMonoidalCategory.lift (𝟙 A) ι[A]).app X =
            CartesianMonoidalCategory.lift (𝟙 (A.obj X)) (ι[A].app X) by
              apply CartesianMonoidalCategory.hom_ext
              · rw [CartesianMonoidalCategory.lift_fst]
                simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app,
                  NatTrans.id_app] using
                  congr_app (CartesianMonoidalCategory.lift_fst (𝟙 A) ι[A]) X
              · rw [CartesianMonoidalCategory.lift_snd]
                simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app] using
                  congr_app (CartesianMonoidalCategory.lift_snd (𝟙 A) ι[A]) X]
        rw [← show (SemiCartesianMonoidalCategory.toUnit A).app X =
            SemiCartesianMonoidalCategory.toUnit (A.obj X) by
              simpa only [Monoidal.tensorUnit_obj] using
                (SemiCartesianMonoidalCategory.toUnit_unique
                  ((SemiCartesianMonoidalCategory.toUnit A).app X)
                  (SemiCartesianMonoidalCategory.toUnit (A.obj X)))]
        exact congr_app (GrpObj.right_inv A) X }

/-- A group object in a functor category induces a functor to group objects. -/
def functorObj (A : C ⥤ D) [GrpObj A] : C ⥤ Grp D where
  obj := functorObjObj A
  map f := ⟨((MonFunctorCategoryEquivalence.functorObj A).map f)⟩
  map_id X := by
    apply Grp.hom_ext
    exact congrArg Mon.Hom.hom ((MonFunctorCategoryEquivalence.functorObj A).map_id X)
  map_comp f g := by
    apply Grp.hom_ext
    exact congrArg Mon.Hom.hom ((MonFunctorCategoryEquivalence.functorObj A).map_comp f g)

set_option backward.isDefEq.respectTransparency false in
/-- A functor to group objects induces a group object in the functor category. -/
def inverseObj (A : C ⥤ Grp D) : Grp (C ⥤ D) := by
  let M := (monFunctorCategoryEquivalence C D).inverse.obj (A ⋙ Grp.forget₂Mon D)
  let inv : M.X ⟶ M.X :=
    { app X := ι[(A.obj X).X]
      naturality X Y f := (GrpObj.inv_hom (A.map f).hom.hom).symm }
  exact
  { M with
    grp :=
      { inv := inv
        left_inv := by
          ext X
          simp only [NatTrans.comp_app]
          rw [show (CartesianMonoidalCategory.lift inv (𝟙 M.X)).app X =
              CartesianMonoidalCategory.lift (inv.app X) (𝟙 (M.X.obj X)) by
                apply CartesianMonoidalCategory.hom_ext
                · rw [CartesianMonoidalCategory.lift_fst]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app] using
                    congr_app (CartesianMonoidalCategory.lift_fst inv (𝟙 M.X)) X
                · rw [CartesianMonoidalCategory.lift_snd]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app,
                    NatTrans.id_app] using
                    congr_app (CartesianMonoidalCategory.lift_snd inv (𝟙 M.X)) X]
          rw [show (SemiCartesianMonoidalCategory.toUnit M.X).app X =
              SemiCartesianMonoidalCategory.toUnit (M.X.obj X) by
                simpa only [Monoidal.tensorUnit_obj] using
                  (SemiCartesianMonoidalCategory.toUnit_unique
                    ((SemiCartesianMonoidalCategory.toUnit M.X).app X)
                    (SemiCartesianMonoidalCategory.toUnit (M.X.obj X)))]
          exact GrpObj.left_inv (A.obj X).X
        right_inv := by
          ext X
          simp only [NatTrans.comp_app]
          rw [show (CartesianMonoidalCategory.lift (𝟙 M.X) inv).app X =
              CartesianMonoidalCategory.lift (𝟙 (M.X.obj X)) (inv.app X) by
                apply CartesianMonoidalCategory.hom_ext
                · rw [CartesianMonoidalCategory.lift_fst]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app,
                    NatTrans.id_app] using
                    congr_app (CartesianMonoidalCategory.lift_fst (𝟙 M.X) inv) X
                · rw [CartesianMonoidalCategory.lift_snd]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app] using
                    congr_app (CartesianMonoidalCategory.lift_snd (𝟙 M.X) inv) X]
          rw [show (SemiCartesianMonoidalCategory.toUnit M.X).app X =
              SemiCartesianMonoidalCategory.toUnit (M.X.obj X) by
                simpa only [Monoidal.tensorUnit_obj] using
                  (SemiCartesianMonoidalCategory.toUnit_unique
                    ((SemiCartesianMonoidalCategory.toUnit M.X).app X)
                    (SemiCartesianMonoidalCategory.toUnit (M.X.obj X)))]
          exact GrpObj.right_inv (A.obj X).X } }

/-- Functorial form of `inverseObj`. -/
def inverse : (C ⥤ Grp D) ⥤ Grp (C ⥤ D) where
  obj := inverseObj
  map α := Grp.homMk'
    ((monFunctorCategoryEquivalence C D).inverse.map
      (Functor.whiskerRight α (Grp.forget₂Mon D)))

/-- The ordinary group-valued functor underlying a group object in a
type-valued functor category. -/
def pointwiseGrp (A : Grp (C ⥤ Type u₂)) : C ⥤ GrpCat.{u₂} :=
  functorObj A.X ⋙ GrpTypeEquivalenceGrp.functor

@[simp]
lemma pointwiseGrp_comp_forget (A : Grp (C ⥤ Type u₂)) :
    pointwiseGrp A ⋙ forget GrpCat.{u₂} = A.X := rfl

@[simp]
lemma inverseObj_pointwiseGrp (A : Grp (C ⥤ Type u₂)) :
    inverseObj (pointwiseGrp A ⋙ GrpTypeEquivalenceGrp.inverse) = A := rfl

end CategoryTheory.Monoidal.GrpFunctorCategory

namespace CategoryTheory.NatTrans

variable {C : Type w} [Category.{v} C]
variable {F : C ⥤ Type u} {G : C ⥤ GrpCat.{u}}
  (p : F ⟶ G ⋙ forget GrpCat.{u})

/-- A natural transformation into a group-valued functor is pointwise a subgroup
when it is injective and each component range is the carrier of a subgroup. -/
structure IsPointwiseSubgroup : Type (max u w) where
  injective (X : C) : Function.Injective (p.app X)
  subgroup (X : C) : Subgroup (G.obj X)
  range_eq (X : C) :
    Set.range (p.app X) = (subgroup X : Set (G.obj X : Type u))

namespace IsPointwiseSubgroup

variable {p} (h : NatTrans.IsPointwiseSubgroup p)

lemma mem_range_iff (X : C) (y : G.obj X) :
    y ∈ Set.range (p.app X) ↔ y ∈ h.subgroup X :=
  Set.ext_iff.mp (h.range_eq X) y

def preimage (X : C) (y : h.subgroup X) : F.obj X :=
  Classical.choose ((h.mem_range_iff X y).mpr y.property)

lemma map_preimage (X : C) (y : h.subgroup X) :
    p.app X (h.preimage X y) = y.1 :=
  Classical.choose_spec ((h.mem_range_iff X y).mpr y.property)

/-- The source component is equivalent to its range subgroup. -/
def equivSubgroup (X : C) : F.obj X ≃ h.subgroup X where
  toFun x := ⟨p.app X x, (h.mem_range_iff X _).mp ⟨x, rfl⟩⟩
  invFun := h.preimage X
  left_inv x := h.injective X (h.map_preimage X
    ⟨p.app X x, (h.mem_range_iff X _).mp ⟨x, rfl⟩⟩)
  right_inv y := Subtype.ext (h.map_preimage X y)

@[instance_reducible]
def group (X : C) : Group (F.obj X) :=
  (h.equivSubgroup X).group

lemma map_one (X : C) :
    letI := h.group X
    p.app X (1 : F.obj X) = (1 : G.obj X) := by
  change p.app X ((h.equivSubgroup X).symm (1 : h.subgroup X)) = _
  exact h.map_preimage X (1 : h.subgroup X)

lemma map_mul (X : C) (x y : F.obj X) :
    letI := h.group X
    p.app X (x * y) = p.app X x * p.app X y := by
  change p.app X ((h.equivSubgroup X).symm
    (h.equivSubgroup X x * h.equivSubgroup X y)) = _
  exact h.map_preimage X (h.equivSubgroup X x * h.equivSubgroup X y)

/-- The source functor, equipped objectwise with the transported range-subgroup
group structures. -/
def toGrp : C ⥤ GrpCat.{u} where
  obj X := @GrpCat.of (F.obj X) (h.group X)
  map {X Y} f := by
    letI := h.group X
    letI := h.group Y
    exact GrpCat.ofHom
      { toFun := F.map f
        map_one' := by
          apply h.injective Y
          calc
            p.app Y (F.map f 1) = (G.map f) (p.app X 1) :=
              NatTrans.naturality_apply p f 1
            _ = (G.map f) 1 := by rw [h.map_one X]
            _ = 1 := (G.map f).hom.map_one
            _ = p.app Y 1 := (h.map_one Y).symm
        map_mul' := by
          intro x y
          apply h.injective Y
          calc
            p.app Y (F.map f (x * y)) = (G.map f) (p.app X (x * y)) :=
              NatTrans.naturality_apply p f (x * y)
            _ = (G.map f) (p.app X x * p.app X y) := by rw [h.map_mul X]
            _ = (G.map f) (p.app X x) * (G.map f) (p.app X y) :=
              (G.map f).hom.map_mul _ _
            _ = p.app Y (F.map f x) * p.app Y (F.map f y) := by
              congr 1
              · change (G ⋙ forget GrpCat).map f (p.app X x) = _
                exact (NatTrans.naturality_apply p f x).symm
              · change (G ⋙ forget GrpCat).map f (p.app X y) = _
                exact (NatTrans.naturality_apply p f y).symm
            _ = p.app Y (F.map f x * F.map f y) := (h.map_mul Y _ _).symm }
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change F.map (𝟙 X) x = x
    rw [F.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change F.map (f ≫ g) x = F.map g (F.map f x)
    rw [F.map_comp]
    rfl

/-- The original natural transformation, now as a transformation of
group-valued functors. -/
def inclusion : h.toGrp ⟶ G where
  app X := by
    letI := h.group X
    exact GrpCat.ofHom
      { toFun := p.app X
        map_one' := h.map_one X
        map_mul' := h.map_mul X }
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact NatTrans.naturality_apply p f x

def internalFunctor : C ⥤ Grp (Type u) :=
  h.toGrp ⋙ GrpTypeEquivalenceGrp.inverse

def internalGrp : Grp (C ⥤ Type u) :=
  Monoidal.GrpFunctorCategory.inverseObj h.internalFunctor

/-- The group-object structure on the exact source functor induced by the
pointwise subgroup hypothesis. -/
abbrev grpObj : GrpObj F := h.internalGrp.grp

def targetInternalFunctor : C ⥤ Grp (Type u) :=
  G ⋙ GrpTypeEquivalenceGrp.inverse

def targetInternalGrp : Grp (C ⥤ Type u) :=
  Monoidal.GrpFunctorCategory.inverseObj (targetInternalFunctor (G := G))

def internalInclusion : h.internalGrp ⟶ targetInternalGrp (G := G) :=
  Monoidal.GrpFunctorCategory.inverse.map
    (Functor.whiskerRight h.inclusion GrpTypeEquivalenceGrp.inverse)

/-- With the induced source structure and the pointwise target structure, the
original natural transformation is a morphism of group objects. -/
theorem isMonHom :
    letI : GrpObj F := h.grpObj
    letI : GrpObj (G ⋙ forget GrpCat.{u}) := (targetInternalGrp (G := G)).grp
    IsMonHom p := by
  change IsMonHom h.internalInclusion.hom.hom
  infer_instance

end IsPointwiseSubgroup

end CategoryTheory.NatTrans
