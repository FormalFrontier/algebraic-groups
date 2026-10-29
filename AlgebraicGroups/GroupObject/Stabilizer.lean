/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Stabilizers of sections of internal actions

For a given internal action of a group object `G` on `X`, the stabilizer of a
section `x : 𝟙_ C ⟶ X` is the fibre of the orbit map over `x`. The carrier is the
chosen pullback, not a replacement representing object. Only this pullback is
required. Its operations restrict the original operations on `G`. All actions
use `MonoidalCategory.selfLeftAction`, the tensor action of `C` on itself.

The construction first gives a monoid object. Inversion is then obtained from
`GrpObj.ofInvertible`, using closure of each ordinary stabilizer subgroup of
`T ⟶ G`. The equivalence `stabilizerHomEquiv` describes all test objects and is
natural under precomposition.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G X : C}

section Monoid

variable [MonObj G] [ModObj G X] (x : 𝟙_ C ⟶ X)

variable (G) in
/-- The orbit map of a section for the given internal action. -/
def orbitMap : G ⟶ X := lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]

/-- Evaluation of the orbit map is the original action on generalized points. -/
@[reassoc]
theorem comp_orbitMap {T : C} (g : T ⟶ G) :
    g ≫ orbitMap G x = g • (toUnit T ≫ x) := by
  simp [orbitMap, Hom.smul_def, comp_lift_assoc]

variable [HasPullback (orbitMap G x) x]

variable (G) in
/-- The stabilizer carrier is the chosen fibre of the orbit map over the section. -/
abbrev stabilizer : C := pullback (orbitMap G x) x

variable (G) in
/-- The inclusion of the stabilizer in the acting monoid object. -/
abbrev stabilizerι : stabilizer G x ⟶ G := pullback.fst (orbitMap G x) x

/-- The defining fibre square of the stabilizer. -/
theorem stabilizerIsPullback :
    IsPullback (stabilizerι G x) (toUnit (stabilizer G x)) (orbitMap G x) x := by
  have hs : pullback.snd (orbitMap G x) x = toUnit (stabilizer G x) :=
    isTerminalTensorUnit.hom_ext _ _
  simpa only [stabilizerι, hs] using IsPullback.of_hasPullback (orbitMap G x) x

instance stabilizerι_mono : Mono (stabilizerι G x) := by
  let : Mono x := isTerminalTensorUnit.mono_from x
  dsimp only [stabilizerι]
  infer_instance

/-- Morphisms into the stabilizer are determined by their inclusion in `G`. -/
@[ext]
theorem stabilizer_hom_ext {T : C} {a b : T ⟶ stabilizer G x}
    (h : a ≫ stabilizerι G x = b ≫ stabilizerι G x) : a = b :=
  (cancel_mono (stabilizerι G x)).1 h

/-- The section is fixed by every generalized point of its stabilizer. -/
theorem stabilizer_fixes {T : C} (a : T ⟶ stabilizer G x) :
    (a ≫ stabilizerι G x) • (toUnit T ≫ x) = toUnit T ≫ x := by
  rw [← comp_orbitMap, Category.assoc, (stabilizerIsPullback (G := G) x).w,
    comp_toUnit_assoc]

/-- Lift a generalized point that fixes the section to its stabilizer. -/
def stabilizerLift {T : C} (g : T ⟶ G)
    (hg : g ≫ orbitMap G x = toUnit T ≫ x) : T ⟶ stabilizer G x :=
  pullback.lift g (toUnit T) hg

/-- The lift has the prescribed inclusion. -/
@[reassoc (attr := simp)]
theorem stabilizerLift_ι {T : C} (g : T ⟶ G)
    (hg : g ≫ orbitMap G x = toUnit T ≫ x) :
    stabilizerLift (G := G) x g hg ≫ stabilizerι G x = g := pullback.lift_fst _ _ _

/-- Uniqueness of the lift of a generalized point. -/
theorem stabilizerLift_unique {T : C} (g : T ⟶ G)
    (hg : g ≫ orbitMap G x = toUnit T ≫ x) (a : T ⟶ stabilizer G x)
    (ha : a ≫ stabilizerι G x = g) : a = stabilizerLift (G := G) x g hg := by
  apply stabilizer_hom_ext (G := G) x
  simpa using ha

/-- A generalized point factors uniquely through the stabilizer exactly when it fixes
the section. -/
theorem existsUnique_stabilizerLift_iff {T : C} (g : T ⟶ G) :
    (∃! a : T ⟶ stabilizer G x, a ≫ stabilizerι G x = g) ↔
      g • (toUnit T ≫ x) = toUnit T ≫ x := by
  constructor
  · rintro ⟨a, rfl, _⟩
    exact stabilizer_fixes (G := G) x a
  · intro hg
    have h : g ≫ orbitMap G x = toUnit T ≫ x := by rw [comp_orbitMap, hg]
    exact ⟨stabilizerLift (G := G) x g h, stabilizerLift_ι (G := G) x g h,
      fun a ha ↦ stabilizerLift_unique (G := G) x g h a ha⟩

/-- The monoid structure obtained by restricting the original unit and multiplication. -/
noncomputable instance stabilizerMonObj : MonObj (stabilizer G x) where
  one := stabilizerLift (G := G) x 1 (by rw [comp_orbitMap, _root_.one_smul])
  mul := stabilizerLift (G := G) x
    ((fst _ _ ≫ stabilizerι G x) * (snd _ _ ≫ stabilizerι G x)) (by
      rw [comp_orbitMap, SemigroupAction.mul_smul, stabilizer_fixes, stabilizer_fixes])
  one_mul := by
    apply (cancel_mono (stabilizerι G x)).1
    simp [Category.assoc, MonObj.comp_mul, leftUnitor_hom]
  mul_one := by
    apply (cancel_mono (stabilizerι G x)).1
    simp [Category.assoc, MonObj.comp_mul, rightUnitor_hom]
  mul_assoc := by
    apply (cancel_mono (stabilizerι G x)).1
    simp [Category.assoc, MonObj.comp_mul, _root_.mul_assoc]

/-- The stabilizer unit is the original unit of the acting monoid. -/
@[reassoc]
theorem stabilizer_one_ι : η[stabilizer G x] ≫ stabilizerι G x = η[G] := by
  have h : η[stabilizer G x] ≫ stabilizerι G x = (1 : 𝟙_ C ⟶ G) :=
    pullback.lift_fst _ _ _
  simpa [Hom.one_def] using h

/-- The stabilizer multiplication restricts the original multiplication. -/
@[reassoc]
theorem stabilizer_mul_ι : μ[stabilizer G x] ≫ stabilizerι G x =
    (stabilizerι G x ⊗ₘ stabilizerι G x) ≫ μ[G] := by
  have h : μ[stabilizer G x] ≫ stabilizerι G x =
      (fst _ _ ≫ stabilizerι G x) * (snd _ _ ≫ stabilizerι G x) :=
    pullback.lift_fst _ _ _
  rw [h, Hom.mul_def]
  congr 1
  ext <;> simp

instance stabilizerι_isMonHom : IsMonHom (stabilizerι G x) where
  one_hom := stabilizer_one_ι (G := G) x
  mul_hom := stabilizer_mul_ι (G := G) x

/-- A monoid morphism fixing the section lifts as a monoid morphism. -/
instance stabilizerLift_isMonHom {H : C} [MonObj H] (f : H ⟶ G) [IsMonHom f]
    (hf : f ≫ orbitMap G x = toUnit H ≫ x) : IsMonHom (stabilizerLift (G := G) x f hf) where
  one_hom := by
    apply (cancel_mono (stabilizerι G x)).1
    simp [Category.assoc]
  mul_hom := by
    apply (cancel_mono (stabilizerι G x)).1
    simp only [Category.assoc, stabilizerLift_ι, IsMonHom.mul_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp

end Monoid

section Group

variable [GrpObj G] [ModObj G X] (x : 𝟙_ C ⟶ X)
  [HasPullback (orbitMap G x) x]

/-- The stabilizer group structure on the same chosen pullback carrier. -/
noncomputable instance stabilizerGrpObj : GrpObj (stabilizer G x) :=
  GrpObj.ofInvertible _ (by
    intro T a
    have ha : a ≫ stabilizerι G x ∈
        MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x) := stabilizer_fixes (G := G) x a
    have hi := (MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)).inv_mem ha
    change (a ≫ stabilizerι G x)⁻¹ • (toUnit T ≫ x) = toUnit T ≫ x at hi
    rw [← comp_orbitMap] at hi
    let b : T ⟶ stabilizer G x := stabilizerLift (G := G) x (a ≫ stabilizerι G x)⁻¹ hi
    have hb : b ≫ stabilizerι G x = (a ≫ stabilizerι G x)⁻¹ :=
      stabilizerLift_ι (G := G) x _ hi
    refine ⟨b, ?_, ?_⟩
    · apply stabilizer_hom_ext (G := G) x
      rw [MonObj.mul_comp, hb, MonObj.one_comp, inv_mul_cancel]
    · apply stabilizer_hom_ext (G := G) x
      rw [MonObj.mul_comp, hb, MonObj.one_comp, mul_inv_cancel])

/-- Inversion in the stabilizer is the restriction of the original inversion. -/
@[reassoc]
theorem stabilizer_inv_ι : ι[stabilizer G x] ≫ stabilizerι G x = stabilizerι G x ≫ ι[G] :=
  GrpObj.inv_hom _

/-- The generalized points of the stabilizer are the ordinary stabilizer subgroup,
with their original Hom group and Hom action. -/
noncomputable def stabilizerHomEquiv (T : C) :
    (T ⟶ stabilizer G x) ≃* MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x) where
  toFun a := ⟨a ≫ stabilizerι G x, stabilizer_fixes (G := G) x a⟩
  invFun g := stabilizerLift (G := G) x g.val (by rw [comp_orbitMap]; exact g.property)
  left_inv a := by
    apply stabilizer_hom_ext (G := G) x
    simp
  right_inv g := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    exact MonObj.mul_comp a b (stabilizerι G x)

/-- Applying the pointwise equivalence is composition with the inclusion. -/
@[simp]
theorem stabilizerHomEquiv_apply (T : C) (a : T ⟶ stabilizer G x) :
    (stabilizerHomEquiv (G := G) x T a).val = a ≫ stabilizerι G x := rfl

/-- The inverse pointwise equivalence has the prescribed inclusion. -/
@[simp]
theorem stabilizerHomEquiv_symm_apply_ι (T : C)
    (g : MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)) :
    (stabilizerHomEquiv (G := G) x T).symm g ≫ stabilizerι G x = g.val := by
  exact stabilizerLift_ι _ _ _

/-- Precomposition on ordinary stabilizer subgroups. -/
def stabilizerPrecomp {T T' : C} (f : T' ⟶ T) :
    MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x) →*
      MulAction.stabilizer (T' ⟶ G) (toUnit T' ≫ x) where
  toFun g := ⟨f ≫ g.val, by
    have h := congrArg (fun z ↦ f ≫ z) g.property
    simpa only [MulAction.mem_stabilizer_iff, comp_smul, comp_toUnit_assoc] using h⟩
  map_one' := by apply Subtype.ext; exact MonObj.comp_one f
  map_mul' a b := by apply Subtype.ext; exact MonObj.comp_mul f a.val b.val

omit [HasPullback (orbitMap G x) x] in
/-- Precomposition on stabilizers has the usual underlying function. -/
@[simp]
theorem stabilizerPrecomp_apply {T T' : C} (f : T' ⟶ T)
    (g : MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)) :
    (stabilizerPrecomp (G := G) x f g).val = f ≫ g.val := rfl

omit [HasPullback (orbitMap G x) x] in
/-- Precomposition by an identity acts identically on the stabilizer subgroup. -/
@[simp]
theorem stabilizerPrecomp_id (T : C) :
    stabilizerPrecomp (G := G) x (𝟙 T) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  simp

omit [HasPullback (orbitMap G x) x] in
/-- Precomposition on stabilizer subgroups respects composition. -/
theorem stabilizerPrecomp_comp {T T' T'' : C} (f : T'' ⟶ T') (g : T' ⟶ T) :
    stabilizerPrecomp (G := G) x (f ≫ g) =
      (stabilizerPrecomp (G := G) x f).comp (stabilizerPrecomp (G := G) x g) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  simp

/-- The pointwise stabilizer equivalence is natural for every precomposition. -/
theorem stabilizerHomEquiv_natural {T T' : C} (f : T' ⟶ T)
    (a : T ⟶ stabilizer G x) :
    stabilizerHomEquiv (G := G) x T' (f ≫ a) =
      stabilizerPrecomp (G := G) x f (stabilizerHomEquiv (G := G) x T a) := by
  apply Subtype.ext
  simp

/-- The inclusion as a morphism of bundled group objects. -/
@[simps!]
def stabilizerιHom : Grp.mk (stabilizer G x) ⟶ Grp.mk G := Grp.homMk (stabilizerι G x)

/-- The group-homomorphism lift of a group homomorphism fixing the section. -/
@[simps!]
def stabilizerLiftHom (H : Grp C) (f : H ⟶ Grp.mk G)
    (hf : f.hom.hom ≫ orbitMap G x = toUnit H.X ≫ x) : H ⟶ Grp.mk (stabilizer G x) :=
  Grp.homMk (stabilizerLift (G := G) x f.hom.hom hf)

/-- The group-homomorphism lift factors the given homomorphism. -/
@[reassoc (attr := simp)]
theorem stabilizerLiftHom_ι (H : Grp C) (f : H ⟶ Grp.mk G)
    (hf : f.hom.hom ≫ orbitMap G x = toUnit H.X ≫ x) :
    stabilizerLiftHom (G := G) x H f hf ≫ stabilizerιHom (G := G) x = f := by
  ext
  exact stabilizerLift_ι (G := G) x _ _

/-- A group homomorphism fixing the section has a unique group-homomorphism lift. -/
theorem existsUnique_stabilizerLiftHom (H : Grp C) (f : H ⟶ Grp.mk G)
    (hf : f.hom.hom ≫ orbitMap G x = toUnit H.X ≫ x) :
    ∃! a : H ⟶ Grp.mk (stabilizer G x), a ≫ stabilizerιHom (G := G) x = f := by
  refine ⟨stabilizerLiftHom (G := G) x H f hf, stabilizerLiftHom_ι (G := G) x H f hf, ?_⟩
  intro a ha
  ext
  have h := congrArg (fun b : H ⟶ Grp.mk G ↦ b.hom.hom) ha
  simpa using h

end Group

section Regular

variable [MonObj G]

attribute [local instance] ModObj.regular

/-- For the existing regular action, the orbit of the unit is the identity. -/
@[simp]
theorem regular_orbitMap_one : orbitMap G (η[G]) = 𝟙 G := by
  change lift (𝟙 G) (toUnit G ≫ η[G]) ≫ μ[G] = 𝟙 G
  exact lift_comp_one_right _ _

instance regularOrbitMap_isIso : IsIso (orbitMap G (η[G])) := by
  rw [regular_orbitMap_one]
  infer_instance

attribute [local instance] hasPullback_of_left_iso

/-- The unit stabilizer of the regular action is the terminal object.

This uses the given regular-action construction, and the same pullback carrier
and inclusion as the general stabilizer construction. -/
def regularStabilizerUnitIso : stabilizer G (η[G]) ≅ 𝟙_ C :=
  asIso (pullback.snd (orbitMap G (η[G])) (η[G]))

/-- Under the regular-action unit-stabilizer isomorphism, the inclusion is the unit. -/
@[reassoc (attr := simp)]
theorem regularStabilizerUnitIso_hom_one :
    (regularStabilizerUnitIso (G := G)).hom ≫ η[G] = stabilizerι G (η[G]) := by
  simpa [regularStabilizerUnitIso, regular_orbitMap_one] using
    (pullback.condition (f := orbitMap G (η[G])) (g := η[G])).symm

end Regular

end CategoryTheory.ModObj
