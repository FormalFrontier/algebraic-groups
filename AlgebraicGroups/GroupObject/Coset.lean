/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Quotient
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Pointwise cosets of group-valued functors

A natural transformation `i : H ⟶ G` of group-valued functors determines a
type-valued functor of left cosets `X ↦ G(X) / i(H(X))`, without any normality
hypothesis. The canonical map is pointwise surjective.

No sheaf condition or representability is asserted here.

## Main definitions

- `CategoryTheory.NatTrans.coset`
- `CategoryTheory.NatTrans.cosetMk`
- `CategoryTheory.IsMonHom.yonedaCoset`
- `CategoryTheory.IsMonHom.yonedaCosetMk`

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.3 and item 1.4,
  for algebraic subgroups and their functors of points. This file constructs
  pointwise cosets, without a representability or sheafification assertion.
* Mathlib, `QuotientGroup.leftRel` for left cosets and the group-object
  Yoneda construction in `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
  Functoriality uses `Quotient.map'` to descend maps to coset types.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]
variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

private lemma map_range_le (f : X ⟶ Y) :
    (i.app X).hom.range ≤ ((i.app Y).hom.range).comap (G.map f).hom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨H.map f x, ?_⟩
  exact NatTrans.naturality_apply i f x

/-- The pointwise left-coset type of a natural transformation of group-valued
functors. Normality is not required. -/
def coset : Functor C (Type w) where
  obj X := G.obj X ⧸ (i.app X).hom.range
  map {X Y} f := ↾(
    @Quotient.map' _ _
      (QuotientGroup.leftRel (i.app X).hom.range)
      (QuotientGroup.leftRel (i.app Y).hom.range)
      (G.map f) fun x y hxy ↦ by
        rw [QuotientGroup.leftRel_apply] at hxy ⊢
        simpa only [Subgroup.mem_comap, map_inv, map_mul] using map_range_le i f hxy)
  map_id X := by
    ext x
    induction x using Quotient.inductionOn'
    simp
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn'
    simp

/-- The canonical pointwise map from a group-valued functor to its coset
functor. -/
def cosetMk : G ⋙ CategoryTheory.forget GrpCat.{w} ⟶ coset i where
  app X := ↾Quotient.mk''
  naturality X Y f := by
    ext x
    rfl

lemma cosetMk_app_surjective (X : C) : Function.Surjective ((cosetMk i).app X) :=
  @Quotient.mk''_surjective _ (QuotientGroup.leftRel (i.app X).hom.range)

variable {K : Functor C (Type w)}

/-- A natural transformation out of `G` which is constant on the left cosets
of `i(H)` descends to the pointwise coset functor. -/
def cosetLift (f : G ⋙ CategoryTheory.forget GrpCat.{w} ⟶ K)
    (hf : ∀ X x y, QuotientGroup.leftRel (i.app X).hom.range x y →
      f.app X x = f.app X y) :
    coset i ⟶ K where
  app X := ↾(fun x ↦ x.liftOn' (f.app X) (hf X))
  naturality X Y g := by
    ext x
    induction x using Quotient.inductionOn'
    exact NatTrans.naturality_apply f g _

@[reassoc]
lemma cosetMk_comp_cosetLift (f : G ⋙ CategoryTheory.forget GrpCat.{w} ⟶ K)
    (hf : ∀ X x y, QuotientGroup.leftRel (i.app X).hom.range x y →
      f.app X x = f.app X y) :
    cosetMk i ≫ cosetLift i f hf = f := by
  ext X x
  rfl

/-- Two transformations out of a pointwise coset functor agree if they agree
after the canonical quotient map. -/
lemma coset_hom_ext {f g : coset i ⟶ K}
    (hfg : cosetMk i ≫ f = cosetMk i ≫ g) : f = g := by
  ext X x
  obtain ⟨x, rfl⟩ := cosetMk_app_surjective i X x
  exact congr($(congr_app hfg X) x)

end CategoryTheory.NatTrans

namespace CategoryTheory.IsMonHom

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]

/-- The presheaf of pointwise left cosets `X ↦ G(X) / i(H(X))` attached to
a morphism of group objects. This construction does not assert a sheaf
condition or representability. -/
abbrev yonedaCoset : Functor Cᵒᵖ (Type v) :=
  NatTrans.coset
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))

/-- The canonical map from the functor of points of a group object to its
pointwise left-coset functor. -/
abbrev yonedaCosetMk :
    yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat.{v} ⟶ yonedaCoset i :=
  NatTrans.cosetMk
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))

lemma yonedaCosetMk_app_surjective (X : C) :
    Function.Surjective ((yonedaCosetMk i).app (op X)) :=
  NatTrans.cosetMk_app_surjective _ (op X)

variable {Q : C} (q : G ⟶ Q)

/-- The represented map `yoneda.map q` is constant on pointwise left cosets
when the right-action square is a pullback. -/
lemma yonedaCosetMap_rel
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q) :
    ∀ (X : Cᵒᵖ) x y,
      QuotientGroup.leftRel
        (((yonedaGrp.map
          (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X).hom.range) x y →
      (yoneda.map q).app X x = (yoneda.map q).app X y := by
  intro X x y hxy
  rw [QuotientGroup.leftRel_apply] at hxy
  rw [yonedaGrp_map_app, yonedaMon_map_app] at hxy
  rcases hxy with ⟨a, ha⟩
  change X.unop ⟶ G at x y
  change X.unop ⟶ H at a
  change x ≫ q = y ≫ q
  have hy : y = x * (a ≫ i) := (inv_mul_eq_iff_eq_mul).1 ha.symm
  calc
    x ≫ q = (lift x a ≫ fst G H) ≫ q := by rw [lift_fst]
    _ = lift x a ≫ (fst G H ≫ q) := Category.assoc _ _ _
    _ = lift x a ≫ (((𝟙 G ⊗ₘ i) ≫ μ[G]) ≫ q) := by rw [h.w]
    _ = (lift x a ≫ ((𝟙 G ⊗ₘ i) ≫ μ[G])) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = (x * (a ≫ i)) ≫ q := by
      congr 1
      rw [← Category.assoc, lift_map, Hom.mul_def]
      simp
    _ = y ≫ q := by rw [← hy]

/-- A morphism `q : G ⟶ Q` whose self-pullback is the right action of `H`
induces a map from the pointwise left-coset presheaf to the functor represented
by `Q`. The target need not carry a group structure. -/
noncomputable def yonedaCosetMap
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q) :
    yonedaCoset i ⟶ yoneda.obj Q :=
  NatTrans.cosetLift _ (yoneda.map q) (yonedaCosetMap_rel i q h)

@[reassoc]
lemma yonedaCosetMk_comp_yonedaCosetMap
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q) :
    yonedaCosetMk i ≫ yonedaCosetMap i q h = yoneda.map q :=
  NatTrans.cosetMk_comp_cosetLift _ _ _

/-- The map from the pointwise left-coset presheaf to `Q` is pointwise
injective when the right-action square presents the self-pullback of `q`. -/
lemma yonedaCosetMap_app_injective
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q) (X : C) :
    Function.Injective ((yonedaCosetMap i q h).app (op X)) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := yonedaCosetMk_app_surjective i X x
  obtain ⟨y, rfl⟩ := yonedaCosetMk_app_surjective i X y
  change X ⟶ G at x y
  change (@Quotient.mk'' (X ⟶ G)
      (QuotientGroup.leftRel (monoidHom i X).range) x) =
    @Quotient.mk'' (X ⟶ G)
      (QuotientGroup.leftRel (monoidHom i X).range) y
  change x ≫ q = y ≫ q at hxy
  apply Quotient.sound
  change QuotientGroup.leftRel (monoidHom i X).range x y
  rw [QuotientGroup.leftRel_apply]
  let l : X ⟶ G ⊗ H := h.lift x y hxy
  refine ⟨l ≫ snd G H, ?_⟩
  change (l ≫ snd G H) ≫ i = x⁻¹ * y
  apply (eq_inv_mul_iff_mul_eq).2
  calc
    x * ((l ≫ snd G H) ≫ i) =
        (l ≫ fst G H) * ((l ≫ snd G H) ≫ i) := by rw [h.lift_fst]
    _ = l ≫ ((𝟙 G ⊗ₘ i) ≫ μ[G]) := by
      rw [Hom.mul_def, ← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    _ = y := h.lift_snd x y hxy

end CategoryTheory.IsMonHom
