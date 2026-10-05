/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Pointwise quotients of group-valued functors

A natural transformation of group-valued functors whose component ranges are
normal subgroups has a pointwise quotient.  The canonical projection is
pointwise surjective, its component kernels are the original ranges, and it is
the categorical coequalizer of the original transformation and the trivial
transformation.

For a normal morphism of group objects, this constructs the presheaf
`X ↦ G(X) / H(X)`.  No sheaf condition or representability is asserted.

## Main definitions

- `CategoryTheory.NatTrans.IsPointwiseNormal`
- `CategoryTheory.NatTrans.IsPointwiseNormal.quotient`
- `CategoryTheory.NatTrans.IsPointwiseNormal.quotientMk`
- `CategoryTheory.NatTrans.IsPointwiseNormal.quotientCoforkIsColimit`
- `CategoryTheory.IsMonHom.Normal.yonedaQuotient`
- `CategoryTheory.IsMonHom.Normal.yonedaQuotientMap`

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.3 and item 1.4,
  for the algebraic-subgroup and functor-of-points context. The quotients
  here are formed pointwise, without a sheaf or representability claim.
* Mathlib, `Mathlib.GroupTheory.QuotientGroup.Defs` for quotient groups and
  their maps, and `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal` for
  normal morphisms of group objects and their pointwise normal ranges.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]
variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

/-- The natural transformation between group-valued functors whose components
send every element to the identity. -/
def trivialGrp : H ⟶ G where
  app _ := GrpCat.ofHom
    { toFun := fun _ ↦ 1
      map_one' := rfl
      map_mul' := by simp }
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    simp

/-- A natural transformation of group-valued functors is pointwise normal if
the range of every component is a normal subgroup. -/
class IsPointwiseNormal : Prop where
  normal (X : C) : (i.app X).hom.range.Normal

namespace IsPointwiseNormal

variable [h : IsPointwiseNormal i]

instance (X : C) : (i.app X).hom.range.Normal := h.normal X

omit h in
lemma map_range_le (f : X ⟶ Y) :
    (i.app X).hom.range ≤ ((i.app Y).hom.range).comap (G.map f).hom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨H.map f x, ?_⟩
  exact NatTrans.naturality_apply i f x

/-- The pointwise quotient of a group-valued functor by a pointwise normal
transformation. -/
def quotient : Functor C GrpCat.{w} where
  obj X := GrpCat.of (G.obj X ⧸ (i.app X).hom.range)
  map {X Y} f := GrpCat.ofHom <|
    QuotientGroup.map _ _ (G.map f).hom (map_range_le i f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    simp
    rfl

/-- The canonical pointwise quotient map. -/
def quotientMk : G ⟶ quotient i where
  app X := GrpCat.ofHom (QuotientGroup.mk' (i.app X).hom.range)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

lemma quotientMk_app_ker (X : C) :
    ((quotientMk i).app X).hom.ker = (i.app X).hom.range :=
  QuotientGroup.ker_mk' _

lemma quotientMk_app_surjective (X : C) :
    Function.Surjective ((quotientMk i).app X) :=
  QuotientGroup.mk'_surjective _

@[reassoc]
lemma comp_quotientMk : i ≫ quotientMk i = trivialGrp := by
  ext X x
  change (QuotientGroup.mk (i.app X x) :
    (G.obj X : Type w) ⧸ (i.app X).hom.range) = 1
  exact (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

variable {K : Functor C GrpCat.{w}}

/-- A natural transformation that kills the pointwise normal transformation
descends to the pointwise quotient. -/
def quotientLift (f : G ⟶ K)
    (hf : ∀ X, (i.app X).hom.range ≤ (f.app X).hom.ker) :
    quotient i ⟶ K where
  app X := GrpCat.ofHom (QuotientGroup.lift _ (f.app X).hom (hf X))
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    exact NatTrans.naturality_apply f g x

@[reassoc]
lemma quotientMk_comp_quotientLift (f : G ⟶ K)
    (hf : ∀ X, (i.app X).hom.range ≤ (f.app X).hom.ker) :
    quotientMk i ≫ quotientLift i f hf = f := by
  ext X x
  rfl

/-- Two transformations out of the pointwise quotient agree if they agree
after the canonical quotient map. -/
lemma quotient_hom_ext {f g : quotient i ⟶ K}
    (hfg : quotientMk i ≫ f = quotientMk i ≫ g) : f = g := by
  ext X x
  obtain ⟨x, rfl⟩ := quotientMk_app_surjective i X x
  exact congr($(congr_app hfg X) x)

lemma quotientLift_unique (f : G ⟶ K)
    (hf : ∀ X, (i.app X).hom.range ≤ (f.app X).hom.ker)
    (g : quotient i ⟶ K) (hg : quotientMk i ≫ g = f) :
    g = quotientLift i f hf := by
  apply quotient_hom_ext i
  rw [hg, quotientMk_comp_quotientLift]

/-- The pointwise quotient map, as a cofork of the original transformation
and the pointwise trivial transformation. -/
def quotientCofork : Limits.Cofork i trivialGrp :=
  Limits.Cofork.ofπ (quotientMk i) (comp_quotientMk i)

/-- The pointwise quotient is the categorical coequalizer of a pointwise
normal transformation and the pointwise trivial transformation. -/
def quotientCoforkIsColimit : Limits.IsColimit (quotientCofork i) :=
  Limits.Cofork.IsColimit.mk' _ fun s ↦ by
    have hs (X : C) : (i.app X).hom.range ≤ (s.π.app X).hom.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      have h := congr($(congr_app s.condition X) x)
      simpa [trivialGrp] using h
    refine ⟨quotientLift i s.π hs, quotientMk_comp_quotientLift i s.π hs, ?_⟩
    intro m hm
    change quotient i ⟶ s.pt at m
    change quotientMk i ≫ m = s.π at hm
    apply quotient_hom_ext i
    rw [hm, quotientMk_comp_quotientLift]

end IsPointwiseNormal

end CategoryTheory.NatTrans

namespace CategoryTheory.IsMonHom.Normal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj H] [GrpObj G] (i : H ⟶ G) [Normal i]

instance yonedaIsPointwiseNormal :
    NatTrans.IsPointwiseNormal
      (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)) where
  normal X := (normal_iff_normal_monoidHom.mp (inferInstance : Normal i)) (unop X)

/-- The presheaf quotient `X ↦ G(X) / i(H(X))` attached to a normal
morphism of group objects. This construction does not assert that the
presheaf is a sheaf or representable. -/
abbrev yonedaQuotient : Functor Cᵒᵖ GrpCat.{v} :=
  NatTrans.IsPointwiseNormal.quotient
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))

/-- The canonical map from the functor of points of a group object to its
pointwise quotient by a normal subgroup object. -/
abbrev yonedaQuotientMk : yonedaGrpObj G ⟶ yonedaQuotient i :=
  NatTrans.IsPointwiseNormal.quotientMk
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))

lemma yonedaQuotientMk_app_ker (X : C) :
    ((yonedaQuotientMk i).app (op X)).hom.ker = (monoidHom i X).range := by
  have hn :
      ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app
        (op X)).hom.range.Normal := by
    rw [yonedaGrp_map_app, yonedaMon_map_app]
    exact (normal_iff_normal_monoidHom.mp (inferInstance : Normal i)) X
  exact @QuotientGroup.ker_mk' _ _ _ hn

lemma yonedaQuotientMk_app_surjective (X : C) :
    Function.Surjective ((yonedaQuotientMk i).app (op X)) := by
  have hn :
      ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app
        (op X)).hom.range.Normal := by
    rw [yonedaGrp_map_app, yonedaMon_map_app]
    exact (normal_iff_normal_monoidHom.mp (inferInstance : Normal i)) X
  exact @QuotientGroup.mk'_surjective _ _ _ hn

variable {Q : C} [GrpObj Q] (q : G ⟶ Q) [IsMonHom q]

/-- If `H` is the kernel of `q : G ⟶ Q`, then on points the image of
`H ⟶ G` is exactly the kernel of `G ⟶ Q`. -/
lemma monoidHom_range_eq_ker_of_isPullback
    (h : IsPullback i (toUnit H) q η[Q]) (X : C) :
    (monoidHom i X).range = (monoidHom q X).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change (y ≫ i) ≫ q = toUnit X ≫ η[Q]
    rw [Category.assoc, h.w]
    simp
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change x ≫ q = toUnit X ≫ η[Q] at hx
    refine ⟨h.lift x (toUnit X) hx, ?_⟩
    exact h.lift_fst x (toUnit X) hx

/-- The map from the pointwise quotient by a kernel subgroup object to the
functor of points of the target group object. -/
noncomputable def yonedaQuotientMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    yonedaQuotient i ⟶ yonedaGrpObj Q := by
  apply NatTrans.IsPointwiseNormal.quotientLift
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))
    (yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk Q) q))
  intro X
  rw [yonedaGrp_map_app, yonedaMon_map_app, yonedaGrp_map_app, yonedaMon_map_app]
  exact (monoidHom_range_eq_ker_of_isPullback i q h X.unop).le

@[reassoc]
lemma yonedaQuotientMk_comp_quotientMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    yonedaQuotientMk i ≫ yonedaQuotientMap i q h =
      yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk Q) q) := by
  ext X x
  rfl

/-- The map from the pointwise quotient by a kernel subgroup object to the
target functor of points is injective on every object. -/
lemma yonedaQuotientMap_app_injective
    (h : IsPullback i (toUnit H) q η[Q]) (X : C) :
    Function.Injective ((yonedaQuotientMap i q h).app (op X)) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := yonedaQuotientMk_app_surjective i X x
  obtain ⟨y, rfl⟩ := yonedaQuotientMk_app_surjective i X y
  change (X ⟶ G) at x y
  apply (QuotientGroup.eq_iff_div_mem).2
  change x / y ∈ (monoidHom i X).range
  rw [monoidHom_range_eq_ker_of_isPullback i q h X, MonoidHom.mem_ker]
  have hx := ConcreteCategory.congr_hom
    (congr_app (yonedaQuotientMk_comp_quotientMap i q h) (op X)) x
  have hy := ConcreteCategory.congr_hom
    (congr_app (yonedaQuotientMk_comp_quotientMap i q h) (op X)) y
  change (yonedaQuotientMap i q h).app (op X)
      ((yonedaQuotientMk i).app (op X) x) =
    (yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk Q) q)).app (op X) x at hx
  change (yonedaQuotientMap i q h).app (op X)
      ((yonedaQuotientMk i).app (op X) y) =
    (yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk Q) q)).app (op X) y at hy
  have hq := hx.symm.trans (hxy.trans hy)
  rw [yonedaGrp_map_app, yonedaMon_map_app] at hq
  change monoidHom q X x = monoidHom q X y at hq
  rw [(monoidHom q X).map_div, hq]
  simp

end CategoryTheory.IsMonHom.Normal
