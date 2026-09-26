/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Category.Grp.FilteredColimits
public import AlgebraicGroups.GroupObject.Quotient
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Relative fppf quotient sheaves of group schemes

For a normal morphism `i : H ⟶ G` of group schemes over `S`, this file
constructs the group-valued relative fppf sheaf obtained by sheafifying the
pointwise quotient presheaf `X ↦ G(X) / H(X)`. Values are lifted from
`GrpCat.{u}` to `GrpCat.{u + 1}`: this is the universe in which the relative
fppf site of `S : Scheme.{u}` has group-valued sheafification.

The canonical projection is locally surjective, hence an epimorphism of
sheaves. Its pointwise quotient part is componentwise surjective, but no
componentwise surjectivity is asserted after sheafification. The construction
also has the quotient universal property for maps to arbitrary group-valued
relative fppf sheaves which kill `H`.

If `H` is the kernel of an fppf morphism `q : G ⟶ Q`, the quotient sheaf is
represented by `Q`.

## Main definitions

- `AlgebraicGeometry.Scheme.relativeFppfTopology`
- `AlgebraicGeometry.Scheme.relativeFppfYoneda`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotient`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotientMk`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotientLift`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotientMap`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotientMap_isIso`
- `CategoryTheory.IsMonHom.Normal.relativeFppfQuotientIso`
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Scheme

/-- The relative fppf topology on schemes over `S`. -/
abbrev relativeFppfTopology (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

lemma relativeFppfTopology_eq_overGrothendieckTopology (S : Scheme.{u}) :
    relativeFppfTopology S =
      S.overGrothendieckTopology (@Flat ⊓ @LocallyOfFinitePresentation) :=
  rfl

variable {S : Scheme.{u}}

lemma relativeFppfYoneda_isSheaf (G : Over S) [GrpObj G] :
    Presheaf.IsSheaf (relativeFppfTopology S)
      (yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u}) := by
  let _ : (yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat.{u}).IsRepresentable :=
    ⟨G, ⟨yonedaGrpObjRepresentableBy G⟩⟩
  apply (Presheaf.isSheaf_iff_isSheaf_forget
    (J := relativeFppfTopology S)
    (P' := yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u})
    (CategoryTheory.forget GrpCat.{u + 1})).2
  change Presheaf.IsSheaf (relativeFppfTopology S)
    ((yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat.{u}) ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})
  apply (isSheaf_iff_isSheaf_of_type (relativeFppfTopology S) _).2
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := relativeFppfTopology S)
    ((yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat.{u}) ⋙
      CategoryTheory.uliftFunctor.{u + 1, u})

/-- The group-valued relative fppf sheaf represented by a group scheme over `S`,
with values lifted to the universe in which relative fppf sheafification exists. -/
noncomputable def relativeFppfYoneda (G : Over S) [GrpObj G] :
    Sheaf (relativeFppfTopology S) GrpCat.{u + 1} :=
  ⟨yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u}, relativeFppfYoneda_isSheaf G⟩

/-- The underlying lifted natural transformation represented by a homomorphism
of group schemes over `S`. -/
noncomputable abbrev relativeFppfYonedaMapHom
    {G K : Over S} [GrpObj G] [GrpObj K] (f : G ⟶ K) [IsMonHom f] :
    yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶
      yonedaGrpObj K ⋙ GrpCat.uliftFunctor.{u + 1, u} :=
  Functor.whiskerRight
    (yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk K) f))
    GrpCat.uliftFunctor.{u + 1, u}

/-- The morphism of relative fppf sheaves represented by a homomorphism of
group schemes over `S`. -/
noncomputable def relativeFppfYonedaMap
    {G K : Over S} [GrpObj G] [GrpObj K] (f : G ⟶ K) [IsMonHom f] :
    relativeFppfYoneda G ⟶ relativeFppfYoneda K :=
  ⟨relativeFppfYonedaMapHom f⟩

end AlgebraicGeometry.Scheme

namespace CategoryTheory.IsMonHom.Normal

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
variable (i : H ⟶ G) [Normal i]

/-- The group-valued relative fppf quotient sheaf of `G` by the normal subgroup
`H`, obtained by sheafifying the pointwise quotient presheaf. -/
noncomputable def relativeFppfQuotient :
    Sheaf (relativeFppfTopology S) GrpCat.{u + 1} :=
  (presheafToSheaf (relativeFppfTopology S) GrpCat.{u + 1}).obj
    (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})

/-- The pointwise quotient projection, with group values lifted by one universe. -/
noncomputable abbrev relativeFppfQuotientPresheafMk :
    yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶
      yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} :=
  Functor.whiskerRight (yonedaQuotientMk i) GrpCat.uliftFunctor.{u + 1, u}

/-- The canonical projection from the relative functor of points of `G` to its
relative fppf quotient sheaf by `H`. -/
noncomputable def relativeFppfQuotientMk :
    relativeFppfYoneda G ⟶ relativeFppfQuotient i :=
  ⟨relativeFppfQuotientPresheafMk i ≫
    toSheafify (relativeFppfTopology S)
      (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})⟩

lemma relativeFppfQuotientMk_hom :
    (relativeFppfQuotientMk i).hom = relativeFppfQuotientPresheafMk i ≫
      toSheafify (relativeFppfTopology S)
        (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u}) :=
  rfl

lemma relativeFppfQuotientMk_app (X : (Over S)ᵒᵖ) :
    (relativeFppfQuotientMk i).hom.app X =
      (relativeFppfQuotientPresheafMk i).app X ≫
        (toSheafify (relativeFppfTopology S)
          (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})).app X :=
  rfl

/-- The canonical quotient projection kills the given normal subgroup. -/
lemma relativeFppfYonedaMap_comp_relativeFppfQuotientMk :
    relativeFppfYonedaMap i ≫ relativeFppfQuotientMk i =
      ⟨NatTrans.trivialGrp⟩ := by
  apply Sheaf.hom_ext
  ext X x
  rcases x with ⟨x⟩
  change (toSheafify (relativeFppfTopology S)
    (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})).app X
      (ULift.up ((yonedaQuotientMk i).app X
        ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X x))) = 1
  have h := ConcreteCategory.congr_hom
    (congr_app (NatTrans.IsPointwiseNormal.comp_quotientMk
      (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))) X) x
  change (yonedaQuotientMk i).app X
    ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X x) = 1 at h
  rw [h]
  exact (toSheafify (relativeFppfTopology S)
    (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})).app X |>.hom.map_one

lemma relativeFppfQuotientPresheafMk_app_surjective (X : (Over S)ᵒᵖ) :
    Function.Surjective ((relativeFppfQuotientPresheafMk i).app X) := by
  rintro ⟨x⟩
  obtain ⟨y, rfl⟩ := yonedaQuotientMk_app_surjective i X.unop x
  refine ⟨⟨y⟩, ?_⟩
  change ULift.up _ = ULift.up _
  rfl

instance relativeFppfQuotientPresheafMk_epi :
    Epi (relativeFppfQuotientPresheafMk i) := by
  let _ (X : (Over S)ᵒᵖ) : Epi ((relativeFppfQuotientPresheafMk i).app X) :=
    (GrpCat.epi_iff_surjective _).2
      (relativeFppfQuotientPresheafMk_app_surjective i X)
  exact NatTrans.epi_of_epi_app _

instance relativeFppfQuotientMk_isLocallySurjective :
    Sheaf.IsLocallySurjective (relativeFppfQuotientMk i) := by
  dsimp only [Sheaf.IsLocallySurjective, relativeFppfQuotientMk]
  let _ : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMk i) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (relativeFppfQuotientPresheafMk_app_surjective i)
  let _ : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (toSheafify (relativeFppfTopology S)
        (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})) :=
    Presheaf.isLocallySurjective_toSheafify'
      (C := Over S) (D := GrpCat.{u + 1})
      (FD := fun X Y : GrpCat.{u + 1} ↦ X →* Y)
      (CD := fun X : GrpCat.{u + 1} ↦ X)
      (J := relativeFppfTopology S)
      (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})
  exact Presheaf.isLocallySurjective_comp (relativeFppfTopology S)
    (relativeFppfQuotientPresheafMk i)
    (toSheafify (relativeFppfTopology S)
      (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u}))

instance relativeFppfQuotientMk_epi : Epi (relativeFppfQuotientMk i) := by
  apply Sheaf.epi_of_isLocallySurjective

variable {i}

/-- A morphism from the lifted functor of points of `G` that kills `H`
descends to the lifted pointwise quotient presheaf. -/
noncomputable def relativeFppfQuotientPresheafLift
    {F : Functor (Over S)ᵒᵖ GrpCat.{u + 1}}
    (f : yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F)
    (hf : relativeFppfYonedaMapHom i ≫ f = NatTrans.trivialGrp) :
    yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F where
  app X := by
    letI :
        ((yonedaGrp.map
          (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X).hom.range.Normal :=
      (normal_iff_normal_monoidHom.mp (inferInstance : Normal i)) X.unop
    let fX : (yonedaGrp.obj (Grp.mk G)).obj X →* F.obj X :=
      { toFun := fun x ↦ f.app X (ULift.up x)
        map_one' := by
          change f.app X (1 : (yonedaGrpObj G ⋙
            GrpCat.uliftFunctor.{u + 1, u}).obj X) = 1
          exact (f.app X).hom.map_one
        map_mul' := fun x y ↦ by
          change f.app X ((ULift.up x) * (ULift.up y)) =
            f.app X (ULift.up x) * f.app X (ULift.up y)
          exact (f.app X).hom.map_mul (ULift.up x) (ULift.up y) }
    have hfX :
        ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X).hom.range ≤
          fX.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      change f.app X (ULift.up
        ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X x)) = 1
      have h := ConcreteCategory.congr_hom (congr_app hf X) (ULift.up x)
      change f.app X (ULift.up
        ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X x)) = 1 at h
      exact h
    refine GrpCat.ofHom ?_
    change ULift.{u + 1, u}
      ((yonedaGrpObj G).obj X ⧸
        ((yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i)).app X).hom.range) →*
      F.obj X
    exact (QuotientGroup.lift _ fX hfX).comp MulEquiv.ulift.toMonoidHom
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    obtain ⟨x, rfl⟩ := yonedaQuotientMk_app_surjective i X.unop x
    exact NatTrans.naturality_apply f g (ULift.up x)

@[reassoc]
lemma relativeFppfQuotientPresheafMk_comp_lift
    {F : Functor (Over S)ᵒᵖ GrpCat.{u + 1}}
    (f : yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F)
    (hf : relativeFppfYonedaMapHom i ≫ f = NatTrans.trivialGrp) :
    relativeFppfQuotientPresheafMk i ≫
      relativeFppfQuotientPresheafLift f hf = f := by
  ext X x
  rcases x with ⟨x⟩
  change (relativeFppfQuotientPresheafLift f hf).app X
    (ULift.up ((yonedaQuotientMk i).app X x)) = f.app X (ULift.up x)
  change f.app X (ULift.up x) = f.app X (ULift.up x)
  rfl

/-- A map from the pointwise quotient presheaf to a group-valued fppf sheaf
extends canonically across quotient sheafification. -/
noncomputable def relativeFppfQuotientSheafifyLift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F.obj) :
    relativeFppfQuotient i ⟶ F :=
  ⟨sheafifyLift (relativeFppfTopology S) f F.property⟩

@[reassoc]
lemma relativeFppfQuotientMk_comp_relativeFppfQuotientSheafifyLift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F.obj) :
    relativeFppfQuotientMk i ≫ relativeFppfQuotientSheafifyLift f =
      ⟨relativeFppfQuotientPresheafMk i ≫ f⟩ := by
  apply Sheaf.hom_ext
  change (relativeFppfQuotientPresheafMk i ≫
    toSheafify (relativeFppfTopology S)
      (yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u})) ≫
      sheafifyLift (relativeFppfTopology S) f F.property =
    relativeFppfQuotientPresheafMk i ≫ f
  rw [Category.assoc, toSheafify_sheafifyLift]

/-- A morphism from the relative functor of points of `G` to an fppf sheaf
that kills `H` descends canonically to the relative fppf quotient sheaf. -/
noncomputable def relativeFppfQuotientLift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : relativeFppfYoneda G ⟶ F)
    (hf : (relativeFppfYonedaMap i).hom ≫ f.hom = NatTrans.trivialGrp) :
    relativeFppfQuotient i ⟶ F :=
  relativeFppfQuotientSheafifyLift
    (relativeFppfQuotientPresheafLift f.hom hf)

@[reassoc]
lemma relativeFppfQuotientMk_comp_lift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : relativeFppfYoneda G ⟶ F)
    (hf : (relativeFppfYonedaMap i).hom ≫ f.hom = NatTrans.trivialGrp) :
    relativeFppfQuotientMk i ≫ relativeFppfQuotientLift f hf = f := by
  rw [relativeFppfQuotientLift,
    relativeFppfQuotientMk_comp_relativeFppfQuotientSheafifyLift]
  apply Sheaf.hom_ext
  exact relativeFppfQuotientPresheafMk_comp_lift f.hom hf

lemma relativeFppfQuotientLift_unique
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : relativeFppfYoneda G ⟶ F)
    (hf : (relativeFppfYonedaMap i).hom ≫ f.hom = NatTrans.trivialGrp)
    (g : relativeFppfQuotient i ⟶ F)
    (hg : relativeFppfQuotientMk i ≫ g = f) :
    g = relativeFppfQuotientLift f hf := by
  apply (cancel_epi (relativeFppfQuotientMk i)).1
  rw [hg, relativeFppfQuotientMk_comp_lift]

variable {Q : Over S} [GrpObj Q] (q : G ⟶ Q) [IsMonHom q]

/-- The map from the pointwise quotient presheaf by a kernel subgroup scheme
to the lifted relative functor of points of the target. -/
noncomputable def relativeFppfQuotientPresheafMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶
      (relativeFppfYoneda Q).obj :=
  Functor.whiskerRight (yonedaQuotientMap i q h)
    GrpCat.uliftFunctor.{u + 1, u}

lemma relativeFppfQuotientPresheafMap_app_injective
    (h : IsPullback i (toUnit H) q η[Q]) (X : (Over S)ᵒᵖ) :
    Function.Injective ((relativeFppfQuotientPresheafMap q h).app X) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  change ULift.up ((yonedaQuotientMap i q h).app X x) =
    ULift.up ((yonedaQuotientMap i q h).app X y) at hxy
  congr 1
  exact yonedaQuotientMap_app_injective i q h X.unop (ULift.up.inj hxy)

/-- An fppf morphism of group schemes is locally surjective on its relative
functor of points. -/
lemma relativeFppfYonedaMapHom_isLocallySurjective
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfYonedaMapHom q) := by
  constructor
  intro U s
  rcases s with ⟨s⟩
  let R : Sieve Q := Sieve.generate (Presieve.singleton q)
  have hR : R ∈ relativeFppfTopology S Q := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv Q (Sieve.generate (Presieve.singleton q)) ∈
      fppfTopology Q.left
    rw [Sieve.overEquiv_generate]
    have heq : Presieve.functorPushforward (Over.forget S)
        (Presieve.singleton q) =
        (Sieve.generate (Presieve.singleton q.left)).arrows := by
      funext Y f
      apply propext
      constructor
      · rintro ⟨Z, g, h, ⟨⟩, rfl⟩
        exact ⟨G.left, h, q.left, ⟨⟩, rfl⟩
      · rintro ⟨Z, h, g, ⟨⟩, hfac⟩
        exact ⟨G, q, h, ⟨⟩, hfac.symm⟩
    rw [heq, Sieve.generate_sieve]
    exact Precoverage.generate_mem_toGrothendieck
      q.left.singleton_mem_fppfPrecoverage
  apply (relativeFppfTopology S).superset_covering _
    ((relativeFppfTopology S).pullback_stable s hR)
  intro V g hg
  rcases hg with ⟨W, a, b, ⟨⟩, hab⟩
  refine ⟨ULift.up a, ?_⟩
  change ULift.up (a ≫ q) = ULift.up (g ≫ s)
  exact congrArg ULift.up hab

@[reassoc]
lemma relativeFppfQuotientPresheafMk_comp_map
    (h : IsPullback i (toUnit H) q η[Q]) :
    relativeFppfQuotientPresheafMk i ≫
      relativeFppfQuotientPresheafMap q h =
      relativeFppfYonedaMapHom q := by
  ext X x
  rcases x with ⟨x⟩
  rfl

lemma relativeFppfQuotientPresheafMap_isLocallyInjective
    (h : IsPullback i (toUnit H) q η[Q]) :
    Presheaf.IsLocallyInjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMap q h) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (relativeFppfQuotientPresheafMap_app_injective q h)

set_option linter.style.haveILetI false in
lemma relativeFppfQuotientPresheafMap_isLocallySurjective
    (h : IsPullback i (toUnit H) q η[Q])
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMap q h) := by
  have hsurj : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfYonedaMapHom q) :=
    relativeFppfYonedaMapHom_isLocallySurjective q
  rw [← relativeFppfQuotientPresheafMk_comp_map q h] at hsurj
  letI : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMk i ≫
        relativeFppfQuotientPresheafMap q h) := hsurj
  exact Presheaf.isLocallySurjective_of_isLocallySurjective _
    (relativeFppfQuotientPresheafMk i)
    (relativeFppfQuotientPresheafMap q h)

set_option linter.style.haveILetI false in
lemma relativeFppfQuotientPresheafMap_W
    (h : IsPullback i (toUnit H) q η[Q])
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    (relativeFppfTopology S).W (relativeFppfQuotientPresheafMap q h) := by
  letI : Presheaf.IsLocallyInjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMap q h) :=
    relativeFppfQuotientPresheafMap_isLocallyInjective q h
  letI : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfQuotientPresheafMap q h) :=
    relativeFppfQuotientPresheafMap_isLocallySurjective q h
  exact (relativeFppfTopology S).W_of_isLocallyBijective _

/-- The morphism from the relative fppf quotient sheaf by a kernel subgroup
scheme to the represented target sheaf. -/
noncomputable def relativeFppfQuotientMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    relativeFppfQuotient i ⟶ relativeFppfYoneda Q :=
  relativeFppfQuotientSheafifyLift
    (relativeFppfQuotientPresheafMap q h)

@[reassoc]
lemma relativeFppfQuotientMk_comp_map
    (h : IsPullback i (toUnit H) q η[Q]) :
    relativeFppfQuotientMk i ≫ relativeFppfQuotientMap q h =
      relativeFppfYonedaMap q := by
  rw [relativeFppfQuotientMap,
    relativeFppfQuotientMk_comp_relativeFppfQuotientSheafifyLift]
  apply Sheaf.hom_ext
  exact relativeFppfQuotientPresheafMk_comp_map q h

set_option linter.style.haveILetI false in
/-- If `H` is the kernel of an fppf morphism `q : G ⟶ Q`, the induced map
from the relative fppf quotient sheaf to the sheaf represented by `Q` is an
isomorphism. -/
lemma relativeFppfQuotientMap_isIso
    (h : IsPullback i (toUnit H) q η[Q])
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    IsIso (relativeFppfQuotientMap q h) := by
  let f := relativeFppfQuotientPresheafMap q h
  have hw : (relativeFppfTopology S).W f :=
    relativeFppfQuotientPresheafMap_W q h
  letI : IsIso ((presheafToSheaf (relativeFppfTopology S)
      GrpCat.{u + 1}).map f) :=
    ((relativeFppfTopology S).W_iff f).1 hw
  letI : IsIso (sheafifyMap (relativeFppfTopology S) f) := by
    change IsIso ((sheafToPresheaf (relativeFppfTopology S) GrpCat.{u + 1}).map
      ((presheafToSheaf (relativeFppfTopology S) GrpCat.{u + 1}).map f))
    infer_instance
  letI : IsIso (sheafifyLift (relativeFppfTopology S) (𝟙 _)
      (relativeFppfYoneda Q).property) := by
    rw [← isoSheafify_inv]
    infer_instance
  apply (isIso_iff_of_reflects_iso
    (relativeFppfQuotientSheafifyLift f)
    (sheafToPresheaf (relativeFppfTopology S) GrpCat.{u + 1})).1
  change IsIso (sheafifyLift (relativeFppfTopology S) f
    (relativeFppfYoneda Q).property)
  have hcomp : sheafifyMap (relativeFppfTopology S) f ≫
      sheafifyLift (relativeFppfTopology S) (𝟙 _)
        (relativeFppfYoneda Q).property =
      sheafifyLift (relativeFppfTopology S) f
        (relativeFppfYoneda Q).property := by
    simpa only [Category.comp_id] using
      sheafifyMap_sheafifyLift (relativeFppfTopology S) f (𝟙 _)
        (relativeFppfYoneda Q).property
  exact hcomp ▸ inferInstance

/-- The relative fppf quotient sheaf by the kernel of an fppf morphism is
isomorphic to the sheaf represented by its target. -/
noncomputable def relativeFppfQuotientIso
    (h : IsPullback i (toUnit H) q η[Q])
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    relativeFppfQuotient i ≅ relativeFppfYoneda Q := by
  letI := relativeFppfQuotientMap_isIso q h
  exact asIso (relativeFppfQuotientMap q h)

end CategoryTheory.IsMonHom.Normal
