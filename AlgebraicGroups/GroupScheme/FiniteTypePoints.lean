/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Sites.Affine
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Functors of points on finite-type affine tests

This file identifies finitely generated algebras over a field, oppositely, with affine schemes
locally of finite type over that field. It proves that these affine tests are dense among schemes
locally of finite type over the field and derives full faithfulness of the resulting restricted
functor of points, including for group objects.

## Main results

- `AlgebraicGeometry.fgAlgCatOpEquivLftAffineOver`
- `AlgebraicGeometry.finiteAlgSpecOver_isDense`
- `AlgebraicGeometry.algebraicOverPointsFullyFaithful`
- `AlgebraicGeometry.lftGroupPointsFullyFaithful`
- `AlgebraicGeometry.lftGroupPoints_essImage_iff`
- `AlgebraicGeometry.algebraicGroupPoints_essImage_iff`
-/

public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

section CoverDense

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- A fully faithful, locally full, cover-dense functor into a subcanonical site is dense. -/
theorem Functor.isDense_of_isCoverDense_of_subcanonical
    (G : C ⥤ D) (J : GrothendieckTopology D)
    [G.Full] [G.IsCoverDense J] [G.IsLocallyFull J] [J.Subcanonical] :
    G.IsDense := by
  apply Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda
  exact ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (Presheaf.restrictedULiftYoneda.{0} G)).mpr (fun X Y ↦ by
      have h₁ := (ULiftYoneda.fullyFaithful D).map_bijective X Y
      have h₂ := Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G
          ((CategoryTheory.uliftYoneda.{0} (C := D)).obj X)
          ((CategoryTheory.uliftYoneda.{0} (C := D)).obj Y)
          (by
            rw [isSheaf_iff_isSheaf_of_type]
            exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
      change Function.Bijective (fun f : X ⟶ Y ↦
        ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v₂)).obj G.op).map
          ((CategoryTheory.uliftYoneda.{0} (C := D)).map f))
      exact h₂.comp h₁)).some

end CoverDense

end CategoryTheory

namespace AlgebraicGeometry

/-- The morphism property of being locally of finite type, with its universe made explicit. -/
abbrev locallyFiniteTypeMorphism : MorphismProperty Scheme.{u} :=
  @LocallyOfFiniteType

/-- The morphism property of being an open immersion, with its universe made explicit. -/
abbrev openImmersionMorphism : MorphismProperty Scheme.{u} :=
  @IsOpenImmersion

/-- An open immersion is locally of finite type. -/
lemma openImmersionMorphism_le_locallyFiniteTypeMorphism :
    openImmersionMorphism ≤ locallyFiniteTypeMorphism := by
  intro X Y f hf
  let _ : IsOpenImmersion f := hf
  infer_instance

/-- Local finite type can be cancelled from a composite on the right. -/
instance : locallyFiniteTypeMorphism.HasOfPostcompProperty locallyFiniteTypeMorphism where
  of_postcomp f g _ hfg := by
    let _ : LocallyOfFiniteType (f ≫ g) := hfg
    exact locallyOfFiniteType_of_comp f g

/-- Affine schemes locally of finite type over a field. -/
abbrev lftAffineOver (K : Type u) [Field K] :=
  (locallyFiniteTypeMorphism.CostructuredArrow ⊤ Scheme.Spec (Spec (.of K)))

/-- The small Zariski topology on schemes locally of finite type over a field. -/
noncomputable abbrev lftZariskiTopology (K : Type u) [Field K] :
    GrothendieckTopology (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  Scheme.smallGrothendieckTopology (P := openImmersionMorphism)
    (Q := locallyFiniteTypeMorphism) (Spec (.of K))

/-- The affine spectrum over a field, restricted to finitely generated algebras. -/
@[implicit_reducible] noncomputable def finiteAlgSpec
    (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ⥤ Over (Spec (.of K)) :=
  (ObjectProperty.ι _).op ⋙ algSpec (.of K)

/-- The affine spectrum functor on finitely generated algebras is fully faithful. -/
noncomputable def finiteAlgSpecFullyFaithful
    (K : Type u) [Field K] : (finiteAlgSpec K).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).op.comp algSpec.fullyFaithful

/-- The spectrum of a finitely generated algebra as a locally-finite-type scheme over its field. -/
@[implicit_reducible] noncomputable def finiteAlgSpecOver
    (K : Type u) [Field K] :
    (FGAlgCat K)ᵒᵖ ⥤ locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)) where
  obj A := MorphismProperty.Over.mk ⊤ ((algSpec (.of K)).obj
    ((ObjectProperty.ι _).op.obj A)).hom (by
      change LocallyOfFiniteType (Spec (.of A.unop.obj) ↘ Spec (.of K))
      infer_instance)
  map f := MorphismProperty.Over.Hom.mk
    ((algSpec (.of K)).map ((ObjectProperty.ι _).op.map f)) trivial

/-- The locally-finite-type refinement of finite-algebra spectrum is fully faithful. -/
noncomputable def finiteAlgSpecOverFullyFaithful
    (K : Type u) [Field K] : (finiteAlgSpecOver K).FullyFaithful where
  preimage f := (finiteAlgSpecFullyFaithful K).preimage f.hom
  map_preimage f := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg CategoryTheory.Over.Hom.left
      ((finiteAlgSpecFullyFaithful K).map_preimage f.hom)
  preimage_map f := (finiteAlgSpecFullyFaithful K).preimage_map f

/-- The inclusion of affine locally-finite-type schemes into all locally-finite-type schemes over a
field. -/
@[implicit_reducible] noncomputable def lftAffineInclusion
    (K : Type u) [Field K] :
    lftAffineOver K ⥤ locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)) :=
  MorphismProperty.CostructuredArrow.toOver
    locallyFiniteTypeMorphism Scheme.Spec (Spec (.of K))

/-- The inclusion of affine locally-finite-type schemes is fully faithful. -/
noncomputable def lftAffineInclusionFullyFaithful
    (K : Type u) [Field K] : (lftAffineInclusion K).FullyFaithful where
  preimage f := MorphismProperty.CostructuredArrow.homMk
    (Spec.fullyFaithful.preimage f.left) trivial (by
      have hmap : Scheme.Spec.map (Spec.fullyFaithful.preimage
          (show Scheme.Spec.obj _ ⟶ Scheme.Spec.obj _ from f.left)) = f.left :=
        Spec.fullyFaithful.map_preimage f.left
      rw [hmap]
      exact f.w)
  map_preimage f := by
    apply MorphismProperty.Over.Hom.ext
    exact Spec.fullyFaithful.map_preimage f.left
  preimage_map f := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact Spec.fullyFaithful.preimage_map f.left

local instance (K : Type u) [Field K] : (lftAffineInclusion K).Full :=
  (lftAffineInclusionFullyFaithful K).full

local instance (K : Type u) [Field K] : (lftAffineInclusion K).Faithful :=
  (lftAffineInclusionFullyFaithful K).faithful

/-- Affine locally-finite-type schemes are cover-dense for the small Zariski topology. -/
instance lftAffineInclusion_isCoverDense
    (K : Type u) [Field K] :
    (lftAffineInclusion K).IsCoverDense (lftZariskiTopology K) where
  is_cover U := by
    change Sieve.coverByImage (lftAffineInclusion K) U ∈
      Scheme.smallGrothendieckTopology (P := openImmersionMorphism)
        (Q := locallyFiniteTypeMorphism) (Spec (.of K)) U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
      (Spec (.of K)) openImmersionMorphism_le_locallyFiniteTypeMorphism,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    let 𝒰 := U.left.affineCover
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    have hi : locallyFiniteTypeMorphism (𝒰.f i) :=
      openImmersionMorphism_le_locallyFiniteTypeMorphism _ (𝒰.map_prop i)
    have hcomp : locallyFiniteTypeMorphism (𝒰.f i ≫ U.hom) :=
      locallyFiniteTypeMorphism.comp_mem _ _ hi U.prop
    let A := Scheme.affineOverMk (𝒰.f i ≫ U.hom) hcomp
    let f : (lftAffineInclusion K).obj A ⟶ U :=
      MorphismProperty.Over.homMk (𝒰.f i) (by rfl)
    refine ⟨_, f, y, ?_, 𝒰.map_prop i, hy⟩
    exact Presieve.in_coverByImage _ f

local instance lftOver_locallyCoverDense
    (K : Type u) [Field K] :
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))).LocallyCoverDense
      (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K))) :=
  Scheme.locallyCoverDense_of_le (Spec (.of K))
    openImmersionMorphism_le_locallyFiniteTypeMorphism

local instance lftOver_representablyFlat
    (K : Type u) [Field K] :
    RepresentablyFlat
      (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))) :=
  flat_of_preservesFiniteLimits _

local instance lftOver_isContinuous
    (K : Type u) [Field K] :
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))).IsContinuous
      (lftZariskiTopology K)
      (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K))) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K)))
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))

local instance lftZariskiTopology_subcanonical
    (K : Type u) [Field K] : (lftZariskiTopology K).Subcanonical := by
  change ((MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))).restrictedTopology
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))).Subcanonical
  apply GrothendieckTopology.subcanonical_of_full_of_faithful
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K)))
    (lftZariskiTopology K)
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))

/-- Affine locally-finite-type schemes are categorically dense among locally-finite-type schemes
over a field. -/
theorem lftAffineInclusion_isDense
    (K : Type u) [Field K] : (lftAffineInclusion K).IsDense :=
  Functor.isDense_of_isCoverDense_of_subcanonical (lftAffineInclusion K)
    (lftZariskiTopology K)

/-- Each finite-algebra spectrum belongs to the essential image of the affine inclusion. -/
lemma finiteAlgSpecOver_mem_lftAffineInclusion
    (K : Type u) [Field K] (A : (FGAlgCat K)ᵒᵖ) :
    (lftAffineInclusion K).essImage ((finiteAlgSpecOver K).obj A) := by
  let U : lftAffineOver K := Scheme.affineOverMk
    ((finiteAlgSpec K).obj A).hom ((finiteAlgSpecOver K).obj A).prop
  exact ⟨U, ⟨Iso.refl _⟩⟩

/-- The factorization of finite-algebra spectrum through affine locally-finite-type schemes. -/
@[implicit_reducible] noncomputable def fgAlgToLftAffine
    (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ⥤ lftAffineOver K :=
  Functor.essImage.liftFunctor (finiteAlgSpecOver K) (lftAffineInclusion K)
    (finiteAlgSpecOver_mem_lftAffineInclusion K)

/-- Factoring through affine locally-finite-type schemes recovers finite-algebra spectrum. -/
noncomputable def fgAlgToLftAffineCompIso
    (K : Type u) [Field K] :
    fgAlgToLftAffine K ⋙ lftAffineInclusion K ≅ finiteAlgSpecOver K :=
  Functor.essImage.liftFunctorCompIso (finiteAlgSpecOver K)
    (lftAffineInclusion K) (finiteAlgSpecOver_mem_lftAffineInclusion K)

/-- The factorization of finite-algebra spectrum is fully faithful. -/
noncomputable def fgAlgToLftAffineFullyFaithful
    (K : Type u) [Field K] : (fgAlgToLftAffine K).FullyFaithful := by
  have hcomp :
      (fgAlgToLftAffine K ⋙ lftAffineInclusion K).FullyFaithful :=
    (finiteAlgSpecOverFullyFaithful K).ofIso
      (fgAlgToLftAffineCompIso K).symm
  exact hcomp.ofCompFaithful

/-- Every affine locally-finite-type scheme over a field is the spectrum of a finitely generated
algebra. -/
lemma finiteAlgSpecOver_covers_affine
    (K : Type u) [Field K] (U : lftAffineOver K) :
    (finiteAlgSpecOver K).essImage
      ((MorphismProperty.CostructuredArrow.toOver
        locallyFiniteTypeMorphism Scheme.Spec (Spec (.of K))).obj U) := by
  let φ := Spec.preimage U.hom
  have hφ : RingHom.FiniteType φ.hom := by
    have h := U.prop
    change LocallyOfFiniteType U.hom at h
    rw [← Spec.map_preimage U.hom,
      HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact h
  let _ : Algebra K U.left.unop := φ.hom.toAlgebra
  have hft : Algebra.FiniteType K U.left.unop := by
    rw [← RingHom.finiteType_algebraMap]
    exact hφ
  let A : FGAlgCat K := ⟨CommAlgCat.of K U.left.unop, hft⟩
  refine ⟨.op A, ⟨MorphismProperty.Over.isoMk (Iso.refl _) ?_⟩⟩
  change 𝟙 (Spec U.left.unop) ≫ U.hom =
    Spec.map (CommRingCat.ofHom (algebraMap K U.left.unop))
  rw [Category.id_comp]
  change U.hom = Spec.map φ
  exact (Spec.map_preimage U.hom).symm

/-- The factorization of finite-algebra spectrum is essentially surjective. -/
theorem fgAlgToLftAffineEssSurj
    (K : Type u) [Field K] : (fgAlgToLftAffine K).EssSurj where
  mem_essImage U := by
    obtain ⟨A, ⟨e⟩⟩ := finiteAlgSpecOver_covers_affine K U
    refine ⟨A, ⟨(lftAffineInclusionFullyFaithful K).preimageIso ?_⟩⟩
    exact (fgAlgToLftAffineCompIso K).app A ≪≫ e

/-- Finitely generated algebras over a field, oppositely, are equivalent to affine
locally-finite-type schemes over that field. -/
noncomputable def fgAlgCatOpEquivLftAffineOver
    (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ≌ lftAffineOver K := by
  let _ : (fgAlgToLftAffine K).Full :=
    (fgAlgToLftAffineFullyFaithful K).full
  let _ : (fgAlgToLftAffine K).Faithful :=
    (fgAlgToLftAffineFullyFaithful K).faithful
  let _ : (fgAlgToLftAffine K).EssSurj := fgAlgToLftAffineEssSurj K
  let _ : (fgAlgToLftAffine K).IsEquivalence := {}
  exact (fgAlgToLftAffine K).asEquivalence

/-- Spectra of finitely generated algebras are dense among locally-finite-type schemes over a
field. -/
theorem finiteAlgSpecOver_isDense
    (K : Type u) [Field K] : (finiteAlgSpecOver K).IsDense := by
  let _ : (lftAffineInclusion K).IsDense := lftAffineInclusion_isDense K
  let _ : (fgAlgToLftAffine K).Full :=
    (fgAlgToLftAffineFullyFaithful K).full
  let _ : (fgAlgToLftAffine K).Faithful :=
    (fgAlgToLftAffineFullyFaithful K).faithful
  let _ : (fgAlgToLftAffine K).EssSurj := fgAlgToLftAffineEssSurj K
  let _ : (fgAlgToLftAffine K).IsEquivalence := {}
  let _ : (fgAlgToLftAffine K ⋙ lftAffineInclusion K).IsDense := inferInstance
  exact Functor.IsDense.of_iso (fgAlgToLftAffineCompIso K)

/-- Finite-type schemes over a field, expressed as locally-finite-type schemes with quasi-compact
structure morphism. -/
abbrev algebraicOver (K : Type u) [Field K] :=
  ObjectProperty.FullSubcategory
    (fun X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)) ↦ QuasiCompact X.hom)

/-- The inclusion of finite-type schemes into locally-finite-type schemes over a field. -/
@[implicit_reducible] noncomputable def algebraicOverInclusion
    (K : Type u) [Field K] :
    algebraicOver K ⥤ locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)) :=
  ObjectProperty.ι _

/-- The set-valued functor of points of a finite-type scheme on finitely generated algebras. -/
noncomputable def algebraicOverPoints
    (K : Type u) [Field K] :=
  algebraicOverInclusion K ⋙
    Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)

/-- The functor of points on finitely generated algebras is fully faithful on finite-type schemes. -/
noncomputable def algebraicOverPointsFullyFaithful
    (K : Type u) [Field K] : (algebraicOverPoints K).FullyFaithful := by
  letI : (finiteAlgSpecOver K).IsDense := finiteAlgSpecOver_isDense K
  exact (ObjectProperty.fullyFaithfulι _).comp
    (Functor.FullyFaithful.ofFullyFaithful
      (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)))

/-- The functor of points on finitely generated algebras is fully faithful on locally-finite-type
schemes. -/
noncomputable def lftPointsFullyFaithful
    (K : Type u) [Field K] :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).FullyFaithful := by
  letI : (finiteAlgSpecOver K).IsDense := finiteAlgSpecOver_isDense K
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- The functor of points on finitely generated algebras preserves finite limits. -/
theorem lftPointsPreservesFiniteLimits
    (K : Type u) [Field K] :
    Limits.PreservesFiniteLimits
      (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)) := by
  change Limits.PreservesFiniteLimits
    (uliftYoneda.{0} ⋙
      (Functor.whiskeringLeft (((FGAlgCat K)ᵒᵖ)ᵒᵖ)
        (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))ᵒᵖ (Type u)).obj
          (finiteAlgSpecOver K).op)
  infer_instance

noncomputable local instance lftPoints_preservesFiniteLimits
    (K : Type u) [Field K] :
    Limits.PreservesFiniteLimits
      (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)) :=
  lftPointsPreservesFiniteLimits K

noncomputable local instance lftOverCartesianMonoidal
    (K : Type u) [Field K] :
    CartesianMonoidalCategory (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  .ofHasFiniteProducts

noncomputable local instance lftPointsMonoidal
    (K : Type u) [Field K] :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The group-valued functor of points on finitely generated algebras. Group objects in this
pointwise Cartesian functor category are group-valued functors. -/
@[expose] noncomputable def lftGroupPoints
    (K : Type u) [Field K] :=
  (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).mapGrp

/-- The functor of points on finitely generated algebras is fully faithful on group objects among
locally-finite-type schemes. -/
noncomputable def lftGroupPointsFullyFaithful
    (K : Type u) [Field K] : (lftGroupPoints K).FullyFaithful :=
  (lftPointsFullyFaithful K).mapGrp

/-- A group-valued functor is represented by a group object among locally-finite-type schemes if
and only if its underlying set-valued functor is represented there. -/
theorem lftGroupPoints_essImage_iff
    (K : Type u) [Field K]
    {F : Grp ((((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))} :
    (lftGroupPoints K).essImage F ↔
      (Presheaf.restrictedULiftYoneda.{0}
        (finiteAlgSpecOver K)).essImage F.X := by
  let _ : (Presheaf.restrictedULiftYoneda.{0}
      (finiteAlgSpecOver K)).Full := (lftPointsFullyFaithful K).full
  let _ : (Presheaf.restrictedULiftYoneda.{0}
      (finiteAlgSpecOver K)).Faithful := (lftPointsFullyFaithful K).faithful
  exact Functor.essImage_mapGrp

/-- Group objects among schemes locally of finite type whose structure morphisms are also
quasi-compact, hence finite type. -/
abbrev algebraicGroupOver (K : Type u) [Field K] :=
  ObjectProperty.FullSubcategory
    (fun G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) ↦
      QuasiCompact G.X.hom)

/-- The inclusion of finite-type group schemes into group objects among schemes locally of finite
type. -/
@[implicit_reducible] noncomputable def algebraicGroupOverInclusion
    (K : Type u) [Field K] :
    algebraicGroupOver K ⥤ Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  ObjectProperty.ι _

/-- The group-valued functor of points of a finite-type group scheme, evaluated on finitely
generated algebras. -/
noncomputable def algebraicGroupPoints
    (K : Type u) [Field K] :=
  algebraicGroupOverInclusion K ⋙ lftGroupPoints K

/-- The functor of points on finitely generated algebras is fully faithful on finite-type group
schemes over a field. -/
noncomputable def algebraicGroupPointsFullyFaithful
    (K : Type u) [Field K] : (algebraicGroupPoints K).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).comp (lftGroupPointsFullyFaithful K)

/-- A group-valued functor on finitely generated algebras is represented by a finite-type group
scheme if and only if its underlying set-valued functor is represented by a finite-type scheme. -/
theorem algebraicGroupPoints_essImage_iff
    (K : Type u) [Field K]
    {F : Grp ((((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))} :
    (algebraicGroupPoints K).essImage F ↔
      (algebraicOverPoints K).essImage F.X := by
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact ⟨⟨G.obj.X, G.property⟩, ⟨(Grp.forget _).mapIso e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    change (Presheaf.restrictedULiftYoneda.{0}
      (finiteAlgSpecOver K)).obj X.obj ≅ F.X at e
    obtain ⟨G, ⟨eG⟩⟩ :=
      (lftGroupPoints_essImage_iff K).mpr ⟨X.obj, ⟨e⟩⟩
    let eGX : (Presheaf.restrictedULiftYoneda.{0}
        (finiteAlgSpecOver K)).obj G.X ≅ F.X := (Grp.forget _).mapIso eG
    let eScheme : G.X ≅ X.obj :=
      (lftPointsFullyFaithful K).preimageIso (eGX ≪≫ e.symm)
    have hqc : QuasiCompact G.X.hom := by
      have hw : eScheme.hom.left ≫ X.obj.hom = G.X.hom := by
        simpa using eScheme.hom.w
      rw [← hw]
      let _ : IsIso eScheme.hom.left := by
        change IsIso (((MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤
          (Spec (.of K))) ⋙ CategoryTheory.Over.forget (Spec (.of K))).map eScheme.hom)
        infer_instance
      let _ : QuasiCompact X.obj.hom := X.property
      infer_instance
    let G' : algebraicGroupOver K := ⟨G, hqc⟩
    refine ⟨G', ⟨?_⟩⟩
    change (lftGroupPoints K).obj G ≅ F
    exact eG

end AlgebraicGeometry
