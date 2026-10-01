/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypePoints
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group-valued functors of points on finite-type affine tests

The generic functor of points on finitely generated algebras, its full faithfulness and
finite-limit preservation come from `SchemeProperties.FiniteTypePoints`. This module
extends those results to group objects and finite-type group schemes.

## Main results

- `AlgebraicGeometry.lftGroupPointsFullyFaithful`
- `AlgebraicGeometry.lftGroupPoints_essImage_iff`
- `AlgebraicGeometry.algebraicGroupPointsFullyFaithful`
- `AlgebraicGeometry.algebraicGroupPoints_essImage_iff`
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

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
    let X : algebraicOver K := ⟨G.obj.X, G.property⟩
    refine ⟨X, ⟨?_⟩⟩
    rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X]
    exact (Grp.forget _).mapIso e
  · rintro ⟨X, ⟨e⟩⟩
    rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X] at e
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
