/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineRepresentation
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import SchemeProperties.Algebra.Category.FGAlgCat.Range
import SchemeProperties.FinitePresentation.PointDescent
import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Finite-type restriction of the geometric point functor

For a locally-finite-type group scheme over a commutative ring, natural
transformations from its geometric point functor to any given group-valued
functor extend uniquely from finite-type coefficient algebras. The forward
function is the existing `Functor.whiskerLeft`.

The group scheme need not be affine or separated. Only point-group carriers
are universe-lifted; coefficient algebras and their given maps are unchanged.
The specialization uses the existing `GeometricRepresentation`, with its
original target on `R ⊗[K] V` and no finiteness condition on `V`.

## Implementation notes

Point descent and eventual equality recognize a particular type
cocone. Type ULift preserves it, and stock group-colimit existence and forgetful
reflection prove that the same lifted group cocone is colimiting. Finality of
the stage functor transfers this witness to the identity-unit comma cocone.
The stock Kan universal property then proves bijectivity of restriction.
The derived left-Kan property is public, so its stock extension, factorization,
uniqueness and naturality API remains available to downstream constructions.

## References

- J. S. Milne, *Algebraic Groups* (2017), Chapter 4, for representations as
  morphisms of group-valued functors. Here the base is any commutative ring and
  the group scheme may be nonaffine and nonseparated.
- SchemeProperties for finite-type coefficient descent, eventual equality of
  points and the finitely generated subalgebra adjunction; Mathlib for filtered
  colimits of types and groups, universe lifting and left Kan extensions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.GrpObj

universe u v w

namespace AlgebraicGeometry

variable {K : Type u} [CommRing K]

local notation "ι" => ObjectProperty.ι
  (fun A : CommAlgCat K => Algebra.FiniteType K A)

private abbrev FGStage (R : CommAlgCat.{u, u} K) := {A : Subalgebra K R // A.FG}

private instance fgStage_nonempty (R : CommAlgCat.{u, u} K) : Nonempty (FGStage R) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

private instance fgStage_directed (R : CommAlgCat.{u, u} K) : IsDirectedOrder (FGStage R) where
  directed A B :=
    ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
      (show A.1 ≤ A.1 ⊔ B.1 from le_sup_left),
      (show B.1 ≤ A.1 ⊔ B.1 from le_sup_right)⟩

private def fgPointCocone (Q : CommAlgCat.{u, u} K ⥤ GrpCat.{w}) (R : CommAlgCat.{u, u} K) :
    Cocone (FGAlgCat.subalgebraFunctor R ⋙ ι ⋙ Q) :=
  ((Functor.LeftExtension.mk Q (𝟙 (ι ⋙ Q))).coconeAt R).whisker
    (FGAlgCat.subalgebraToCostructuredArrow R)

variable (G : Scheme.{u}) [G.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))]
  [LocallyOfFiniteType (G ↘ Spec (.of K))]

local notation "P" => affineGeometricPointFunctor (K := K) G

private noncomputable def fgPointTypesIsColimit (R : CommAlgCat.{u, u} K) :
    IsColimit ((forget GrpCat.{u}).mapCocone (fgPointCocone P R)) := by
  classical
  letI : IsFiltered (FGStage R) := inferInstance
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    change (Spec (.of R)).asOver (Spec (.of K)) ⟶
      G.asOver (Spec (.of K)) at x
    obtain ⟨A, hA, xA, hxA⟩ :=
      Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFiniteType
        (R := K) K G x
    refine ⟨⟨A, hA⟩, xA, ?_⟩
    change x = (algSpec (.of K)).map (CommAlgCat.ofHom A.val).op ≫ xA
    apply Over.OverMorphism.ext
    exact congrArg Over.Hom.left hxA.symm
  · intro A x y h
    change (algSpec (.of K)).map (CommAlgCat.ofHom A.1.val).op ≫ x =
      (algSpec (.of K)).map (CommAlgCat.ofHom A.1.val).op ≫ y at h
    have hval : A.1.val.restrictScalars K = A.1.val := by
      ext a
      rfl
    have h' :
        (algSpec (.of K)).map
            (CommAlgCat.ofHom (A.1.val.restrictScalars K)).op ≫ x =
          (algSpec (.of K)).map
            (CommAlgCat.ofHom (A.1.val.restrictScalars K)).op ≫ y := by
      simpa only [hval] using h
    obtain ⟨B, hB, hAB, _hAB', hxy⟩ :=
      Scheme.exists_algSpec_map_subalgebra_inclusion_comp_eq_of_locallyOfFiniteType
        (R := K) K G A.1 A.1 A.2 A.2 x y h'
    -- The two containment proofs are definitionally equal by proof irrelevance.
    have hxy' :
        (algSpec (.of K)).map
            (CommAlgCat.ofHom ((Subalgebra.inclusion hAB).restrictScalars K)).op ≫ x =
          (algSpec (.of K)).map
            (CommAlgCat.ofHom ((Subalgebra.inclusion hAB).restrictScalars K)).op ≫ y :=
      hxy
    have hinc : (Subalgebra.inclusion hAB).restrictScalars K =
        Subalgebra.inclusion hAB := by
      ext a
      rfl
    refine ⟨⟨B, hB⟩, homOfLE hAB, ?_⟩
    change (algSpec (.of K)).map
        (CommAlgCat.ofHom (Subalgebra.inclusion hAB)).op ≫ x =
      (algSpec (.of K)).map
        (CommAlgCat.ofHom (Subalgebra.inclusion hAB)).op ≫ y
    simpa only [hinc] using hxy'

private noncomputable def fgPointIsColimit (R : CommAlgCat.{u, u} K) :
    IsColimit (fgPointCocone (P ⋙ GrpCat.uliftFunctor.{v, u}) R) := by
  letI : IsFiltered (FGStage R) := inferInstance
  let D : FGStage R ⥤ GrpCat.{max u v} :=
    FGAlgCat.subalgebraFunctor R ⋙ ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u})
  have htypes : IsColimit
      ((forget GrpCat.{max u v}).mapCocone (fgPointCocone (P ⋙ GrpCat.uliftFunctor.{v, u}) R)) := by
    let T₀ : FGStage R ⥤ Type u :=
      (FGAlgCat.subalgebraFunctor R ⋙ ι ⋙ P) ⋙ forget GrpCat.{u}
    let T₁ : FGStage R ⥤ Type (max u v) :=
      (FGAlgCat.subalgebraFunctor R ⋙ ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u})) ⋙
        forget GrpCat.{max u v}
    let c₀ : Cocone T₀ :=
      (forget GrpCat.{u}).mapCocone (fgPointCocone P R)
    let c₁ : Cocone T₁ :=
      (forget GrpCat.{max u v}).mapCocone (fgPointCocone (P ⋙ GrpCat.uliftFunctor.{v, u}) R)
    let cU : Cocone (T₀ ⋙ CategoryTheory.uliftFunctor.{v, u}) :=
      (CategoryTheory.uliftFunctor.{v, u}).mapCocone c₀
    have hcU : IsColimit cU :=
      isColimitOfPreserves (CategoryTheory.uliftFunctor.{v, u})
        (fgPointTypesIsColimit G R)
    let e : T₁ ≅ T₀ ⋙ CategoryTheory.uliftFunctor.{v, u} :=
      NatIso.ofComponents (fun A => Iso.refl _) (by
        intro A B f
        ext x
        rfl)
    have hcU' : IsColimit ((Cocone.precompose e.hom).obj cU) :=
      (IsColimit.precomposeHomEquiv e cU).symm hcU
    let ec : ((Cocone.precompose e.hom).obj cU) ≅ c₁ :=
      Cocone.ext (Iso.refl _) (by
        intro A
        ext x
        rfl)
    exact IsColimit.ofIsoColimit hcU' ec
  letI : HasColimit D := HasColimit.mk {
    cocone := GrpCat.FilteredColimits.colimitCocone.{u, v} D
    isColimit := GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, v} D }
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget GrpCat.{max u v}) :=
    GrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (forget GrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink.{u, v, u, v}
      (forget GrpCat.{max u v})
  letI : PreservesColimit D (forget GrpCat.{max u v}) := inferInstance
  letI : ReflectsColimit D (forget GrpCat.{max u v}) :=
    reflectsColimit_of_reflectsIsomorphisms D (forget GrpCat.{max u v})
  exact isColimitOfReflects (forget GrpCat.{max u v}) htypes

/-- The geometric point functor of a locally-finite-type group scheme is the
left Kan extension of its restriction to finite-type coefficient algebras.
The unit is the identity on that restriction. -/
theorem affineGeometricPointFunctor_isLeftKanExtension :
    (P ⋙ GrpCat.uliftFunctor.{v, u}).IsLeftKanExtension
      (𝟙 (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u}))) := by
  let E : Functor.LeftExtension ι (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u})) :=
    Functor.LeftExtension.mk (P ⋙ GrpCat.uliftFunctor.{v, u})
      (𝟙 (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u})))
  have hE : E.IsPointwiseLeftKanExtension := by
    intro R
    have hsmall : IsColimit
        ((E.coconeAt R).whisker
          (FGAlgCat.subalgebraToCostructuredArrow R)) := by
      exact fgPointIsColimit.{u, v} G R
    exact
      (Functor.Final.isColimitWhiskerEquiv
        (FGAlgCat.subalgebraToCostructuredArrow R)
        (E.coconeAt R)) hsmall
  exact hE.isLeftKanExtension

/-- Natural transformations from the geometric point functor of a
locally-finite-type group scheme extend uniquely from finite-type coefficient
algebras. The target functor is arbitrary, and the forward map is restriction. -/
theorem affineGeometricPointFunctor_restriction_bijective
    (H : CommAlgCat.{u, u} K ⥤ GrpCat.{max u v}) :
    Function.Bijective
      (fun η :
        (affineGeometricPointFunctor (K := K) G ⋙
          GrpCat.uliftFunctor.{v, u}) ⟶ H =>
        Functor.whiskerLeft
          (ObjectProperty.ι
            (fun A : CommAlgCat.{u, u} K => Algebra.FiniteType K A)) η) := by
  let : (P ⋙ GrpCat.uliftFunctor.{v, u}).IsLeftKanExtension
      (𝟙 (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u}))) :=
    affineGeometricPointFunctor_isLeftKanExtension.{u, v} G
  let e := (P ⋙ GrpCat.uliftFunctor.{v, u}).homEquivOfIsLeftKanExtension
    (𝟙 (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u}))) H
  have hf :
      (e : ((P ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ H) →
        (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ ι ⋙ H)) =
        (fun η : (P ⋙ GrpCat.uliftFunctor.{v, u}) ⟶ H => Functor.whiskerLeft ι η) := by
    funext η
    change (𝟙 (ι ⋙ (P ⋙ GrpCat.uliftFunctor.{v, u}))) ≫ Functor.whiskerLeft ι η =
      Functor.whiskerLeft ι η
    exact Category.id_comp _
  rw [← hf]
  exact e.bijective

namespace GeometricRepresentation

/-- Geometric representations on an arbitrary module extend uniquely from
finite-type coefficient algebras, using the existing representation type. -/
theorem restriction_bijective (V : Type v) [AddCommGroup V] [Module K V] :
    Function.Bijective
      (fun η : GeometricRepresentation (K := K) G V =>
        Functor.whiskerLeft
          (ObjectProperty.ι
            (fun A : CommAlgCat.{u, u} K => Algebra.FiniteType K A)) η) :=
  affineGeometricPointFunctor_restriction_bijective.{u, v} G
    (generalLinearModuleFunctor K V :
      CommAlgCat.{u, u} K ⥤ GrpCat.{max u v})

end GeometricRepresentation

end AlgebraicGeometry
