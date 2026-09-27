/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.SplitKernelProduct
public import AlgebraicGroups.GroupScheme.SpecialLinearKernel
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection
public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth

/-!
# A product trivialization of the finite general linear determinant

For a chosen matrix index, the determinant character admits a diagonal section.
The actual determinant-one kernel pullback therefore gives an isomorphism of
underlying schemes over the base, with the section multiplied *before* the
special-linear factor. This is not a direct-product isomorphism of group schemes.
The projection of this product is a base change of the smooth special-linear
structure morphism, so the actual determinant morphism of schemes is smooth.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The published group-scheme section equation after forgetting to schemes over the base. -/
theorem generalLinearDeterminantSection_over_comp_det (pivot : n) :
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
        𝟙 (multiplicativeGroupUnderlyingScheme K) := by
  have h := congrArg
    (fun f : multiplicativeGroupScheme K ⟶ multiplicativeGroupScheme K ↦ f.hom.hom)
    (generalLinearDeterminantSectionSchemeHom_comp_det K n pivot)
  exact h

/-- The actual underlying-scheme isomorphism `SL(n,K) ×ₖ Gₘ,K ≅ GL(n,K)`.
Its forward map sends `(s,t)` to `diagonalSection(t) * inclusion(s)`;
the inverse first normalizes by `diagonalSection(det(g))⁻¹`. -/
def generalLinearDeterminantProductIso (pivot : n) :
    specialLinearGroupUnderlyingScheme K n ⊗ multiplicativeGroupUnderlyingScheme K ≅
      generalLinearGroupUnderlyingScheme K n :=
  splitKernelProductIso (specialLinearInclusion K n).hom.hom
    (generalLinearDeterminantSchemeHom K n).hom.hom
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom
    (specialLinearDeterminantSquare_isPullback_over K n)
    (generalLinearDeterminantSection_over_comp_det K n pivot)

/-- The forward map is section-first multiplication, not a homomorphism
from the direct-product group object in general. -/
theorem generalLinearDeterminantProductIso_hom (pivot : n) :
    (generalLinearDeterminantProductIso K n pivot).hom =
      (snd (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) ≫
          (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) *
      (fst (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) ≫
          (specialLinearInclusion K n).hom.hom) := by
  exact splitKernelProductIso_hom _ _ _ _ _

/-- The genuine determinant projection triangle in schemes over `Spec K`. -/
@[simp] theorem generalLinearDeterminantProductIso_hom_comp_det (pivot : n) :
    (generalLinearDeterminantProductIso K n pivot).hom ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
        snd (specialLinearGroupUnderlyingScheme K n)
          (multiplicativeGroupUnderlyingScheme K) := by
  exact splitKernelProductIso_hom_comp_q _ _ _ _ _

/-- The second inverse projection recovers the actual determinant. -/
@[simp] theorem generalLinearDeterminantProductIso_inv_comp_snd (pivot : n) :
    (generalLinearDeterminantProductIso K n pivot).inv ≫
      snd (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) =
          (generalLinearDeterminantSchemeHom K n).hom.hom := by
  exact splitKernelProductIso_inv_comp_snd _ _ _ _ _

/-- The first inverse projection lifts the normalized matrix into the actual
determinant-one kernel. -/
@[simp] theorem generalLinearDeterminantProductIso_inv_comp_fst (pivot : n) :
    (generalLinearDeterminantProductIso K n pivot).inv ≫
      fst (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) =
          splitKernelRemainder (specialLinearInclusion K n).hom.hom
            (generalLinearDeterminantSchemeHom K n).hom.hom
            (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom
            (specialLinearDeterminantSquare_isPullback_over K n)
            (generalLinearDeterminantSection_over_comp_det K n pivot) := by
  exact splitKernelProductIso_inv_comp_fst _ _ _ _ _

/-- The first inverse projection, followed by inclusion, is precisely
`diagonalSection(det(g))⁻¹ * g` in that noncommutative order. -/
@[simp] theorem generalLinearDeterminantProductIso_inv_fst_comp_inclusion (pivot : n) :
    (generalLinearDeterminantProductIso K n pivot).inv ≫
      fst (specialLinearGroupUnderlyingScheme K n)
        (multiplicativeGroupUnderlyingScheme K) ≫
          (specialLinearInclusion K n).hom.hom =
            ((generalLinearDeterminantSchemeHom K n).hom.hom ≫
              (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom)⁻¹ *
                𝟙 (generalLinearGroupUnderlyingScheme K n) := by
  rw [← Category.assoc, generalLinearDeterminantProductIso_inv_comp_fst,
    splitKernelRemainder_comp_i]

/-- The actual determinant scheme morphism is smooth whenever an explicit
matrix index is available; this also applies in rank one and over the zero ring. -/
theorem generalLinearDeterminantSchemeHom_smooth (pivot : n) :
    Smooth (generalLinearDeterminantSchemeHom K n).hom.hom.left := by
  let SL := specialLinearGroupUnderlyingScheme K n
  let GM := multiplicativeGroupUnderlyingScheme K
  let iso := generalLinearDeterminantProductIso K n pivot
  have hproj : Smooth (snd SL GM).left := by
    rw [Over.snd_left]
    exact smooth_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback SL.hom GM.hom)
      (show Smooth SL.hom from inferInstance)
  have hrespects : MorphismProperty.RespectsIso (@Smooth) := by
    rw [HasRingHomProperty.eq_affineLocally (@Smooth)]
    exact affineLocally_respectsIso RingHom.Smooth
      RingHom.Smooth.propertyIsLocal.respectsIso
  have hiso : IsIso iso.inv.left := by
    change IsIso ((Over.forget (Spec (.of K))).map iso.inv)
    infer_instance
  have hinv : Smooth (iso.inv.left ≫ (snd SL GM).left) :=
    hrespects.toRespectsLeft.precomp iso.inv.left hiso _ hproj
  change Smooth (iso.inv ≫ snd SL GM).left at hinv
  rw [← generalLinearDeterminantProductIso_hom_comp_det K n pivot,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hinv
  exact hinv

end AlgebraicGeometry
