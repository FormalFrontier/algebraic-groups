/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import SchemeProperties.JacobsonClosedPoints

/-!
# Surjectivity of dominant affine group homomorphisms

A dominant homomorphism of affine group schemes of finite type over an
algebraically closed field is surjective on all underlying scheme points.
The proof combines closed-point surjectivity with Chevalley's theorem and the
locally constructible closed-point comparison theorem for Jacobson spaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 1.69.
* Mathlib's Chevalley image theorem and the locally constructible closed-point
  comparison in scheme-properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Topology
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A dominant homomorphism of affine group schemes of finite type over an
algebraically closed field is surjective on all underlying scheme points.

This is the affine, algebraically closed-field scheme formulation of
Milne, *Algebraic Groups*, Corollary 1.69. Its closed-point formulation is
promoted here to all scheme points by constructibility. -/
theorem Surjective.of_dominant_affine_group_hom
    {K : Type u} [Field K] [IsAlgClosed K] {G H : Scheme.{u}}
    (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K))
    [IsAffine G] [IsAffine H]
    [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
    [GrpObj (Over.mk fG)] [GrpObj (Over.mk fH)]
    (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]
    [IsDominant φ.left] : Surjective φ.left := by
  have hcomp : φ.left ≫ fH = fG := Over.w φ
  have : LocallyOfFiniteType (φ.left ≫ fH) :=
    hcomp.symm ▸ (inferInstance : LocallyOfFiniteType fG)
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left fH
  have : IsAffineHom φ.left := isAffineHom_of_isAffine (X := G) (Y := H) φ.left
  have : QuasiCompact φ.left := inferInstance
  have : IsLocallyNoetherian (Spec (.of K)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian fH
  have : CompactSpace (Over.mk fH).left :=
    (show CompactSpace H from
      isCompact_univ_iff.mp (isAffineOpen_top H).isCompact)
  -- Affineness gives quasi-separatedness through the spectrum of global sections.
  have : QuasiSeparatedSpace (Over.mk fH).left :=
    (show QuasiSeparatedSpace H from
      Topology.IsOpenEmbedding.quasiSeparatedSpace
        (Scheme.homeoOfIso H.isoSpec).isOpenEmbedding)
  have : LocallyOfFinitePresentation φ.left :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (X := G) (Y := H) (f := φ.left)).mpr inferInstance
  -- Transfer Jacobsonness through affine spectra and the map on global sections.
  have : IsJacobsonRing Γ(Spec (.of K), ⊤) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr
      (JacobsonSpace.of_isOpenEmbedding
        (Scheme.homeoOfIso ((Spec (.of K)).isoSpec)).symm.isOpenEmbedding)
  have hft : fH.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType fH inferInstance
  have : IsJacobsonRing Γ(H, ⊤) := hft.isJacobsonRing
  have : JacobsonSpace H :=
    JacobsonSpace.of_isOpenEmbedding (Scheme.homeoOfIso H.isoSpec).isOpenEmbedding
  have himage : IsConstructible (Set.range φ.left) := by
    simpa only [Set.image_univ] using
      φ.left.isConstructible_image (IsConstructible.univ : IsConstructible (Set.univ : Set G))
  refine ⟨Set.range_eq_univ.mp ?_⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  apply (IsLocallyConstructible.subset_iff_inter_closedPoints_subset
    (IsConstructible.univ : IsConstructible (Set.univ : Set H)).isLocallyConstructible
    himage.isLocallyConstructible).mpr
  rintro y ⟨_, hy⟩
  obtain ⟨x, hx⟩ := groupSchemeClosedPointsMap_surjective fG fH φ ⟨y, hy⟩
  refine ⟨⟨x.val, ?_⟩, hy⟩
  exact (groupSchemeClosedPointsMap_apply_value fG fH φ x).symm.trans
    (congrArg Subtype.val hx)

end AlgebraicGeometry
