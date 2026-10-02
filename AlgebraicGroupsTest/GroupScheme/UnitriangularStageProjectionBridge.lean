/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageProjectionBridge
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry UnitriangularStageCoordinateRing
open scoped Classical

variable (K : Type) [CommRing K] (n r : ℕ) (hr : 1 ≤ r)

example (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    stageProductCoordinatePullback K n r hr (MvPolynomial.X ij) =
      coordinate K n r ij :=
  stageProductCoordinatePullback_X K n r hr ij

example (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom ≫
        additiveGroupAffineProductProjection K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij =
      (unitriangularStageUnderlyingSpecIso K n r).hom ≫
        stageProductSpecRename K n r hr ≫
        additiveGroupAffineProductProjection K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r) ij :=
  unitriangularStage_projection_triangle K n r hr ij

example :
    (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom =
      (unitriangularStageUnderlyingSpecIso K n r).hom ≫
        stageProductSpecRename K n r hr :=
  unitriangularStageCoordinateMap_underlying_spec K n r hr

example :
    (unitriangularStageUnderlyingAffineSpaceIso K n r).inv ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (additiveGroupProductUnderlyingAffineSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom =
      (additiveGroupAffineProductSpecToSpaceIso K (SurvivingPair n r)).symm.hom ≫
        stageProductSpecRename K n r hr ≫
        (additiveGroupAffineProductSpecToSpaceIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom :=
  unitriangularStageCoordinateMap_underlying_affineSpace K n r hr

example :
    unitriangularStageCoordinateSectionOver K n r hr ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom =
      𝟙 ((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
        additiveGroupScheme K).X) :=
  unitriangularStageCoordinateSectionOver_comp K n r hr

example (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    stageProductSectionPullback K n r hr (coordinate K n r ij) =
      MvPolynomial.X ij :=
  stageProductSectionPullback_inclusion K n r hr ij

example (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr).left)
        (coordinate K n r ij) = MvPolynomial.X ij :=
  unitriangularStageCoordinateSectionOver_coordinate K n r hr ij

example (s : SurvivingPair n r)
    (hs : s.1.1.1.val + r < s.1.1.2.val) :
    stageProductSectionPullback K n r hr
      (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = 0 :=
  stageProductSectionPullback_higher K n r hr s hs

example (s : SurvivingPair n r)
    (hs : s.1.1.1.val + r < s.1.1.2.val) :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso K
          (Matrix.UnitriangularGroup.superdiagonalIndex n r)).inv ≫
        unitriangularStageCoordinateSectionOver K n r hr).left)
        (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = 0 :=
  unitriangularStageCoordinateSectionOver_higher K n r hr s hs

example :
    unitriangularStageCoordinateSectionOver ℤ 0 1 (by decide) ≫
        (unitriangularStageCoordinateMap ℤ 0 1 (by decide)).hom.hom =
      𝟙 ((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 0 1 =>
        additiveGroupScheme ℤ).X) :=
  unitriangularStageCoordinateSectionOver_comp ℤ 0 1 (by decide)

example :
    unitriangularStageCoordinateSectionOver (ZMod 1) 1 2 (by decide) ≫
        (unitriangularStageCoordinateMap (ZMod 1) 1 2 (by decide)).hom.hom =
      𝟙 ((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 1 2 =>
        additiveGroupScheme (ZMod 1)).X) :=
  unitriangularStageCoordinateSectionOver_comp (ZMod 1) 1 2 (by decide)

example :
    (unitriangularStageCoordinateMap ℤ 3 3 (by decide)).hom.hom ≫
        (additiveGroupProductUnderlyingSpecIso ℤ
          (Matrix.UnitriangularGroup.superdiagonalIndex 3 3)).hom =
      (unitriangularStageUnderlyingSpecIso ℤ 3 3).hom ≫
        stageProductSpecRename ℤ 3 3 (by decide) :=
  unitriangularStageCoordinateMap_underlying_spec ℤ 3 3 (by decide)

example :
    unitriangularStageCoordinateSectionOver (ZMod 1) 3 4 (by decide) ≫
        (unitriangularStageCoordinateMap (ZMod 1) 3 4 (by decide)).hom.hom =
      𝟙 ((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 4 =>
        additiveGroupScheme (ZMod 1)).X) :=
  unitriangularStageCoordinateSectionOver_comp (ZMod 1) 3 4 (by decide)

example :
    stageProductSectionPullback ℤ 3 1 (by decide)
      (quotient ℤ 3 1 (entry ℤ 3 (0 : Fin 3) (2 : Fin 3))) = 0 :=
  stageProductSectionPullback_higher ℤ 3 1 (by decide)
    ⟨⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩, by decide⟩ (by decide)

example :
    Spec.preimage
      (((additiveGroupProductUnderlyingSpecIso ℤ
          (Matrix.UnitriangularGroup.superdiagonalIndex 3 1)).inv ≫
        unitriangularStageCoordinateSectionOver ℤ 3 1 (by decide)).left)
        (quotient ℤ 3 1 (entry ℤ 3 (0 : Fin 3) (2 : Fin 3))) = 0 :=
  unitriangularStageCoordinateSectionOver_higher ℤ 3 1 (by decide)
    ⟨⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩, by decide⟩ (by decide)
