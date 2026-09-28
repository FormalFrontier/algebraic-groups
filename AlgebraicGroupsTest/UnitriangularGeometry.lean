/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularGeometry

/-!
# Ordinary-import clients of unitriangular affine geometry

These examples use the structural morphism of the existing group scheme and the
actual affine-space identification, with no assumptions on positive rank.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry UnitriangularCoordinateRing

universe u

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

example : unitriangularGroupUnderlyingScheme K ι ≅
    (AffineSpace (StrictUpperPair ι) (Spec (.of K))).asOver (Spec (.of K)) :=
  unitriangularUnderlyingAffineSpaceIso K ι

example (p : StrictUpperPair ι) :
    Spec.preimage ((unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).hom) (MvPolynomial.X p) =
        quotient K ι (GeneralLinearCoordinateRing.matrix K ι p.1.1 p.1.2) :=
  unitriangularUnderlyingAffineSpaceIso_preimage_variable K ι p

example (f : CoordinateRing K ι) :
    Spec.preimage ((AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left) f =
        (freeEquiv K ι).symm f :=
  unitriangularUnderlyingAffineSpaceIso_preimage_inverse K ι f

example : Algebra.Smooth K (CoordinateRing K ι) := inferInstance
example : Algebra.FinitePresentation K (CoordinateRing K ι) := inferInstance
example : Module.Flat K (CoordinateRing K ι) := inferInstance

example : Smooth (unitriangularGroupUnderlyingScheme K ι).hom := inferInstance
example : Flat (unitriangularGroupUnderlyingScheme K ι).hom := inferInstance
example : LocallyOfFinitePresentation (unitriangularGroupUnderlyingScheme K ι).hom :=
  inferInstance
example : GeometricallyIntegral (unitriangularGroupUnderlyingScheme K ι).hom :=
  inferInstance

example [IsDomain K] : IsIntegral (unitriangularGroupUnderlyingScheme K ι).left :=
  inferInstance

variable (F : Type u) [Field F] (index : Type u) [Fintype index] [LinearOrder index]

example : ringKrullDim (CoordinateRing F index) =
    (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) :=
  unitriangularCoordinateRing_ringKrullDim F index

example : topologicalKrullDim (unitriangularGroupUnderlyingScheme F index).left =
    (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) :=
  unitriangularGroupUnderlyingScheme_topologicalKrullDim F index

example : Smooth (unitriangularGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance
example : Flat (unitriangularGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance
example : LocallyOfFinitePresentation
    (unitriangularGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance
example : GeometricallyIntegral
    (unitriangularGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance

example : topologicalKrullDim (unitriangularGroupUnderlyingScheme ℚ (Fin 0)).left =
    (0 : WithBot ℕ∞) := by simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 0
example : topologicalKrullDim (unitriangularGroupUnderlyingScheme ℚ (Fin 1)).left =
    (0 : WithBot ℕ∞) := by simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 1
example : topologicalKrullDim (unitriangularGroupUnderlyingScheme ℚ (Fin 2)).left =
    (1 : WithBot ℕ∞) := by simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 2
example : topologicalKrullDim (unitriangularGroupUnderlyingScheme ℚ (Fin 3)).left =
    (3 : WithBot ℕ∞) := by simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 3
