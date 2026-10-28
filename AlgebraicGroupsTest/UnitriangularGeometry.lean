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

open TauCeti.UpperUnitriangularGroup


noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

example : (TauCeti.UpperUnitriangular.groupScheme K ι).X ≅
    (AffineSpace (TauCeti.UpperUnitriangular.Index ι) (Spec (.of K))).asOver (Spec (.of K)) :=
  unitriangularUnderlyingAffineSpaceIso K ι

example (p : TauCeti.UpperUnitriangular.Index ι) :
    Spec.preimage ((unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (TauCeti.UpperUnitriangular.Index ι) (.of K)).hom) (MvPolynomial.X p) =
        (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K ι
          (TauCeti.UpperUnitriangular.genericMatrix K ι p.1.1 p.1.2)) :=
  unitriangularUnderlyingAffineSpaceIso_preimage_variable K ι p

example (f : (TauCeti.UpperUnitriangular.coordinateHopfAlgebra K ι)) :
    Spec.preimage ((AffineSpace.SpecIso (TauCeti.UpperUnitriangular.Index ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left) f =
        ((TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K ι)).symm f :=
  unitriangularUnderlyingAffineSpaceIso_preimage_inverse K ι f

example : Algebra.Smooth K ((TauCeti.UpperUnitriangular.coordinateHopfAlgebra K ι)) := inferInstance
example : Algebra.FinitePresentation K ((TauCeti.UpperUnitriangular.coordinateHopfAlgebra K
  ι)) := inferInstance
example : Module.Flat K ((TauCeti.UpperUnitriangular.coordinateHopfAlgebra K ι)) := inferInstance

example : Smooth ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom := inferInstance
example : Flat ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom := inferInstance
example : LocallyOfFinitePresentation ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom :=
  inferInstance
example : GeometricallyIntegral ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom :=
  inferInstance

example [IsDomain K] : IsIntegral ((TauCeti.UpperUnitriangular.groupScheme K ι).X).left :=
  inferInstance

variable (F : Type u) [Field F] (index : Type u) [Fintype index] [LinearOrder index]

example : ringKrullDim ((TauCeti.UpperUnitriangular.coordinateHopfAlgebra F index)) =
    (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) :=
  unitriangularCoordinateRing_ringKrullDim F index

example : topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme F index).X).left =
    (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) :=
  unitriangularGroupUnderlyingScheme_topologicalKrullDim F index

example : Smooth ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)).X).hom := inferInstance
example : Flat ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)).X).hom := inferInstance
example : LocallyOfFinitePresentation
    ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)).X).hom := inferInstance
example : GeometricallyIntegral
    ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)).X).hom := inferInstance

example : topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme ℚ (Fin 0)).X).left =
    (0 : WithBot ℕ∞) := by simpa using
      unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 0
example : topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme ℚ (Fin 1)).X).left =
    (0 : WithBot ℕ∞) := by simpa using
      unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 1
example : topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme ℚ (Fin 2)).X).left =
    (1 : WithBot ℕ∞) := by simpa using
      unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 2
example : topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme ℚ (Fin 3)).X).left =
    (3 : WithBot ℕ∞) := by simpa using
      unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin ℚ 3
