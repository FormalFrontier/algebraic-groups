/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageAffineSpace
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

example : unitriangularStageUnderlyingScheme K n r ≅
    (AffineSpace (SurvivingPair n r) (Spec (.of K))).asOver (Spec (.of K)) :=
  unitriangularStageUnderlyingAffineSpaceIso K n r

example : (unitriangularStageUnderlyingAffineSpaceIso K n r).hom ≫
    (unitriangularStageUnderlyingAffineSpaceIso K n r).inv =
      𝟙 (unitriangularStageUnderlyingScheme K n r) :=
  (unitriangularStageUnderlyingAffineSpaceIso K n r).hom_inv_id

example (s : SurvivingPair n r) :
    Spec.preimage ((unitriangularStageUnderlyingAffineSpaceIso K n r).hom.left ≫
      (AffineSpace.SpecIso (SurvivingPair n r) (.of K)).hom) (MvPolynomial.X s) =
        quotient K n r (entry K n s.1.1.1 s.1.1.2) :=
  unitriangularStageUnderlyingAffineSpaceIso_preimage_variable K n r s

example (f : CoordinateRing K n r) :
    Spec.preimage ((AffineSpace.SpecIso (SurvivingPair n r) (.of K)).inv ≫
      (unitriangularStageUnderlyingAffineSpaceIso K n r).inv.left) f =
        polynomialEquiv K n r f :=
  unitriangularStageUnderlyingAffineSpaceIso_preimage_inverse K n r f

-- Empty rank, empty strict-upper indices, initial stage, and stages above the rank.
example : unitriangularStageUnderlyingScheme ℤ 0 0 ≅
    (AffineSpace (SurvivingPair 0 0) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 0 0

example : unitriangularStageUnderlyingScheme ℤ 1 1 ≅
    (AffineSpace (SurvivingPair 1 1) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 1 1

example : unitriangularStageUnderlyingScheme ℤ 3 0 ≅
    (AffineSpace (SurvivingPair 3 0) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 3 0

example : unitriangularStageUnderlyingScheme ℤ 3 1 ≅
    (AffineSpace (SurvivingPair 3 1) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 3 1

example : unitriangularStageUnderlyingScheme ℤ 3 3 ≅
    (AffineSpace (SurvivingPair 3 3) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 3 3

example : unitriangularStageUnderlyingScheme ℤ 3 4 ≅
    (AffineSpace (SurvivingPair 3 4) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  unitriangularStageUnderlyingAffineSpaceIso ℤ 3 4

-- At rank three/stage two, the sole surviving coordinate is (0,2).
example :
    Spec.preimage ((unitriangularStageUnderlyingAffineSpaceIso ℤ 3 2).hom.left ≫
      (AffineSpace.SpecIso (SurvivingPair 3 2) (.of ℤ)).hom)
      (MvPolynomial.X (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2)) =
        quotient ℤ 3 2 (entry ℤ 3 (0 : Fin 3) (2 : Fin 3)) :=
  unitriangularStageUnderlyingAffineSpaceIso_preimage_variable ℤ 3 2
    (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2)

-- The zero coefficient ring is allowed, including empty surviving-variable sets.
example : unitriangularStageUnderlyingScheme (ZMod 1) 0 4 ≅
    (AffineSpace (SurvivingPair 0 4) (Spec (.of (ZMod 1)))).asOver
      (Spec (.of (ZMod 1))) :=
  unitriangularStageUnderlyingAffineSpaceIso (ZMod 1) 0 4

example : unitriangularStageUnderlyingScheme (ZMod 1) 3 2 ≅
    (AffineSpace (SurvivingPair 3 2) (Spec (.of (ZMod 1)))).asOver
      (Spec (.of (ZMod 1))) :=
  unitriangularStageUnderlyingAffineSpaceIso (ZMod 1) 3 2

example :
    Spec.preimage ((unitriangularStageUnderlyingAffineSpaceIso (ZMod 1) 3 2).hom.left ≫
      (AffineSpace.SpecIso (SurvivingPair 3 2) (.of (ZMod 1))).hom)
      (MvPolynomial.X (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2)) =
        quotient (ZMod 1) 3 2 (entry (ZMod 1) 3 (0 : Fin 3) (2 : Fin 3)) :=
  unitriangularStageUnderlyingAffineSpaceIso_preimage_variable (ZMod 1) 3 2
    (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2)
