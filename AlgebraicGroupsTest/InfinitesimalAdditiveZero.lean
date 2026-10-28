/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveZero

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

private def testGenericBialgebra :
    infinitesimalAdditiveCoordinateRing K p 0 ≃ₐc[K] K :=
  infinitesimalAdditiveZeroBialgEquiv K p

private def testGenericGroupIso :
    infinitesimalAdditiveGroupScheme K p 0 ≅ (TauCeti.RootsOfUnityGroup.groupScheme K 1) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne K p

private theorem testGenericIsoInverseLaws :
    (testGenericGroupIso K p).hom ≫ (testGenericGroupIso K p).inv =
        𝟙 (infinitesimalAdditiveGroupScheme K p 0) ∧
      (testGenericGroupIso K p).inv ≫ (testGenericGroupIso K p).hom =
        𝟙 ((TauCeti.RootsOfUnityGroup.groupScheme K 1)) :=
  ⟨(testGenericGroupIso K p).hom_inv_id, (testGenericGroupIso K p).inv_hom_id⟩

private def testGenericSourcePower :
    infinitesimalAdditiveGroupScheme K p 0 ≅ (TauCeti.RootsOfUnityGroup.groupScheme K (p ^ 0)) := by
  simpa using infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne K p

private theorem testGenericCounit (x : infinitesimalAdditiveCoordinateRing K p 0) :
    infinitesimalAdditiveZeroBialgEquiv K p x = CoalgebraStruct.counit (R := K) x :=
  infinitesimalAdditiveZeroBialgEquiv_apply K p x

private theorem testGenericUnit (x : K) :
    (infinitesimalAdditiveZeroBialgEquiv K p).symm x =
      algebraMap K (infinitesimalAdditiveCoordinateRing K p 0) x :=
  infinitesimalAdditiveZeroBialgEquiv_symm_apply K p x

private theorem testGenericHomReadback :
    (testGenericGroupIso K p).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (((infinitesimalAdditiveZeroBialgEquiv K p).symm :
            K →ₐ[K] infinitesimalAdditiveCoordinateRing K p 0).comp
          (MonoidAlgebra.bialgEquivOfSubsingleton (R := K)
        (M := TauCeti.RootsOfUnityGroup.characterGroup.{u} 1) :
            (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} 1)) →ₐ[K]
              K)).toRingHom) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne_hom_left K p

private theorem testGenericInvReadback :
    (testGenericGroupIso K p).inv.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (((MonoidAlgebra.bialgEquivOfSubsingleton (R := K)
        (M := TauCeti.RootsOfUnityGroup.characterGroup.{u} 1)).symm :
            K →ₐ[K] (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} 1))).comp
          (infinitesimalAdditiveZeroBialgEquiv K p :
            infinitesimalAdditiveCoordinateRing K p 0 →ₐ[K] K)).toRingHom) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne_inv_left K p

variable (R : Type u) [CommRing R] [Algebra K R]

private theorem testAdditivePoint (x : infinitesimalAdditiveSubgroup K p 0 R) :
    (infinitesimalAdditiveMulEquivAlgHom K p 0 R (.ofAdd x)).ofConv
      (infinitesimalAdditiveCoordinate K p 0) = 0 := by
  rw [infinitesimalAdditiveMulEquivAlgHom_coordinate]
  exact congrArg Subtype.val (infinitesimalAdditiveSubgroup_zero_eq_zero K p R x)

private theorem testAdditiveSchemePoint (x : infinitesimalAdditiveSubgroup K p 0 R) :
    (infinitesimalAdditiveMulEquivPoints K p 0 R (.ofAdd x)).left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveMulEquivAlgHom K p 0 R (.ofAdd x)).ofConv.toRingHom) :=
  infinitesimalAdditiveMulEquivPoints_apply_left K p 0 R x

private theorem testRootsPoint (ζ : rootsOfUnity 1 R) :
    ((TauCeti.RootsOfUnityGroup.pointsMulEquiv (R := K) (A := R) 1).symm ζ).ofConv
      (MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator 1) 1) = 1 := by
  rw [TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator]
  have hζ : ζ = 1 := Subsingleton.elim _ _
  subst ζ
  rfl

private theorem testRootsSchemePoint (ζ : rootsOfUnity 1 R) :
    (TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv
      (R := K) (A := R) (TauCeti.RootsOfUnityGroup.characterGroup.{u} 1)
        ((TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := K) (A := R) 1).symm ζ)).ofConv
      (MonoidAlgebra.single (ULift.up (TauCeti.RootsOfUnityGroup.generator 1)) 1) =
        ((ζ : Rˣ) : R) :=
  TauCeti.RootsOfUnityGroup.schemePointsMulEquiv_symm_apply_single_generator 1 ζ

private def testField (F : Type u) [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] :
    infinitesimalAdditiveGroupScheme F q 0 ≅ (TauCeti.RootsOfUnityGroup.groupScheme F 1) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne F q

private def testPolynomialNonfield :
    infinitesimalAdditiveGroupScheme (Polynomial (ZMod 2)) 2 0 ≅
      (TauCeti.RootsOfUnityGroup.groupScheme (Polynomial (ZMod 2)) 1) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private def testZModTwo :
    infinitesimalAdditiveGroupScheme (ZMod 2) 2 0 ≅
      (TauCeti.RootsOfUnityGroup.groupScheme (ZMod 2) 1) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private def testZModThree :
    infinitesimalAdditiveGroupScheme (ZMod 3) 3 0 ≅
      (TauCeti.RootsOfUnityGroup.groupScheme (ZMod 3) 1) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private theorem testZeroAlgebraAdditivePoint
    (x : infinitesimalAdditiveSubgroup (ZMod 2) 2 0 PUnit) :
    (infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 0 PUnit (.ofAdd x)).ofConv
      (infinitesimalAdditiveCoordinate (ZMod 2) 2 0) = 0 :=
  testAdditivePoint (ZMod 2) 2 PUnit x

private theorem testZeroAlgebraRootsPoint (ζ : rootsOfUnity 1 PUnit.{1}) :
    ((TauCeti.RootsOfUnityGroup.pointsMulEquiv (R := ZMod 3) (A := PUnit.{1}) 1).symm ζ).ofConv
      (MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator 1) 1) = 1 :=
  testRootsPoint (ZMod 3) PUnit.{1} ζ

end AlgebraicGeometry
