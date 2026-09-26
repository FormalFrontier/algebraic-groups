/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveZero

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

private def testGenericBialgebra :
    infinitesimalAdditiveCoordinateRing K p 0 ≃ₐc[K] K :=
  infinitesimalAdditiveZeroBialgEquiv K p

private def testGenericGroupIso :
    infinitesimalAdditiveGroupScheme K p 0 ≅ rootsOfUnityGroupScheme K 1 :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne K p

private theorem testGenericIsoInverseLaws :
    (testGenericGroupIso K p).hom ≫ (testGenericGroupIso K p).inv =
        𝟙 (infinitesimalAdditiveGroupScheme K p 0) ∧
      (testGenericGroupIso K p).inv ≫ (testGenericGroupIso K p).hom =
        𝟙 (rootsOfUnityGroupScheme K 1) :=
  ⟨(testGenericGroupIso K p).hom_inv_id, (testGenericGroupIso K p).inv_hom_id⟩

private def testGenericSourcePower :
    infinitesimalAdditiveGroupScheme K p 0 ≅ rootsOfUnityGroupScheme K (p ^ 0) := by
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
          (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := K) (M := ZMod 1) :
            rootsOfUnityCoordinateRing K 1 →ₐ[K] K)).toRingHom) :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne_hom_left K p

private theorem testGenericInvReadback :
    (testGenericGroupIso K p).inv.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (((AddMonoidAlgebra.bialgEquivOfSubsingleton (R := K) (M := ZMod 1)).symm :
            K →ₐ[K] rootsOfUnityCoordinateRing K 1).comp
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
    (rootsOfUnityMulEquivAlgHom K R 1 ζ).ofConv
      (rootsOfUnityCoordinateGenerator K 1) = 1 := by
  have hζ : ζ = 1 := Subsingleton.elim _ _
  subst ζ
  simp [rootsOfUnityCoordinateGenerator]

private theorem testRootsSchemePoint (ζ : rootsOfUnity 1 R) :
    (rootsOfUnityMulEquivPoints K R 1 ζ).left =
      Spec.map (CommRingCat.ofHom
        (rootsOfUnityMulEquivAlgHom K R 1 ζ).ofConv.toRingHom) :=
  rootsOfUnityMulEquivPoints_apply_left K R 1 ζ

private def testField (F : Type u) [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] :
    infinitesimalAdditiveGroupScheme F q 0 ≅ rootsOfUnityGroupScheme F 1 :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne F q

private def testPolynomialNonfield :
    infinitesimalAdditiveGroupScheme (Polynomial (ZMod 2)) 2 0 ≅
      rootsOfUnityGroupScheme (Polynomial (ZMod 2)) 1 :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private def testZModTwo :
    infinitesimalAdditiveGroupScheme (ZMod 2) 2 0 ≅
      rootsOfUnityGroupScheme (ZMod 2) 1 :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private def testZModThree :
    infinitesimalAdditiveGroupScheme (ZMod 3) 3 0 ≅
      rootsOfUnityGroupScheme (ZMod 3) 1 :=
  infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne _ _

private theorem testZeroAlgebraAdditivePoint
    (x : infinitesimalAdditiveSubgroup (ZMod 2) 2 0 PUnit) :
    (infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 0 PUnit (.ofAdd x)).ofConv
      (infinitesimalAdditiveCoordinate (ZMod 2) 2 0) = 0 :=
  testAdditivePoint (ZMod 2) 2 PUnit x

private theorem testZeroAlgebraRootsPoint (ζ : rootsOfUnity 1 PUnit) :
    (rootsOfUnityMulEquivAlgHom (ZMod 3) PUnit 1 ζ).ofConv
      (rootsOfUnityCoordinateGenerator (ZMod 3) 1) = 1 :=
  testRootsPoint (ZMod 3) PUnit ζ

end AlgebraicGeometry
