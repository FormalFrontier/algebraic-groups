/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant

set_option warningAsError true

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
variable (R : Type u) [CommRing R] [Algebra K R]

private def testDeterminantBialgebraMorphism :
    multiplicativeGroupCoordinateRing K →ₐc[K] CoordinateRing K n :=
  generalLinearDeterminantBialgHom K n

private def testDeterminantGroupSchemeMorphism :
    generalLinearGroupScheme K n ⟶ multiplicativeGroupScheme K :=
  generalLinearDeterminantSchemeHom K n

private theorem testCoordinate :
    generalLinearDeterminantCoordinateMap K n (LaurentPolynomial.T 1) =
      (matrix K n).det :=
  generalLinearDeterminantCoordinateMap_coordinate K n

private theorem testInverseCoordinate :
    generalLinearDeterminantCoordinateMap K n (LaurentPolynomial.T (-1)) =
      detInverse K n :=
  generalLinearDeterminantCoordinateMap_inverse K n

private theorem testNativeComultiplication :
    Coalgebra.comul (R := K) (matrix K n).det =
      (matrix K n).det ⊗ₜ[K] (matrix K n).det :=
  generalLinearDeterminant_comul K n

private theorem testNativeCounit :
    Coalgebra.counit (R := K) (matrix K n).det = 1 :=
  generalLinearDeterminant_counit K n

private theorem testNativeAntipode :
    HopfAlgebra.antipode K (matrix K n).det = detInverse K n :=
  generalLinearDeterminant_antipode K n

private theorem testUnderlyingAffineMap :
    (generalLinearDeterminantSchemeHom K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantCoordinateMap K n).toRingHom) :=
  generalLinearDeterminantSchemeHom_left K n

private theorem testPoint (g : Matrix.GeneralLinearGroup n R) :
    generalLinearGroupMulEquivPoints K n R g ≫
        (generalLinearDeterminantSchemeHom K n).hom.hom =
      multiplicativeGroupMulEquivPoints K R (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point K n R g

private theorem testCoefficientNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (g : Matrix.GeneralLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Units.map f (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_natural K n R f g

private def testFunctorNaturality :
    generalLinearGroupFunctor K n ⟶ multiplicativeGroupFunctor K :=
  generalLinearDeterminantFunctorHom K n

private theorem testEmptyIndexPoint (g : Matrix.GeneralLinearGroup Empty ℤ) :
    generalLinearGroupMulEquivPoints ℤ Empty ℤ g ≫
        (generalLinearDeterminantSchemeHom ℤ Empty).hom.hom =
      multiplicativeGroupMulEquivPoints ℤ ℤ (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point ℤ Empty ℤ g

private theorem testZeroRingPoint (g : Matrix.GeneralLinearGroup (Fin 0) (ZMod 1)) :
    generalLinearGroupMulEquivPoints (ZMod 1) (Fin 0) (ZMod 1) g ≫
        (generalLinearDeterminantSchemeHom (ZMod 1) (Fin 0)).hom.hom =
      multiplicativeGroupMulEquivPoints (ZMod 1) (ZMod 1)
        (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point (ZMod 1) (Fin 0) (ZMod 1) g

private theorem testNonflatCoefficientNaturality (g : Matrix.GeneralLinearGroup (Fin 1) ℤ) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ (ZMod 2)) g) =
      Units.map (algebraMap ℤ (ZMod 2)) (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_natural ℤ (Fin 1) ℤ (Algebra.ofId ℤ (ZMod 2)) g

private def negativeOneMatrix : Matrix.GeneralLinearGroup (Fin 1) ℤ :=
  Matrix.GeneralLinearGroup.mk'' !![-1] (by norm_num)

private theorem testNegativeOnePoint :
    generalLinearGroupMulEquivPoints ℤ (Fin 1) ℤ negativeOneMatrix ≫
        (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom =
      multiplicativeGroupMulEquivPoints ℤ ℤ (-1 : ℤˣ) := by
  rw [generalLinearDeterminant_point]
  congr 1
  apply Units.ext
  norm_num [negativeOneMatrix, Matrix.GeneralLinearGroup.val_det_apply]

private theorem testNegativeOneNonidentity :
    Matrix.GeneralLinearGroup.det negativeOneMatrix ≠ (1 : ℤˣ) := by
  intro h
  have hval := congrArg (fun unit : ℤˣ ↦ (unit : ℤ)) h
  norm_num [negativeOneMatrix, Matrix.GeneralLinearGroup.val_det_apply] at hval

end AlgebraicGeometry
