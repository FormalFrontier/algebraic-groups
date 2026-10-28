/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant

/-!
# Determinant-character tests

These clients check coordinate and point formulas, empty indices, zero rings, and reduction
of coefficients from the integers to `ZMod 2`.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory TauCeti.GeneralLinear TauCeti.DiagonalizableGroup
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
variable (R : Type u) [CommRing R] [Algebra K R]

private def testDeterminantBialgebraMorphism :
    MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐc[K]
      coordinateHopfAlgebra K (Fintype.card n) :=
  (generalLinearDeterminantSchemeCoordinateMap K n).hom

private def testDeterminantGroupSchemeMorphism :
    groupScheme K (Fintype.card n) ⟶ multiplicativeGroupScheme K :=
  generalLinearDeterminantSchemeHom K n

private theorem testCoordinate :
    (generalLinearDeterminantSchemeCoordinateMap K n).hom
      (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1) =
      (reindexedGenericMatrix K n).det :=
  generalLinearDeterminantSchemeCoordinateMap_generator K n

private theorem testInverseCoordinate :
    (generalLinearDeterminantSchemeCoordinateMap K n).hom
        (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-1 : ℤ))) 1) =
      Ring.inverse (reindexedGenericMatrix K n).det := by
  let unit := (MonoidAlgebra.of K (ULift.{u} (Multiplicative ℤ))).toHomUnits
    (ULift.up (Multiplicative.ofAdd (1 : ℤ)))
  have hinv : Ring.inverse
      (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) (1 : K)) =
      MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-1 : ℤ))) 1 :=
    Ring.inverse_unit unit
  have hunit : IsUnit
      (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) (1 : K)) := unit.isUnit
  rw [← hinv, hunit.map_ringInverse,
    generalLinearDeterminantSchemeCoordinateMap_generator]

private theorem testNativeComultiplication :
    Coalgebra.comul (R := K) (reindexedGenericMatrix K n).det =
      (reindexedGenericMatrix K n).det ⊗ₜ[K] (reindexedGenericMatrix K n).det :=
by
  rw [generalLinearReindexedGenericMatrix_det]
  exact (determinantGroupLike K (Fintype.card n)).isGroupLikeElem_val.comul_eq_tmul_self

private theorem testNativeCounit :
    Coalgebra.counit (R := K) (reindexedGenericMatrix K n).det = 1 :=
by
  rw [generalLinearReindexedGenericMatrix_det]
  exact (determinantGroupLike K (Fintype.card n)).isGroupLikeElem_val.counit_eq_one

private theorem testNativeAntipode :
    HopfAlgebra.antipode K (reindexedGenericMatrix K n).det =
      Ring.inverse (reindexedGenericMatrix K n).det :=
by
  rw [generalLinearReindexedGenericMatrix_det]
  exact (Ring.inverse_unit ((GroupLike.toUnits K)
    (determinantGroupLike K (Fintype.card n)))).symm

omit [DecidableEq n] in
private theorem testUnderlyingAffineMap :
    (generalLinearDeterminantSchemeHom K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom.toRingHom) :=
by
  classical
  exact generalLinearDeterminantSchemeHom_left K n

private theorem testPoint (g : Matrix.GeneralLinearGroup n R) :
    groupSchemePointMulEquiv (Fintype.card n) R ((reindexedPointsMulEquiv K n R).symm g) ≫
        (generalLinearDeterminantSchemeHom K n).hom.hom =
      (multiplicativeGroupSchemePointsMulEquiv (R := K) (A := R)).symm
        (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point K n R g

private theorem testCoefficientNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (g : Matrix.GeneralLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Units.map f (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det f.toRingHom g

private def testFunctorNaturality :
    generalLinearIndexedFunctor K n ⟶ multiplicativeGroupFunctor K :=
  generalLinearDeterminantFunctorHom K n

private theorem testEmptyIndexPoint (g : Matrix.GeneralLinearGroup Empty ℤ) :
    groupSchemePointMulEquiv (Fintype.card Empty) ℤ
      ((reindexedPointsMulEquiv ℤ Empty ℤ).symm g) ≫
        (generalLinearDeterminantSchemeHom ℤ Empty).hom.hom =
      (multiplicativeGroupSchemePointsMulEquiv (R := ℤ) (A := ℤ)).symm
        (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point ℤ Empty ℤ g

private theorem testZeroRingPoint (g : Matrix.GeneralLinearGroup (Fin 0) (ZMod 1)) :
    groupSchemePointMulEquiv (Fintype.card (Fin 0)) (ZMod 1)
      ((reindexedPointsMulEquiv (ZMod 1) (Fin 0) (ZMod 1)).symm g) ≫
        (generalLinearDeterminantSchemeHom (ZMod 1) (Fin 0)).hom.hom =
      (multiplicativeGroupSchemePointsMulEquiv (R := (ZMod 1)) (A := (ZMod 1))).symm
        (Matrix.GeneralLinearGroup.det g) :=
  generalLinearDeterminant_point (ZMod 1) (Fin 0) (ZMod 1) g

/-- Reduction of a one-by-one invertible integer matrix modulo two commutes with determinant. -/
public theorem generalLinearGroup_det_map_int_zmod_two_fin_one
    (g : Matrix.GeneralLinearGroup (Fin 1) ℤ) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ (ZMod 2)) g) =
      Units.map (algebraMap ℤ (ZMod 2)) (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det (algebraMap ℤ (ZMod 2)) g

private def negativeOneMatrix : Matrix.GeneralLinearGroup (Fin 1) ℤ :=
  Matrix.GeneralLinearGroup.mk'' !![-1] (by norm_num)

private theorem testNegativeOnePoint :
    groupSchemePointMulEquiv (Fintype.card (Fin 1)) ℤ
      ((reindexedPointsMulEquiv ℤ (Fin 1) ℤ).symm negativeOneMatrix) ≫
        (generalLinearDeterminantSchemeHom ℤ (Fin 1)).hom.hom =
      (multiplicativeGroupSchemePointsMulEquiv (R := ℤ) (A := ℤ)).symm (-1 : ℤˣ) := by
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
