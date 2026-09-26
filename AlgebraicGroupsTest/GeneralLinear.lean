/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.GeneralLinear
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# Finite-matrix general-linear regression clients

Named private declarations retain the original examples, including empty index
types, zero target rings, noncommuting matrices and polynomial evaluation.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
variable (n : Type u) [Fintype n] [DecidableEq n]

private theorem testFinitePresentation : Algebra.FinitePresentation K (CoordinateRing K n) :=
  inferInstance

private abbrev testHopfAlgebra : HopfAlgebra K (CoordinateRing K n) := inferInstance

private theorem testLocallyOfFiniteType :
    LocallyOfFiniteType (generalLinearGroupUnderlyingScheme K n).hom :=
  inferInstance

private theorem testQuasiCompact :
    QuasiCompact (generalLinearGroupUnderlyingScheme K n).hom := inferInstance

private def testMulEquivAlgHom : Matrix.GeneralLinearGroup n R ≃*
    WithConv (CoordinateRing K n →ₐ[K] R) :=
  generalLinearGroupMulEquivAlgHom K n R

private def testMulEquivPoints : Matrix.GeneralLinearGroup n R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ generalLinearGroupUnderlyingScheme K n) :=
  generalLinearGroupMulEquivPoints K n R

private def testPointsIso : generalLinearGroupFunctor K n ≅ generalLinearGroupPointsFunctor K n :=
  generalLinearGroupPointsIso K n

private theorem testAlgHomEntry (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    (generalLinearGroupMulEquivAlgHom K n R g).ofConv (matrix K n i j) = g i j :=
  generalLinearGroupMulEquivAlgHom_apply_matrix K n R g i j

private theorem testAlgHomDetInverse (g : Matrix.GeneralLinearGroup n R) :
    (generalLinearGroupMulEquivAlgHom K n R g).ofConv (detInverse K n) =
      ↑(Matrix.GeneralLinearGroup.det g)⁻¹ :=
  generalLinearGroupMulEquivAlgHom_apply_detInverse K n R g

private theorem testPointEntry (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K n R g).left).hom
      (matrix K n i j) = g i j :=
  generalLinearGroupPoint_preimage_entry K n R g i j

private theorem testPointDetInverse (g : Matrix.GeneralLinearGroup n R) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K n R g).left).hom
      (detInverse K n) = ↑(Matrix.GeneralLinearGroup.det g)⁻¹ :=
  generalLinearGroupPoint_preimage_detInverse K n R g

private theorem testQuotientEntry (i j : n) :
    (quotientEquiv K n).symm (AdjoinRoot.of _ (MvPolynomial.X (i, j))) =
      matrix K n i j := quotientEquiv_symm_entry K n i j

private theorem testQuotientInverseVariable :
    (quotientEquiv K n).symm
      (AdjoinRoot.root (Polynomial.C (determinant K n) * Polynomial.X - 1)) =
        detInverse K n := quotientEquiv_symm_inverseVariable K n

private theorem testComulEntry (i j : n) :
    Coalgebra.comul (R := K) (matrix K n i j) =
      ∑ index : n, matrix K n i index ⊗ₜ[K] matrix K n index j :=
  native_comul_matrix K n i j

private theorem testComulInverse :
    Coalgebra.comul (R := K) (detInverse K n) =
      detInverse K n ⊗ₜ[K] detInverse K n := native_comul_detInverse K n

private theorem testAntipodeEntry (i j : n) :
    HopfAlgebra.antipode K (matrix K n i j) =
      detInverse K n * (matrix K n).adjugate i j := by
  rw [native_antipode_matrix]
  exact universal_inv_apply K n i j

private theorem testEvaluateNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S)
    (g : Matrix.GeneralLinearGroup n R) :
    evaluate (K := K) (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      f.comp (evaluate (K := K) g) := evaluate_natural f g

private theorem testConvolutionEntry (f g : CoordinateRing K n →ₐ[K] R) (i j : n) :
    ((WithConv.toConv f * WithConv.toConv g).ofConv) (matrix K n i j) =
      ∑ index : n, f (matrix K n i index) * g (matrix K n index j) :=
  generalLinearConvMul_matrix K n R f g i j

/-- Retain the original stronger-context regression, although the equivalence works for any target. -/
@[nolint unusedArguments]
private def testSubsingletonMulEquiv [Subsingleton R] : Matrix.GeneralLinearGroup n R ≃*
    WithConv (CoordinateRing K n →ₐ[K] R) :=
  generalLinearGroupMulEquivAlgHom K n R

private def testZModTwoMulEquiv : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃*
    WithConv (CoordinateRing (ZMod 2) (Fin 2) →ₐ[ZMod 2] ZMod 2) :=
  generalLinearGroupMulEquivAlgHom (ZMod 2) (Fin 2) (ZMod 2)

private def testEmptyZModOneMulEquiv : Matrix.GeneralLinearGroup Empty (ZMod 1) ≃*
    WithConv (CoordinateRing (ZMod 1) Empty →ₐ[ZMod 1] ZMod 1) :=
  generalLinearGroupMulEquivAlgHom (ZMod 1) Empty (ZMod 1)

private def testZModOnePoints : Matrix.GeneralLinearGroup (Fin 1) (ZMod 1) ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      generalLinearGroupUnderlyingScheme ℤ (Fin 1)) :=
  generalLinearGroupMulEquivPoints ℤ (Fin 1) (ZMod 1)

private def upper : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.upperRightHom (1 : ℤ)

private def lower : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.mk'' !![1, 0; 1, 1]
    (by norm_num [Matrix.det_fin_two])

private theorem order_detection :
    (generalLinearGroupMulEquivAlgHom ℤ (Fin 2) ℤ (upper * lower)).ofConv
      (matrix ℤ (Fin 2) 0 0) = 2 ∧
    (generalLinearGroupMulEquivAlgHom ℤ (Fin 2) ℤ (lower * upper)).ofConv
      (matrix ℤ (Fin 2) 0 0) = 1 := by
  constructor <;> rw [generalLinearGroupMulEquivAlgHom_apply_matrix]
  all_goals norm_num [upper, lower, Matrix.GeneralLinearGroup.upperRightHom,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem order_not_commutative : upper * lower ≠ lower * upper := by
  intro h
  have test := order_detection
  rw [h] at test
  omega

private def polynomialTestMap : Polynomial ℤ →ₐ[ℤ] ℤ := Polynomial.aeval 2

private theorem polynomialTestMap_nonidentity :
    polynomialTestMap Polynomial.X = 2 := by simp [polynomialTestMap]

private theorem polynomial_test_naturality :
    evaluate (K := ℤ)
      (Matrix.GeneralLinearGroup.map polynomialTestMap.toRingHom
        (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ))) =
      polynomialTestMap.comp
        (evaluate (K := ℤ)
          (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ))) :=
  evaluate_natural polynomialTestMap _

private theorem polynomial_test_entry :
    (Matrix.GeneralLinearGroup.map polynomialTestMap.toRingHom
      (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ))) 0 1 = 2 := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  change polynomialTestMap
    ((Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ) :
      Matrix.GeneralLinearGroup (Fin 2) (Polynomial ℤ)) 0 1) = 2
  exact polynomialTestMap_nonidentity

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (K R : Type) [CommRing K] [CommRing R] [Algebra K R]

private def testEmptyIndexMulEquiv : Matrix.GeneralLinearGroup Empty R ≃*
    WithConv (CoordinateRing K Empty →ₐ[K] R) :=
  generalLinearGroupMulEquivAlgHom K Empty R

private def testFinOneIndexMulEquiv : Matrix.GeneralLinearGroup (Fin 1) R ≃*
    WithConv (CoordinateRing K (Fin 1) →ₐ[K] R) :=
  generalLinearGroupMulEquivAlgHom K (Fin 1) R

end AlgebraicGeometry
