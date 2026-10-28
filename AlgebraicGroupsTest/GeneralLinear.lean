/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinear
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Determinant

/-!
# Finite-matrix general-linear regression clients

The named convolution-entry test records matrix multiplication on coordinates.
Private clients include empty index types, zero target rings, noncommuting matrices
and polynomial evaluation.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory TauCeti.GeneralLinear
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
variable (n : Type u) [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem testFinitePresentation : Algebra.FinitePresentation K (coordinateHopfAlgebra K
    (Fintype.card n)) :=
  inferInstance

private abbrev testHopfAlgebra : HopfAlgebra K (coordinateHopfAlgebra K (Fintype.card n)) :=
    inferInstance

omit [DecidableEq n] in
private theorem testLocallyOfFiniteType :
    LocallyOfFiniteType ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).hom :=
  inferInstance

omit [DecidableEq n] in
private theorem testQuasiCompact :
    QuasiCompact ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).hom := inferInstance

private def testMulEquivAlgHom : Matrix.GeneralLinearGroup n R ≃*
    WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] R) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm

private def testMulEquivPoints : Matrix.GeneralLinearGroup n R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (TauCeti.GeneralLinear.groupScheme K (Fintype.card
        n)).X) :=
  ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm.trans
      (TauCeti.GeneralLinear.groupSchemePointMulEquiv (R := K) (Fintype.card n) R))

private def testPointsIso : generalLinearIndexedFunctor K n ≅
    TauCeti.GroupScheme.algebraPointsFunctor K (TauCeti.GeneralLinear.groupScheme K
    (Fintype.card n)) :=
  generalLinearIndexedPointsIso K n

private theorem testAlgHomEntry (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g).ofConv
        (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) = g i j :=
  reindexedPointsMulEquiv_symm_apply K n R g i j

private theorem testAlgHomDetInverse (g : Matrix.GeneralLinearGroup n R) :
    ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g).ofConv ((Ring.inverse
        (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det)) =
      ↑(Matrix.GeneralLinearGroup.det g)⁻¹ :=
  reindexedPointsMulEquiv_symm_apply_ringInverse_det K n R g

private theorem testPointEntry (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    (Spec.preimage (((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm.trans
        (TauCeti.GeneralLinear.groupSchemePointMulEquiv (R := K) (Fintype.card n) R)) g).left).hom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) = g i j :=
by
  rw [MulEquiv.trans_apply, groupSchemePointMulEquiv_apply_left]
  erw [Spec.preimage_map]
  exact reindexedPointsMulEquiv_symm_apply K n R g i j

private theorem testPointDetInverse (g : Matrix.GeneralLinearGroup n R) :
    (Spec.preimage (((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm.trans
        (TauCeti.GeneralLinear.groupSchemePointMulEquiv (R := K) (Fintype.card n) R)) g).left).hom
      ((Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det)) =
          ↑(Matrix.GeneralLinearGroup.det g)⁻¹ :=
by
  rw [MulEquiv.trans_apply, groupSchemePointMulEquiv_apply_left]
  erw [Spec.preimage_map]
  exact reindexedPointsMulEquiv_symm_apply_ringInverse_det K n R g

omit [DecidableEq n] in
private theorem testQuotientEntry (i j : Fin (Fintype.card n)) :
    (Localization.awayEquivAdjoin
      (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det).symm
        (AdjoinRoot.of _ (MvPolynomial.X (i, j))) =
      coordinateRingMap K (Fintype.card n) (MvPolynomial.X (i, j)) := by
  rw [coordinateRingMap_apply]
  exact (Localization.awayEquivAdjoin
    (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det).symm.commutes
      (MvPolynomial.X (i, j))

omit [DecidableEq n] in
private theorem testQuotientInverseVariable :
    (Localization.awayEquivAdjoin
      (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det).symm
        (AdjoinRoot.root _) =
      IsLocalization.Away.invSelf
        (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det := by
  rw [Localization.awayEquivAdjoin, AlgEquiv.ofAlgHom_symm_apply]
  erw [AdjoinRoot.liftAlgHom_root]

omit [DecidableEq n] in
private theorem testComulEntry (i j : n) :
    Coalgebra.comul (R := K) (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) =
      ∑ index : n, TauCeti.GeneralLinear.reindexedGenericMatrix K n i index ⊗ₜ[K]
          TauCeti.GeneralLinear.reindexedGenericMatrix K n index j :=
  reindexedGenericMatrix_comul K n i j

private theorem testComulInverse :
    Coalgebra.comul (R := K) ((Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K
        n).det)) =
      (Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det) ⊗ₜ[K] (Ring.inverse
          (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det) := by
  have hd : (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det =
      (determinantGroupLike K (Fintype.card n) :
        coordinateHopfAlgebra K (Fintype.card n)) := by
    have hmatrix : genericMatrix K (Fintype.card n) =
        (localizedGenericMatrix K (Fintype.card n)).map
          (coordinateHopfAlgebraAlgEquiv K (Fintype.card n)) := by
      ext i j
      simp only [genericMatrix_apply, Matrix.map_apply, localizedGenericMatrix_apply]
    rw [reindexedGenericMatrix, Matrix.det_reindex_self, hmatrix,
      ← AlgEquiv.mapMatrix_apply, ← AlgEquiv.map_det, determinantGroupLike_val]
  have hg := (determinantGroupLike K (Fintype.card n)).isGroupLikeElem_val
  rw [← hd] at hg
  have hs : HopfAlgebra.antipode K (reindexedGenericMatrix K n).det =
      Ring.inverse (reindexedGenericMatrix K n).det := by
    apply hg.isUnit.mul_left_cancel
    rw [hg.mul_antipode_cancel, Ring.mul_inverse_cancel _ hg.isUnit]
  simpa only [hs] using hg.antipode.comul_eq_tmul_self


private theorem testAntipodeEntry (i j : n) :
    HopfAlgebra.antipode K (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) =
      (Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det) *
          (TauCeti.GeneralLinear.reindexedGenericMatrix K n).adjugate i j := by
  calc
    _ = (reindexedGenericMatrix K n)⁻¹ i j := by
      rw [reindexedGenericMatrix, Matrix.inv_reindex]
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [genericMatrix_apply, coordinateHopfAlgebra_antipode_X, genericMatrix_inv_apply]
    _ = _ := by rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]

private theorem testEvaluateNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (g : Matrix.GeneralLinearGroup n R) :
    ((reindexedPointsMulEquiv K n S).symm
      (Matrix.GeneralLinearGroup.map f.toRingHom g)).ofConv =
      f.comp ((reindexedPointsMulEquiv K n R).symm g).ofConv := by
  have h := mapValue_reindexedPointsMulEquiv_symm_apply K n f g
  rw [AlgHom.mapValue_apply] at h
  exact (congrArg WithConv.ofConv h).symm

omit [DecidableEq n] in
/-- Convolution of coordinate algebra maps evaluates a matrix entry by matrix multiplication. -/
public theorem generalLinearGroup_convolution_entry
    (f g : coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] R) (i j : n) :
    ((WithConv.toConv f * WithConv.toConv g).ofConv)
        (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) =
      ∑ index : n, f (TauCeti.GeneralLinear.reindexedGenericMatrix K n i index) * g
          (TauCeti.GeneralLinear.reindexedGenericMatrix K n index j) :=
by
  classical
  have h := congrArg (fun q : Matrix.GeneralLinearGroup n R => q i j)
    ((reindexedPointsMulEquiv K n R).map_mul (WithConv.toConv f) (WithConv.toConv g))
  simpa only [reindexedPointsMulEquiv_apply, WithConv.ofConv_toConv,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply] using h

/-- The equivalence works for every target, including subsingleton algebras. -/
private def testSubsingletonMulEquiv : Matrix.GeneralLinearGroup n R ≃*
    WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] R) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm

private def testZModTwoMulEquiv : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃*
    WithConv (coordinateHopfAlgebra (ZMod 2) 2 →ₐ[ZMod 2] ZMod 2) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv (ZMod 2) (Fin 2) (ZMod 2)).symm

private def testEmptyZModOneMulEquiv : Matrix.GeneralLinearGroup Empty (ZMod 1) ≃*
    WithConv (coordinateHopfAlgebra (ZMod 1) 0 →ₐ[ZMod 1] ZMod 1) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv (ZMod 1) Empty (ZMod 1)).symm

private def testZModOnePoints : Matrix.GeneralLinearGroup (Fin 1) (ZMod 1) ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      (TauCeti.GeneralLinear.groupScheme ℤ (Fintype.card (Fin 1))).X) :=
  ((TauCeti.GeneralLinear.reindexedPointsMulEquiv ℤ (Fin 1) (ZMod 1)).symm.trans
      (TauCeti.GeneralLinear.groupSchemePointMulEquiv (R := ℤ) (Fintype.card (Fin 1)) (ZMod 1)))

private def upper : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.upperRightHom (1 : ℤ)

private def lower : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.mk'' !![1, 0; 1, 1]
    (by norm_num [Matrix.det_fin_two])

private theorem order_detection :
    ((TauCeti.GeneralLinear.reindexedPointsMulEquiv ℤ (Fin 2) ℤ).symm (upper * lower)).ofConv
      (reindexedGenericMatrix ℤ (Fin 2) 0 0) = 2 ∧
    ((TauCeti.GeneralLinear.reindexedPointsMulEquiv ℤ (Fin 2) ℤ).symm (lower * upper)).ofConv
      (reindexedGenericMatrix ℤ (Fin 2) 0 0) = 1 := by
  constructor <;> rw [reindexedPointsMulEquiv_symm_apply]
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
    ((reindexedPointsMulEquiv ℤ (Fin 2) ℤ).symm
      (Matrix.GeneralLinearGroup.map polynomialTestMap.toRingHom
        (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ)))).ofConv =
      polynomialTestMap.comp
        ((reindexedPointsMulEquiv ℤ (Fin 2) (Polynomial ℤ)).symm
          (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ))).ofConv :=
  testEvaluateNaturality ℤ (Polynomial ℤ) (Fin 2) polynomialTestMap _

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
    WithConv (coordinateHopfAlgebra K 0 →ₐ[K] R) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv K Empty R).symm

private def testFinOneIndexMulEquiv : Matrix.GeneralLinearGroup (Fin 1) R ≃*
    WithConv (coordinateHopfAlgebra K 1 →ₐ[K] R) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv K (Fin 1) R).symm

end AlgebraicGeometry
