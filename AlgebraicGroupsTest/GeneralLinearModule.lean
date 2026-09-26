/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

set_option warningAsError true

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry.GeneralLinearModuleTest

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (R S T : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing T] [Algebra K T] (g : R →ₐ[K] S) (h : S →ₐ[K] T)

private theorem arbitraryModuleEndAndInverse
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModuleBaseChange K V R S g f).val = endBaseChange K V R S g f.val ∧
      (generalLinearModuleBaseChange K V R S g f).inv = endBaseChange K V R S g f.inv :=
  ⟨generalLinearModuleBaseChange_val K V R S g f,
   generalLinearModuleBaseChange_inv K V R S g f⟩

private theorem arbitraryModuleAction
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (v : V) (s : S) :
    (generalLinearModuleBaseChange K V R S g f).val (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f.val (1 ⊗ₜ[K] v)) :=
  generalLinearModuleBaseChange_tmul K V R S g f s v

private theorem arbitraryModuleComposition
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleBaseChange K V S T h (generalLinearModuleBaseChange K V R S g f) =
      generalLinearModuleBaseChange K V R T (h.comp g) f :=
  generalLinearModuleBaseChange_comp K V R S T g h f

private theorem literalOrderAction
    (f : LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R))
    (v : V) (s : S) :
    (sourceOrderedGeneralLinearBaseChange K V R S g f).val
        (sourceOrderedTmul K V S v s) =
      (sourceOrderedCanonicalLinearEquiv K V S).symm
        (s • (g.toLinearMap.rTensor V)
          ((sourceOrderedGeneralLinearEquiv K V R f).val (1 ⊗ₜ[K] v))) :=
  sourceOrderedGeneralLinearBaseChange_tmul K V R S g f v s

variable (indexType : Type u) [Fintype indexType] [DecidableEq indexType]
  (basis otherBasis : Module.Basis indexType K V)

private theorem arbitraryAlgebraMatrixNaturality
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleMatrixEquiv K V indexType basis S
        (generalLinearModuleBaseChange K V R S g f) =
      Matrix.GeneralLinearGroup.map g.toRingHom
        (generalLinearModuleMatrixEquiv K V indexType basis R f) :=
  generalLinearModuleMatrixEquiv_natural K V indexType basis R S g f

private theorem chosenBasisMatrixMultiplication
    (f j : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleMatrixEquiv K V indexType basis R (f * j) =
      generalLinearModuleMatrixEquiv K V indexType basis R f *
        generalLinearModuleMatrixEquiv K V indexType basis R j :=
  map_mul _ f j

private theorem chosenBasisMatrixInverse
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleMatrixEquiv K V indexType basis R f⁻¹ =
      (generalLinearModuleMatrixEquiv K V indexType basis R f)⁻¹ :=
  map_inv _ f

private theorem chosenBasisVectorAction
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (x : SourceOrderTensor K V R) :
    (generalLinearModuleMatrixEquiv K V indexType basis R f).val *ᵥ
        (generalLinearScalarBasis K V indexType basis R).repr x =
      (generalLinearScalarBasis K V indexType basis R).repr (f.val x) :=
  generalLinearModuleMatrixEquiv_action K V indexType basis R f x

private theorem chosenBasisCoordinateEntry
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (row col : indexType) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K indexType R
      (generalLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
        (matrix K indexType row col) =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f.val ((generalLinearScalarBasis K V indexType basis R) col)) row :=
  generalLinearModulePoint_preimage_entry K V indexType basis R f row col

private theorem chosenBasisCoordinateDetInverse
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K indexType R
      (generalLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
        (detInverse K indexType) =
      ↑(Matrix.GeneralLinearGroup.det
        (generalLinearModuleMatrixEquiv K V indexType basis R f))⁻¹ :=
  generalLinearModulePoint_preimage_detInverse K V indexType basis R f

private theorem twoBasesNaturality (f : Matrix.GeneralLinearGroup indexType R) :
    generalLinearModuleChangeBasis K V indexType basis otherBasis S
        (Matrix.GeneralLinearGroup.map g.toRingHom f) =
      Matrix.GeneralLinearGroup.map g.toRingHom
        (generalLinearModuleChangeBasis K V indexType basis otherBasis R f) :=
  generalLinearModuleChangeBasis_natural K V indexType basis otherBasis R S g f

private theorem twoBasesIdentity :
    generalLinearModuleChangeBasis K V indexType basis basis R = MulEquiv.refl _ :=
  generalLinearModuleChangeBasis_id K V indexType basis R

private theorem twoBasesComposition (thirdBasis : Module.Basis indexType K V) :
    (generalLinearModuleChangeBasis K V indexType basis otherBasis R).trans
        (generalLinearModuleChangeBasis K V indexType otherBasis thirdBasis R) =
      generalLinearModuleChangeBasis K V indexType basis thirdBasis R :=
  generalLinearModuleChangeBasis_comp K V indexType basis otherBasis thirdBasis R

private theorem twoBasesPointAgreement (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModulePointsIso K V indexType otherBasis).hom.app R f =
      (generalLinearGroupPointsIso K indexType).hom.app R
        (generalLinearModuleChangeBasis K V indexType basis otherBasis R
          (generalLinearModuleMatrixEquiv K V indexType basis R f)) :=
  generalLinearModulePointsIso_changeBasis K V indexType basis otherBasis R f

private theorem representedSpecMap (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    ((generalLinearModulePointsIso K V indexType basis).hom.app R f).left =
      Spec.map (CommRingCat.ofHom
        (generalLinearModuleCoordinateEval K V indexType basis R f).toRingHom) :=
  generalLinearModulePointsIso_apply_left K V indexType basis R f

private theorem nonflatPolynomialEvaluation
    (f : LinearMap.GeneralLinearGroup (Polynomial ℤ)
      (SourceOrderTensor ℤ (Fin 2 → ℤ) (Polynomial ℤ))) :
    generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) ℤ
        (generalLinearModuleBaseChange ℤ (Fin 2 → ℤ) (Polynomial ℤ) ℤ
          (Polynomial.aeval (2 : ℤ)) f) =
      Matrix.GeneralLinearGroup.map (Polynomial.aeval (2 : ℤ)).toRingHom
        (generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
          (Pi.basisFun ℤ (Fin 2)) (Polynomial ℤ) f) :=
  generalLinearModuleMatrixEquiv_natural ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (Polynomial ℤ) ℤ (Polynomial.aeval (2 : ℤ)) f

private theorem polynomialEvaluationIsNonidentity :
    Polynomial.aeval (2 : ℤ) (Polynomial.X : Polynomial ℤ) = 2 := by simp

/-- A genuinely nonidentity automorphism whose off-diagonal coordinate is a polynomial. -/
private def polynomialShear :
    LinearMap.GeneralLinearGroup (Polynomial ℤ)
      (SourceOrderTensor ℤ (Fin 2 → ℤ) (Polynomial ℤ)) :=
  (generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (Polynomial ℤ)).symm
      (Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ))

private theorem nonflatPolynomialShearEntry :
    generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) ℤ
        (generalLinearModuleBaseChange ℤ (Fin 2 → ℤ) (Polynomial ℤ) ℤ
          (Polynomial.aeval (2 : ℤ)) polynomialShear) 0 1 = 2 := by
  rw [generalLinearModuleMatrixEquiv_natural, Matrix.GeneralLinearGroup.map_apply]
  have matrix_eq :
      generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) (Polynomial ℤ) polynomialShear =
          Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ) := by
    simp [polynomialShear]
  rw [matrix_eq]
  change Polynomial.aeval (2 : ℤ)
    ((Matrix.GeneralLinearGroup.upperRightHom (Polynomial.X : Polynomial ℤ) :
      Matrix.GeneralLinearGroup (Fin 2) (Polynomial ℤ)) 0 1) = 2
  exact polynomialEvaluationIsNonidentity

private theorem polynomialShear_ne_one : polynomialShear ≠ 1 := by
  intro equality
  have entry := nonflatPolynomialShearEntry
  rw [equality] at entry
  simp at entry

private def emptyBasisOverIntegers :
    LinearMap.GeneralLinearGroup ℤ (SourceOrderTensor ℤ (Fin 0 → ℤ) ℤ) ≃*
      Matrix.GeneralLinearGroup (Fin 0) ℤ :=
  generalLinearModuleMatrixEquiv ℤ (Fin 0 → ℤ) (Fin 0)
    (Module.Basis.empty (Fin 0 → ℤ)) ℤ

private def zeroCoefficientAlgebra :
    LinearMap.GeneralLinearGroup (ZMod 1)
        (SourceOrderTensor ℤ (Fin 2 → ℤ) (ZMod 1)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 1) :=
  generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (ZMod 1)

private def zeroBaseAlgebra :
    LinearMap.GeneralLinearGroup (ZMod 1)
        (SourceOrderTensor (ZMod 1) (Fin 0 → ZMod 1) (ZMod 1)) ≃*
      Matrix.GeneralLinearGroup (Fin 0) (ZMod 1) :=
  generalLinearModuleMatrixEquiv (ZMod 1) (Fin 0 → ZMod 1) (Fin 0)
    (Module.Basis.empty (Fin 0 → ZMod 1)) (ZMod 1)

private theorem zeroTargetNaturality
    (f : LinearMap.GeneralLinearGroup ℤ (SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ)) :
    generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) (ZMod 1)
        (generalLinearModuleBaseChange ℤ (Fin 2 → ℤ) ℤ (ZMod 1)
          (Algebra.ofId ℤ (ZMod 1)) f) =
      Matrix.GeneralLinearGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
        (generalLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
          (Pi.basisFun ℤ (Fin 2)) ℤ f) :=
  generalLinearModuleMatrixEquiv_natural ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) ℤ (ZMod 1) (Algebra.ofId ℤ (ZMod 1)) f

private theorem finiteFieldCoefficients
    (f : LinearMap.GeneralLinearGroup (ZMod 2)
      (SourceOrderTensor (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2))) :
    generalLinearModuleCoordinateEval (ZMod 2) (Fin 2 → ZMod 2) (Fin 2)
        (Pi.basisFun (ZMod 2) (Fin 2)) (ZMod 2)
        f (detInverse (ZMod 2) (Fin 2)) =
      ↑(Matrix.GeneralLinearGroup.det
        (generalLinearModuleMatrixEquiv (ZMod 2) (Fin 2 → ZMod 2) (Fin 2)
          (Pi.basisFun (ZMod 2) (Fin 2)) (ZMod 2) f))⁻¹ :=
  generalLinearModuleCoordinateEval_detInverse (ZMod 2) (Fin 2 → ZMod 2)
    (Fin 2) (Pi.basisFun (ZMod 2) (Fin 2)) (ZMod 2) f

end AlgebraicGeometry.GeneralLinearModuleTest
#print axioms AlgebraicGeometry.endBaseChangeRingHom
#print axioms AlgebraicGeometry.endBaseChangeRingHom_apply
#print axioms AlgebraicGeometry.endCompositionFunctor
#print axioms AlgebraicGeometry.generalLinearModuleFunctor
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange_val
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange_id
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange_comp
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange_inv
#print axioms AlgebraicGeometry.generalLinearModuleBaseChange_tmul
#print axioms AlgebraicGeometry.generalLinearModuleAutomorphisms
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearEquiv
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearEquiv_tmul
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearBaseChange
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearBaseChange_id
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearBaseChange_comp
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearFunctor
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearIso
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearBaseChange_tmul
#print axioms AlgebraicGeometry.generalLinearScalarBasis
#print axioms AlgebraicGeometry.generalLinearScalarBasis_apply
#print axioms AlgebraicGeometry.generalLinearScalarBasis_repr_rTensor
#print axioms AlgebraicGeometry.generalLinearScalarBasis_endBaseChange_matrix
#print axioms AlgebraicGeometry.generalLinearModuleMatrixEquiv
#print axioms AlgebraicGeometry.generalLinearModuleMatrixEquiv_entry
#print axioms AlgebraicGeometry.generalLinearModuleMatrixEquiv_action
#print axioms AlgebraicGeometry.generalLinearModuleMatrixEquiv_natural
#print axioms AlgebraicGeometry.generalLinearModuleMatrixIso
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearMatrixIso
#print axioms AlgebraicGeometry.generalLinearModulePointsIso
#print axioms AlgebraicGeometry.generalLinearModuleCoordinateEval
#print axioms AlgebraicGeometry.generalLinearModuleCoordinateEval_entry
#print axioms AlgebraicGeometry.generalLinearModuleCoordinateEval_detInverse
#print axioms AlgebraicGeometry.generalLinearModulePointsIso_apply_left
#print axioms AlgebraicGeometry.generalLinearModulePoint_preimage_entry
#print axioms AlgebraicGeometry.generalLinearModulePoint_preimage_detInverse
#print axioms AlgebraicGeometry.sourceOrderedGeneralLinearPointsIso
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_apply
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_id
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_comp
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_natural
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasisIso
#print axioms AlgebraicGeometry.generalLinearModulePointsIso_changeBasis
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_entry
#print axioms AlgebraicGeometry.generalLinearModuleChangeBasis_action
#print axioms AlgebraicGeometry.generalLinearModuleMatrixEquiv_endMatrixLinearEquiv
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.arbitraryModuleEndAndInverse
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.arbitraryModuleAction
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.arbitraryModuleComposition
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.literalOrderAction
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.arbitraryAlgebraMatrixNaturality
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.chosenBasisMatrixMultiplication
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.chosenBasisMatrixInverse
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.chosenBasisVectorAction
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.chosenBasisCoordinateEntry
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.chosenBasisCoordinateDetInverse
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.twoBasesNaturality
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.twoBasesIdentity
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.twoBasesComposition
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.twoBasesPointAgreement
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.representedSpecMap
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.nonflatPolynomialEvaluation
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.polynomialEvaluationIsNonidentity
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.polynomialShear
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.nonflatPolynomialShearEntry
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.polynomialShear_ne_one
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.emptyBasisOverIntegers
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.zeroCoefficientAlgebra
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.zeroBaseAlgebra
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.zeroTargetNaturality
#print axioms AlgebraicGeometry.GeneralLinearModuleTest.finiteFieldCoefficients
