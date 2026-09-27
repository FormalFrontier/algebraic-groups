/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinearModule
public import Mathlib.Data.ZMod.Basic

/-!
# Finite-free special linear module clients

These clients exercise the native module automorphisms and the actual represented
points in ranks zero, one and two, including the zero coefficient ring, an
integer shear, scalar extension, and a nontrivial change of basis.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory SpecialLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace AlgebraicGroupsTest.SpecialLinearModule

example : specialLinearModuleFunctor ℤ (Fin 0 → ℤ) ≅
    specialLinearGroupPointsFunctor ℤ (Fin 0) :=
  specialLinearModulePointsIso ℤ (Fin 0 → ℤ) (Fin 0) (Pi.basisFun ℤ (Fin 0))

example : specialLinearModuleFunctor ℤ (Fin 1 → ℤ) ≅
    specialLinearGroupPointsFunctor ℤ (Fin 1) :=
  specialLinearModulePointsIso ℤ (Fin 1 → ℤ) (Fin 1) (Pi.basisFun ℤ (Fin 1))

example (f : SpecialLinearGroup (ZMod 5)
    (SourceOrderTensor ℤ (Fin 1 → ℤ) (ZMod 5))) : f = 1 := by
  apply (specialLinearModuleMatrixEquiv ℤ (Fin 1 → ℤ) (Fin 1)
    (Pi.basisFun ℤ (Fin 1)) (ZMod 5)).injective
  exact Subsingleton.elim _ _

example : specialLinearModuleFunctor ℤ (Fin 2 → ℤ) ≅
    specialLinearGroupPointsFunctor ℤ (Fin 2) :=
  specialLinearModulePointsIso ℤ (Fin 2 → ℤ) (Fin 2) (Pi.basisFun ℤ (Fin 2))

example : SpecialLinearGroup (ZMod 1)
    (SourceOrderTensor ℤ (Fin 0 → ℤ) (ZMod 1)) := 1

example : Matrix.det
    (fun row column ↦ entry ℤ (Fin 0) row column :
      Matrix (Fin 0) (Fin 0) (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 0))) =
        1 :=
  determinant_entry ℤ (Fin 0)

example : (specialLinearModuleCoordinateEval ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) (ZMod 1) 1)
    (quotient ℤ (Fin 0) (GeneralLinearCoordinateRing.detInverse ℤ (Fin 0))) = 1 :=
  specialLinearModuleCoordinateEval_detInverse ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) (ZMod 1) 1

example : (Spec.preimage
    ((specialLinearModulePointsIso ℤ (Fin 0 → ℤ) (Fin 0)
      (Pi.basisFun ℤ (Fin 0))).hom.app (CommAlgCat.of ℤ (ZMod 1)) 1).left).hom
    (quotient ℤ (Fin 0) (GeneralLinearCoordinateRing.detInverse ℤ (Fin 0))) = 1 :=
  specialLinearModulePoint_preimage_detInverse ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) (ZMod 1) 1

example : (specialLinearModulePointsIso ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0))).hom.app (CommAlgCat.of ℤ (ZMod 1)) 1 ≫
      (specialLinearInclusion ℤ (Fin 0)).hom.hom =
    (generalLinearModulePointsIso ℤ (Fin 0 → ℤ) (Fin 0)
      (Pi.basisFun ℤ (Fin 0))).hom.app (CommAlgCat.of ℤ (ZMod 1))
      (1 : SpecialLinearGroup (ZMod 1)
        (SourceOrderTensor ℤ (Fin 0 → ℤ) (ZMod 1))).toGeneralLinearGroup :=
  specialLinearModulePointsIso_inclusion ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) (CommAlgCat.of ℤ (ZMod 1)) 1

/-- Resolve integer-module instance ambiguity with the canonical tensor action. -/
local instance emptyRankTensorModule : Module ℤ (SourceOrderTensor ℤ (Fin 0 → ℤ) ℤ) :=
  TensorProduct.leftModule

example : (specialLinearModuleBaseChange ℤ (Fin 0 → ℤ) ℤ (ZMod 1)
    (Algebra.ofId ℤ (ZMod 1)) (1 : SpecialLinearGroup ℤ
      (SourceOrderTensor ℤ (Fin 0 → ℤ) ℤ))).toGeneralLinearGroup =
    generalLinearModuleBaseChange ℤ (Fin 0 → ℤ) ℤ (ZMod 1)
      (Algebra.ofId ℤ (ZMod 1))
      (1 : SpecialLinearGroup ℤ (SourceOrderTensor ℤ (Fin 0 → ℤ) ℤ)).toGeneralLinearGroup :=
  specialLinearModuleBaseChange_toGL ℤ (Fin 0 → ℤ) ℤ (ZMod 1)
    (Algebra.ofId ℤ (ZMod 1)) 1

example : specialLinearModuleMatrixEquiv ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) (ZMod 1)
    (specialLinearModuleBaseChange ℤ (Fin 0 → ℤ) ℤ (ZMod 1)
      (Algebra.ofId ℤ (ZMod 1))
      (1 : SpecialLinearGroup ℤ (SourceOrderTensor ℤ (Fin 0 → ℤ) ℤ))) =
    Matrix.SpecialLinearGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      (specialLinearModuleMatrixEquiv ℤ (Fin 0 → ℤ) (Fin 0)
        (Pi.basisFun ℤ (Fin 0)) ℤ 1) :=
  specialLinearModuleMatrixEquiv_natural ℤ (Fin 0 → ℤ) (Fin 0)
    (Pi.basisFun ℤ (Fin 0)) ℤ (ZMod 1) (Algebra.ofId ℤ (ZMod 1)) 1

/-- Select the canonical tensor action rather than the generic integer module action. -/
local instance integerShearTensorModule : Module ℤ (SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ) :=
  TensorProduct.leftModule

/-- An actual nonidentity determinant-one automorphism of a rank-two scalar extension. -/
def integerShear : SpecialLinearGroup ℤ
    (SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ) :=
  (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) ℤ).symm
    (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) 1)

theorem integerShear_ne_one : integerShear ≠ 1 := by
  intro equality
  have entryEquality := congrArg
    (fun automorphism : SpecialLinearGroup ℤ
        (SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ) ↦
      specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) ℤ automorphism 0 1) equality
  simp only [map_one] at entryEquality
  norm_num [integerShear, Matrix.SpecialLinearGroup.transvection_coe] at entryEquality

example : (specialLinearModuleCoordinateEval ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) ℤ integerShear) (entry ℤ (Fin 2) 0 1) = 1 := by
  rw [specialLinearModuleCoordinateEval_entry]
  rw [← specialLinearModuleMatrixEquiv_entry]
  norm_num [integerShear, Matrix.SpecialLinearGroup.transvection_coe]

example : specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (ZMod 5)
    (specialLinearModuleBaseChange ℤ (Fin 2 → ℤ) ℤ (ZMod 5)
      (Algebra.ofId ℤ (ZMod 5)) integerShear) 0 1 = 1 := by
  rw [specialLinearModuleMatrixEquiv_natural]
  norm_num [integerShear, Matrix.SpecialLinearGroup.transvection_coe]

example (x : SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ) :
    (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
      (Pi.basisFun ℤ (Fin 2)) ℤ integerShear : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ
        (generalLinearScalarBasis ℤ (Fin 2 → ℤ) (Fin 2) (Pi.basisFun ℤ (Fin 2)) ℤ).repr x =
      (generalLinearScalarBasis ℤ (Fin 2 → ℤ) (Fin 2) (Pi.basisFun ℤ (Fin 2)) ℤ).repr
        (integerShear x) :=
  specialLinearModuleMatrixEquiv_action ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) ℤ integerShear x

example : specialLinearModuleCoordinateEval ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (ZMod 5)
      (specialLinearModuleBaseChange ℤ (Fin 2 → ℤ) ℤ (ZMod 5)
        (Algebra.ofId ℤ (ZMod 5)) integerShear) =
    (Algebra.ofId ℤ (ZMod 5)).comp
      (specialLinearModuleCoordinateEval ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) ℤ integerShear) :=
  specialLinearModuleCoordinateEval_natural ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) ℤ (ZMod 5) (Algebra.ofId ℤ (ZMod 5)) integerShear

/-- Swapping the two coordinate vectors gives a genuinely different basis. -/
def swappedBasis : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) :=
  (Pi.basisFun ℤ (Fin 2)).reindex (Equiv.swap 0 1)

theorem swappedBasis_ne_standard : swappedBasis ≠ Pi.basisFun ℤ (Fin 2) := by
  intro equality
  have entryEquality := congrArg
    (fun coordinates : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) ↦ coordinates 0 0)
    equality
  norm_num [swappedBasis, Module.Basis.reindex_apply, Pi.basisFun_apply] at entryEquality

example : specialLinearModuleChangeBasis ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ
    (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
      (Pi.basisFun ℤ (Fin 2)) ℤ integerShear) =
    specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
      swappedBasis ℤ integerShear :=
  specialLinearModuleChangeBasis_apply ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ integerShear

example (x : SourceOrderTensor ℤ (Fin 2 → ℤ) ℤ) :
    (specialLinearModuleChangeBasis ℤ (Fin 2 → ℤ) (Fin 2)
      (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ
      (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) ℤ integerShear) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ
        (generalLinearScalarBasis ℤ (Fin 2 → ℤ) (Fin 2) swappedBasis ℤ).repr x =
      (generalLinearScalarBasis ℤ (Fin 2 → ℤ) (Fin 2) swappedBasis ℤ).repr
        (integerShear x) :=
  specialLinearModuleChangeBasis_action ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ integerShear x

example : specialLinearModuleChangeBasis ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) swappedBasis (ZMod 5)
      (Matrix.SpecialLinearGroup.map (Algebra.ofId ℤ (ZMod 5)).toRingHom
        (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
          (Pi.basisFun ℤ (Fin 2)) ℤ integerShear)) =
    Matrix.SpecialLinearGroup.map (Algebra.ofId ℤ (ZMod 5)).toRingHom
      (specialLinearModuleChangeBasis ℤ (Fin 2 → ℤ) (Fin 2)
        (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ
        (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
          (Pi.basisFun ℤ (Fin 2)) ℤ integerShear)) :=
  specialLinearModuleChangeBasis_natural ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) swappedBasis ℤ (ZMod 5)
    (Algebra.ofId ℤ (ZMod 5))
    (specialLinearModuleMatrixEquiv ℤ (Fin 2 → ℤ) (Fin 2)
      (Pi.basisFun ℤ (Fin 2)) ℤ integerShear)

example : (specialLinearModulePointsIso ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2))).hom.app (CommAlgCat.of ℤ ℤ) integerShear ≫
      (specialLinearInclusion ℤ (Fin 2)).hom.hom =
    (generalLinearModulePointsIso ℤ (Fin 2 → ℤ) (Fin 2)
      (Pi.basisFun ℤ (Fin 2))).hom.app (CommAlgCat.of ℤ ℤ)
      integerShear.toGeneralLinearGroup :=
  specialLinearModulePointsIso_inclusion ℤ (Fin 2 → ℤ) (Fin 2)
    (Pi.basisFun ℤ (Fin 2)) (CommAlgCat.of ℤ ℤ) integerShear

end AlgebraicGroupsTest.SpecialLinearModule

#lint
