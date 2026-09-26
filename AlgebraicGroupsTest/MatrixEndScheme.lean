/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.MatrixEndScheme
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Polynomial.Basic

public section

set_option warningAsError true

noncomputable section

open CategoryTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u

section AnyModule

variable (K V R S T : Type u) [CommRing K] [AddCommGroup V] [Module K V]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing T] [Algebra K T]

private theorem persistentTestMatrixEndScheme001 (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChangeAddHom K V R S g f =
      sourceOrderedEndBaseChange K V R S g f := rfl

theorem matrixEndSchemeTest_add (g : R →ₐ[K] S)
    (f h : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V R S g (f + h) =
      sourceOrderedEndBaseChange K V R S g f +
        sourceOrderedEndBaseChange K V R S g h :=
  (sourceOrderedEndBaseChangeAddHom K V R S g).map_add f h

private theorem persistentTestMatrixEndScheme002 (g : R →ₐ[K] S) :
    sourceOrderedEndBaseChange K V R S g
      (0 : Module.End R (SourceOrderedTensor K V R)) = 0 :=
  (sourceOrderedEndBaseChangeAddHom K V R S g).map_zero

private theorem persistentTestMatrixEndScheme003 (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V R S g (-f) =
      -sourceOrderedEndBaseChange K V R S g f :=
  (sourceOrderedEndBaseChangeAddHom K V R S g).map_neg f

private theorem persistentTestMatrixEndScheme004 (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V S T h (sourceOrderedEndBaseChange K V R S g f) =
      sourceOrderedEndBaseChange K V R T (h.comp g) f :=
  sourceOrderedEndBaseChange_comp K V R S T g h f

private theorem persistentTestMatrixEndScheme005 (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V R R (AlgHom.id K R) f = f := by simp

private theorem persistentTestMatrixEndScheme006 (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R))
    (v : V) (s : S) :
    sourceOrderedCanonicalLinearEquiv K V S
        (sourceOrderedEndBaseChange K V R S g f (sourceOrderedTmul K V S v s)) =
      s • (g.toLinearMap.rTensor V)
        (sourceOrderedCanonicalLinearEquiv K V R
          (f (sourceOrderedTmul K V R v 1))) :=
  sourceOrderedEndBaseChange_tmul K V R S g f v s

end AnyModule

section Functor

variable (K V R S : Type u) [Field K] [AddCommGroup V] [Module K V]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

private noncomputable def persistentTestMatrixEndScheme007 : CommAlgCat K ⥤ GrpCat := sourceOrderedAdditiveEndFunctor K V

private noncomputable def persistentTestMatrixEndScheme008 : sourceOrderedAdditiveEndFunctor K V ≅ additiveEndFunctor K V :=
  sourceOrderedEndGroupIso K V

private theorem persistentTestMatrixEndScheme009 (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedAdditiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd f) =
      .ofAdd (sourceOrderedEndBaseChange K V R S g f) := rfl

private theorem persistentTestMatrixEndScheme010 (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedEndGroupIso K V).hom.app (CommAlgCat.of K S)
      ((sourceOrderedAdditiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd f)) =
      (additiveEndFunctor K V).map (CommAlgCat.ofHom g)
        ((sourceOrderedEndGroupIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f)) :=
  congrArg (fun q : (sourceOrderedAdditiveEndFunctor K V).obj (CommAlgCat.of K R) ⟶
      (additiveEndFunctor K V).obj (CommAlgCat.of K S) ↦
        q (Multiplicative.ofAdd f))
    ((sourceOrderedEndGroupIso K V).hom.naturality (CommAlgCat.ofHom g))

variable [FiniteDimensional K V]

private noncomputable def persistentTestMatrixEndScheme011 : sourceOrderedAdditiveEndFunctor K V ≅
    vectorGroupPointsFunctor K (Module.End K V) :=
  sourceOrderedEndPointsIso K V

end Functor

section NativeScheme

variable (K V R : Type u) [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [CommRing R] [Algebra K R]
  (i j : Type u) [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]
  (b : Module.Basis i K V) (c : Module.Basis j K V)

private noncomputable def persistentTestMatrixEndScheme012 : vectorGroupScheme K (Module.End K V) ≅
    vectorGroupScheme K (Matrix i i K) := endMatrixSchemeIso K V i b

private noncomputable def persistentTestMatrixEndScheme013 : sourceOrderedAdditiveEndFunctor K V ≅ additiveMatrixFunctor K i i :=
  sourceOrderedEndMatrixGroupIso K V i b

private noncomputable def persistentTestMatrixEndScheme014 : sourceOrderedAdditiveEndFunctor K V ≅
    vectorGroupPointsFunctor K (Matrix i i K) :=
  sourceOrderedEndMatrixPointsIso K V i b

private noncomputable def persistentTestMatrixEndScheme015 : vectorGroupScheme K (Matrix i i K) ≅
    vectorGroupScheme K (Matrix j j K) :=
  endMatrixSchemeBasisChangeIso K V i j b c

/- The original examples include `[FiniteDimensional K V]` although these
equalities do not use it; retain that regression context explicitly. -/
omit [FiniteDimensional K V] in
@[nolint unusedArguments]
private theorem persistentTestMatrixEndScheme016 [FiniteDimensional K V] : endMatrixSchemeBasisChangeIso K V i i b b =
    Iso.refl (vectorGroupScheme K (Matrix i i K)) :=
  endMatrixSchemeBasisChangeIso_refl K V i b

omit [FiniteDimensional K V] in
@[nolint unusedArguments]
private theorem persistentTestMatrixEndScheme017 [FiniteDimensional K V] (l : Type u) [Fintype l] [DecidableEq l] (d : Module.Basis l K V) :
    endMatrixSchemeBasisChangeIso K V i j b c ≪≫
      endMatrixSchemeBasisChangeIso K V j l c d =
        endMatrixSchemeBasisChangeIso K V i l b d :=
  endMatrixSchemeBasisChangeIso_comp K V i j b c l d

private theorem persistentTestMatrixEndScheme018 (f : Module.End R (R ⊗[K] V)) :
    (endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom =
      (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f)) :=
  endMatrixSchemeIso_points K V i b R f

private theorem persistentTestMatrixEndScheme019 (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedEndPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom =
      (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R
          (sourceOrderedEndEquiv K V R f))) :=
  sourceOrderedEndMatrixScheme_points K V i b R f

theorem matrixEndSchemeTest_evaluationEntry (f : Module.End R (R ⊗[K] V))
    (row col : i) :
    ((endCoordinateEval K V R f).comp
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap))
        (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
      endMatrixLinearEquiv K V i b R f row col :=
  endMatrixSchemeIso_evaluation_entry K V i b R f row col

theorem matrixEndSchemeTest_polynomial (f : Module.End R (R ⊗[K] V))
    (row col : i) :
    ((endCoordinateEval K V R f).comp
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap)).comp
        (matrixCoordinateRingEquiv K i i).symm.toAlgHom
        (MvPolynomial.X (row, col) + 1) =
      endMatrixLinearEquiv K V i b R f row col + 1 := by
  have h := congrArg (fun p : MvPolynomial (i × i) K →ₐ[K] R ↦
    p (MvPolynomial.X (row, col) + 1)) (endMatrixSchemeIso_polynomial K V i b R f)
  simpa only [AlgHom.comp_apply, map_add, map_one, MvPolynomial.aeval_X] using h

theorem matrixEndSchemeTest_basisPoints (f : Module.End R (R ⊗[K] V)) :
    (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f)) ≫
        (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom =
      (matrixGroupPointsIso K j j).hom.app (CommAlgCat.of K R)
        ((endMatrixBasisChangeIso K V i b j c).hom.app (CommAlgCat.of K R)
          (.ofAdd (endMatrixLinearEquiv K V i b R f))) :=
  endMatrixSchemeBasisChangeIso_points K V i j b c R f

set_option maxRecDepth 1024 in
private theorem persistentTestMatrixEndScheme020 (f : Module.End R (R ⊗[K] V)) (row col : j) :
    matrixCoordinateEval K j j R
      ((endMatrixBasisChangeIso K V i b j c).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f))).toAdd
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K j j).dualBasis (row, col))) =
        endMatrixLinearEquiv K V j c R f row col :=
  endMatrixBasisChangeCoordinate_ι K V i b j c (CommAlgCat.of K R) f row col

private theorem persistentTestMatrixEndScheme021 (f : Module.End R (R ⊗[K] V)) :
    (matrixCoordinateEval K i i R (endMatrixLinearEquiv K V i b R f)).comp
        (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
          (endMatrixSchemeBasisLinearMap K V i j b c)) =
      matrixCoordinateEval K j j R (endMatrixLinearEquiv K V j c R f) :=
  endMatrixSchemeBasisChangeIso_evaluation K V i j b c R f

omit [FiniteDimensional K V] in
@[nolint unusedArguments]
private theorem persistentTestMatrixEndScheme022 [FiniteDimensional K V] : (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom.left =
    Spec.map (CommRingCat.ofHom
      (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
        (endMatrixSchemeBasisLinearMap K V i j b c)).toRingHom) :=
  endMatrixSchemeBasisChangeIso_spec K V i j b c

end NativeScheme

section FiniteFieldBoundaries

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
/-- The zero coefficient algebra of the finite field of two elements. -/
local instance zeroRingAlgebra : Algebra (ZMod 2) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 2 by decide) (ZMod 1)).toAlgebra

private noncomputable def persistentTestMatrixEndScheme023 : vectorGroupScheme (ZMod 2) (Module.End (ZMod 2) (Fin 0 → ZMod 2)) ≅
    vectorGroupScheme (ZMod 2) (Matrix (Fin 0) (Fin 0) (ZMod 2)) :=
  endMatrixSchemeIso (ZMod 2) (Fin 0 → ZMod 2) (Fin 0)
    (Pi.basisFun (ZMod 2) (Fin 0))

theorem matrixEndSchemeTest_zeroAlgebra (f : Module.End (ZMod 1)
    (SourceOrderedTensor (ZMod 2) (Fin 0 → ZMod 2) (ZMod 1))) :
    (sourceOrderedEndPointsIso (ZMod 2) (Fin 0 → ZMod 2)).hom.app
        (CommAlgCat.of (ZMod 2) (ZMod 1)) (.ofAdd f) ≫
        (endMatrixSchemeIso (ZMod 2) (Fin 0 → ZMod 2) (Fin 0)
          (Pi.basisFun (ZMod 2) (Fin 0))).hom.hom.hom =
      (matrixGroupPointsIso (ZMod 2) (Fin 0) (Fin 0)).hom.app
        (CommAlgCat.of (ZMod 2) (ZMod 1))
          (.ofAdd (endMatrixLinearEquiv (ZMod 2) (Fin 0 → ZMod 2) (Fin 0)
            (Pi.basisFun (ZMod 2) (Fin 0)) (ZMod 1)
              (sourceOrderedEndEquiv (ZMod 2) (Fin 0 → ZMod 2) (ZMod 1) f))) :=
  sourceOrderedEndMatrixScheme_points (ZMod 2) (Fin 0 → ZMod 2)
    (Fin 0) (Pi.basisFun (ZMod 2) (Fin 0)) (ZMod 1) f

private theorem persistentTestMatrixEndScheme024 (f : Module.End (ZMod 1)
    ((ZMod 1) ⊗[ZMod 2] (Fin 1 → ZMod 2))) :
    (endGroupPointsIso (ZMod 2) (Fin 1 → ZMod 2)).hom.app
        (CommAlgCat.of (ZMod 2) (ZMod 1)) (.ofAdd f) ≫
        (endMatrixSchemeIso (ZMod 2) (Fin 1 → ZMod 2) (Fin 1)
          (Pi.basisFun (ZMod 2) (Fin 1))).hom.hom.hom =
      (matrixGroupPointsIso (ZMod 2) (Fin 1) (Fin 1)).hom.app
        (CommAlgCat.of (ZMod 2) (ZMod 1))
          (.ofAdd (endMatrixLinearEquiv (ZMod 2) (Fin 1 → ZMod 2) (Fin 1)
            (Pi.basisFun (ZMod 2) (Fin 1)) (ZMod 1) f)) :=
  endMatrixSchemeIso_points (ZMod 2) (Fin 1 → ZMod 2)
    (Fin 1) (Pi.basisFun (ZMod 2) (Fin 1)) (ZMod 1) f

theorem matrixEndSchemeTest_finiteFieldPolynomial
    (f : Module.End (ZMod 2) ((ZMod 2) ⊗[ZMod 2] (Fin 1 → ZMod 2))) :
    ((endCoordinateEval (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2) f).comp
      (vectorGroupCoordinateMap (ZMod 2)
        (Module.End (ZMod 2) (Fin 1 → ZMod 2))
        (Matrix (Fin 1) (Fin 1) (ZMod 2))
        (endMatrixBaseLinearEquiv (ZMod 2) (Fin 1 → ZMod 2) (Fin 1)
          (Pi.basisFun (ZMod 2) (Fin 1))).toLinearMap)).comp
        (matrixCoordinateRingEquiv (ZMod 2) (Fin 1) (Fin 1)).symm.toAlgHom =
      MvPolynomial.aeval (fun p : Fin 1 × Fin 1 ↦
        endMatrixLinearEquiv (ZMod 2) (Fin 1 → ZMod 2) (Fin 1)
          (Pi.basisFun (ZMod 2) (Fin 1)) (ZMod 2) f p.1 p.2) :=
  endMatrixSchemeIso_polynomial (ZMod 2) (Fin 1 → ZMod 2)
    (Fin 1) (Pi.basisFun (ZMod 2) (Fin 1)) (ZMod 2) f

private theorem persistentTestMatrixEndScheme025 (f : Module.End (Polynomial (ZMod 2))
    (SourceOrderedTensor (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2))))
    (v : Fin 1 → ZMod 2) :
    sourceOrderedCanonicalLinearEquiv (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2)
      (sourceOrderedEndBaseChange (ZMod 2) (Fin 1 → ZMod 2)
        (Polynomial (ZMod 2)) (ZMod 2) (Polynomial.aeval (1 : ZMod 2)) f
        (sourceOrderedTmul (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2) v 1)) =
      ((Polynomial.aeval (1 : ZMod 2)).toLinearMap.rTensor (Fin 1 → ZMod 2))
        (sourceOrderedCanonicalLinearEquiv (ZMod 2) (Fin 1 → ZMod 2)
          (Polynomial (ZMod 2))
          (f (sourceOrderedTmul (ZMod 2) (Fin 1 → ZMod 2)
            (Polynomial (ZMod 2)) v 1))) := by
  simpa using sourceOrderedEndBaseChange_tmul (ZMod 2) (Fin 1 → ZMod 2)
    (Polynomial (ZMod 2)) (ZMod 2) (Polynomial.aeval (1 : ZMod 2)) f v 1

private theorem persistentTestMatrixEndScheme026 (f : Module.End (Polynomial (ZMod 2))
    (SourceOrderedTensor (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2)))) :
    sourceOrderedEndBaseChange (ZMod 2) (Fin 1 → ZMod 2)
      (Polynomial (ZMod 2)) (ZMod 1)
        ((Algebra.ofId (ZMod 2) (ZMod 1)).comp (Polynomial.aeval (1 : ZMod 2))) f =
      sourceOrderedEndBaseChange (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2) (ZMod 1)
        (Algebra.ofId (ZMod 2) (ZMod 1))
        (sourceOrderedEndBaseChange (ZMod 2) (Fin 1 → ZMod 2)
          (Polynomial (ZMod 2)) (ZMod 2) (Polynomial.aeval (1 : ZMod 2)) f) :=
  (sourceOrderedEndBaseChange_comp (ZMod 2) (Fin 1 → ZMod 2)
    (Polynomial (ZMod 2)) (ZMod 2) (ZMod 1) (Polynomial.aeval (1 : ZMod 2))
      (Algebra.ofId (ZMod 2) (ZMod 1)) f).symm

end FiniteFieldBoundaries

end AlgebraicGeometry

#lint

#print axioms AlgebraicGeometry.sourceOrderedEndBaseChange
#print axioms AlgebraicGeometry.sourceOrderedEndBaseChangeAddHom
#print axioms AlgebraicGeometry.sourceOrderedEndBaseChangeAddHom_apply
#print axioms AlgebraicGeometry.sourceOrderedEndBaseChange_id
#print axioms AlgebraicGeometry.sourceOrderedEndBaseChange_comp
#print axioms AlgebraicGeometry.sourceOrderedEndBaseChange_tmul
#print axioms AlgebraicGeometry.sourceOrderedAdditiveEndFunctor
#print axioms AlgebraicGeometry.sourceOrderedEndGroupIso
#print axioms AlgebraicGeometry.sourceOrderedEndPointsIso
#print axioms AlgebraicGeometry.endMatrixBaseLinearEquiv
#print axioms AlgebraicGeometry.endMatrixBaseLinearEquiv_apply
#print axioms AlgebraicGeometry.endMatrixSchemeIso
#print axioms AlgebraicGeometry.endMatrixSchemeIso_hom
#print axioms AlgebraicGeometry.endMatrixSchemeIso_spec
#print axioms AlgebraicGeometry.endMatrixSchemeIso_coordinate
#print axioms AlgebraicGeometry.endMatrixSchemeIso_entry_dual
#print axioms AlgebraicGeometry.endMatrixSchemeIso_tensor
#print axioms AlgebraicGeometry.endMatrixSchemeIso_evaluation
#print axioms AlgebraicGeometry.endMatrixSchemeIso_evaluation_entry
#print axioms AlgebraicGeometry.endMatrixSchemeIso_polynomial
#print axioms AlgebraicGeometry.endMatrixSchemeIso_points
#print axioms AlgebraicGeometry.sourceOrderedEndMatrixScheme_points
#print axioms AlgebraicGeometry.sourceOrderedEndMatrixGroupIso
#print axioms AlgebraicGeometry.sourceOrderedEndMatrixPointsIso
#print axioms AlgebraicGeometry.sourceOrderedEndMatrixGroupIso_apply
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso
#print axioms AlgebraicGeometry.endMatrixSchemeBasisLinearMap
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_hom
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_spec
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_coordinate
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_coordinate_comp
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_evaluation
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_refl
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_comp
#print axioms AlgebraicGeometry.endMatrixSchemeBasisChangeIso_points
#print axioms AlgebraicGeometry.matrixEndSchemeTest_add
#print axioms AlgebraicGeometry.matrixEndSchemeTest_evaluationEntry
#print axioms AlgebraicGeometry.matrixEndSchemeTest_polynomial
#print axioms AlgebraicGeometry.matrixEndSchemeTest_basisPoints
#print axioms AlgebraicGeometry.matrixEndSchemeTest_zeroAlgebra
#print axioms AlgebraicGeometry.matrixEndSchemeTest_finiteFieldPolynomial
