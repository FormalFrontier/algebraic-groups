/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.MatrixEndAdditive
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Private matrix and endomorphism group regression clients

The original fifty examples are stored as private declarations without
enlarging the ordinary public API. The three pre-existing named theorems
and the actual local instance declarations retain their public names.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u

section ArbitraryVectorSpace

variable (K V R S T : Type u) [Field K] [AddCommGroup V] [Module K V]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing T] [Algebra K T]

private def testEndFunctor : CommAlgCat K ⥤ GrpCat := additiveEndFunctor K V

private def testOrderedTensor : SourceOrderedTensor K V R ≃ₗ[R] R ⊗[K] V :=
  sourceOrderedCanonicalLinearEquiv K V R

private def testOrderedEnd : Module.End R (SourceOrderedTensor K V R) ≃ₗ[R]
    Module.End R (R ⊗[K] V) := sourceOrderedEndEquiv K V R

private theorem testOrderedScalar (v : V) (r s : R) :
    r • sourceOrderedTmul K V R v s = sourceOrderedTmul K V R v (r * s) := by
  simp

private theorem testEndBaseChangePure (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) (s : S) (v : V) :
    endBaseChange K V R S g f (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] v)) := by simp

private theorem testEndFunctorMap (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) :
    (additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd f) =
      .ofAdd (endBaseChange K V R S g f) := rfl

private theorem testEndFunctorAdd (g : R →ₐ[K] S) (f h : Module.End R (R ⊗[K] V)) :
    (additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd (f + h)) =
      (additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd f) *
        (additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd h) :=
  ((additiveEndFunctor K V).map (CommAlgCat.ofHom g)).hom.map_mul (.ofAdd f) (.ofAdd h)

private theorem testEndFunctorZero (g : R →ₐ[K] S) :
    (additiveEndFunctor K V).map (CommAlgCat.ofHom g)
      (.ofAdd (0 : Module.End R (R ⊗[K] V))) = 1 :=
  ((additiveEndFunctor K V).map (CommAlgCat.ofHom g)).hom.map_one

private theorem testEndFunctorNeg (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) :
    (additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd (-f)) =
      ((additiveEndFunctor K V).map (CommAlgCat.ofHom g) (.ofAdd f))⁻¹ :=
  ((additiveEndFunctor K V).map (CommAlgCat.ofHom g)).hom.map_inv (.ofAdd f)

private theorem testEndFunctorComp (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : Module.End R (R ⊗[K] V)) :
    endBaseChange K V S T h (endBaseChange K V R S g f) =
      endBaseChange K V R T (h.comp g) f :=
  endBaseChange_comp K V R S T g h f

private theorem testEndFunctorId (f : Module.End R (R ⊗[K] V)) :
    endBaseChange K V R R (AlgHom.id K R) f = f := by simp

end ArbitraryVectorSpace

section FiniteVectorSpace

variable (K V R S : Type u) [Field K] [AddCommGroup V] [Module K V]
  [finiteDimensional : FiniteDimensional K V] [CommRing R] [Algebra K R]
  [CommRing S] [Algebra K S]

private def testEndVectorIso : vectorGroupFunctor K (Module.End K V) ≅ additiveEndFunctor K V :=
  endVectorGroupIso K V

private def testEndPointsIso : additiveEndFunctor K V ≅ vectorGroupPointsFunctor K (Module.End K V) :=
  endGroupPointsIso K V

private theorem testEndFiniteType : Algebra.FiniteType K (vectorGroupCoordinateRing K (Module.End K V)) :=
  inferInstance

private theorem testEndLocallyFiniteType : LocallyOfFiniteType
    (vectorGroupUnderlyingScheme K (Module.End K V)).hom := inferInstance

omit finiteDimensional in
/-- The original regression includes finite dimension even though quasi-compactness does not need it. -/
@[nolint unusedArguments]
private theorem testEndQuasiCompact [_finiteDimensional : FiniteDimensional K V] : QuasiCompact
    (vectorGroupUnderlyingScheme K (Module.End K V)).hom := inferInstance

private theorem testEndNaturality (g : R →ₐ[K] S) (x : Module.End K V ⊗[K] R) :
    endVectorLinearEquiv K V S
      (TensorProduct.map (LinearMap.id : Module.End K V →ₗ[K] Module.End K V)
        g.toLinearMap x) =
      endBaseChange K V R S g (endVectorLinearEquiv K V R x) :=
  endVectorLinearEquiv_naturality K V R S g x

private theorem testEndPure (r s : R) (f : Module.End K V) (v : V) :
    endVectorLinearEquiv K V R (f ⊗ₜ[K] r) (s ⊗ₜ[K] v) =
      (r * s) ⊗ₜ[K] f v := by simp

end FiniteVectorSpace

section Matrix

variable (K m n R S : Type u) [Field K] [finiteM : Fintype m] [finiteN : Fintype n]
  [decidableM : DecidableEq m] [decidableN : DecidableEq n] [CommRing R] [Algebra K R]
  [CommRing S] [Algebra K S]

private def testMatrixVectorIso : vectorGroupFunctor K (Matrix m n K) ≅ additiveMatrixFunctor K m n :=
  matrixVectorGroupIso K m n

private def testMatrixPointsIso : additiveMatrixFunctor K m n ≅
    vectorGroupPointsFunctor K (Matrix m n K) := matrixGroupPointsIso K m n

omit decidableM decidableN in
/-- Preserve the original matrix test's decidable-equality hypotheses. -/
@[nolint unusedArguments]
private theorem testMatrixFiniteType [_decidableM : DecidableEq m] [_decidableN : DecidableEq n] : Algebra.FiniteType K (vectorGroupCoordinateRing K (Matrix m n K)) :=
  inferInstance

omit decidableM decidableN in
/-- Preserve the original matrix test's decidable-equality hypotheses. -/
@[nolint unusedArguments]
private theorem testMatrixLocallyFiniteType
    [_decidableM : DecidableEq m] [_decidableN : DecidableEq n] : LocallyOfFiniteType
    (vectorGroupUnderlyingScheme K (Matrix m n K)).hom := inferInstance

omit finiteM finiteN decidableM decidableN in
/-- Preserve the original finite-matrix testing context without strengthening the library theorem. -/
@[nolint unusedArguments]
private theorem testMatrixQuasiCompact [_finiteM : Fintype m] [_finiteN : Fintype n]
    [_decidableM : DecidableEq m] [_decidableN : DecidableEq n] : QuasiCompact
    (vectorGroupUnderlyingScheme K (Matrix m n K)).hom := inferInstance

private theorem testMatrixPointsAdd (A B : Matrix m n R) :
    (matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R) (.ofAdd (A + B)) =
      (matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R) (.ofAdd A) *
        (matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R) (.ofAdd B) :=
  ((matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R)).hom.map_mul
    (.ofAdd A) (.ofAdd B)

private theorem testMatrixPointsZero : (matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R)
    (.ofAdd (0 : Matrix m n R)) = 1 :=
  ((matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R)).hom.map_one

private theorem testMatrixPointsInv (A : Matrix m n R) :
    (matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R) (.ofAdd (-A)) =
      ((matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R) (.ofAdd A))⁻¹ :=
  ((matrixGroupPointsIso K m n).hom.app (CommAlgCat.of K R)).hom.map_inv (.ofAdd A)

omit finiteM finiteN decidableM decidableN in
/-- This regression intentionally retains the original finite-matrix context for the group law. -/
@[nolint unusedArguments]
private theorem testMatrixPointsAddInverse [_finiteM : Fintype m] [_finiteN : Fintype n]
    [_decidableM : DecidableEq m] [_decidableN : DecidableEq n] (A : Matrix m n R) :
    (.ofAdd A : Multiplicative (Matrix m n R)) * .ofAdd (-A) = 1 := by simp

omit finiteM finiteN decidableM decidableN in
/-- This regression intentionally retains the original finite-matrix context for coefficient maps. -/
@[nolint unusedArguments]
private theorem testMatrixFunctorMap [_finiteM : Fintype m] [_finiteN : Fintype n]
    [_decidableM : DecidableEq m] [_decidableN : DecidableEq n]
    (g : R →ₐ[K] S) (A : Matrix m n R) :
    (additiveMatrixFunctor K m n).map (CommAlgCat.ofHom g) (.ofAdd A) =
      .ofAdd (g.toAddMonoidHom.mapMatrix A) := rfl

private theorem testMatrixTensorAdd (A B : Matrix m n K) (r s : R) (row : m) (col : n) :
    matrixVectorLinearEquiv K m n R (A ⊗ₜ[K] r + B ⊗ₜ[K] s) row col =
      algebraMap K R (A row col) * r + algebraMap K R (B row col) * s := by
  simp [matrixVectorLinearEquiv, matrixScalarEquiv_tmul, mul_comm]

private theorem testMatrixCoordinate (A : Matrix m n R) (row : m) (col : n) :
    matrixCoordinateEval K m n R A
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (row, col))) =
      A row col := matrixCoordinateEval_ι K m n R A row col

private theorem testMatrixCoordinateNaturality (g : R →ₐ[K] S) (A : Matrix m n R) (row : m) (col : n) :
    matrixCoordinateEval K m n S (g.toAddMonoidHom.mapMatrix A)
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (row, col))) =
      g (matrixCoordinateEval K m n R A
        (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (row, col)))) := by
  rw [matrixCoordinateEval_ι, matrixCoordinateEval_ι]
  rfl

private theorem testMatrixPolynomialEvaluation (A : Matrix m n R) :
    (matrixCoordinateEval K m n R A).comp (matrixCoordinateRingEquiv K m n).symm.toAlgHom =
      MvPolynomial.aeval (fun p : m × n ↦ A p.1 p.2) :=
  matrixCoordinateEval_polynomial K m n R A

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The rectangular polynomial-coordinate regression client. -/
theorem matrixEndTest_rectangularEval (A : Matrix m n R) :
    (Matrix.mvPolynomialX m n K).map
      (MvPolynomial.aeval (fun p : m × n ↦ A p.1 p.2)) = A :=
  matrixPolynomialX_evaluation K m n R A

end Matrix

section ChosenBasis

variable (K V R S : Type u) [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [CommRing R] [Algebra K R]
  [CommRing S] [Algebra K S]
variable (i j : Type u) [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
  (b : Module.Basis i K V) (c : Module.Basis j K V)

private def testBasisEndMatrixIso : additiveEndFunctor K V ≅ additiveMatrixFunctor K i i :=
  endMatrixGroupIso K V i b

private def testBasisChangeIso : additiveMatrixFunctor K i i ≅ additiveMatrixFunctor K j j :=
  endMatrixBasisChangeIso K V i b j c

theorem matrixEndTest_basisChange (A : CommAlgCat K)
    (f : Module.End A (A ⊗[K] V)) :
    (endMatrixBasisChangeIso K V i b j c).hom.app A
      (.ofAdd (endMatrixLinearEquiv K V i b A f)) =
        .ofAdd (endMatrixLinearEquiv K V j c A f) :=
  endMatrixBasisChangeIso_apply K V i b j c A f

private theorem testBasisNaturality (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) :
    endMatrixLinearEquiv K V i b S (endBaseChange K V R S g f) =
      g.toAddMonoidHom.mapMatrix (endMatrixLinearEquiv K V i b R f) :=
  endMatrixLinearEquiv_naturality K V i b R S g f

private theorem testBasisCoordinatePure (r : R) (f : Module.End K V) (row col : i) :
    endMatrixCoordinateEval K V i b R (endVectorLinearEquiv K V R (f ⊗ₜ[K] r))
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
        r * algebraMap K R (b.repr (f (b col)) row) :=
  endMatrixCoordinateEval_tmul K V i b R r f row col

private theorem testBasisCoordinateNaturality (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) (row col : i) :
    endMatrixCoordinateEval K V i b S (endBaseChange K V R S g f)
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
      g (endMatrixCoordinateEval K V i b R f
        (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col)))) := by
  rw [endMatrixCoordinateEval_ι, endMatrixCoordinateEval_ι,
    endMatrixLinearEquiv_naturality]
  rfl

end ChosenBasis

section Boundaries

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
/-- A concrete coefficient algebra with a zero target. -/
local instance zeroRingAlgebra : Algebra (ZMod 2) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 2 by decide) (ZMod 1)).toAlgebra

private def testEmptyRows : vectorGroupFunctor (ZMod 2) (Matrix (Fin 0) (Fin 3) (ZMod 2)) ≅
    additiveMatrixFunctor (ZMod 2) (Fin 0) (Fin 3) :=
  matrixVectorGroupIso (ZMod 2) (Fin 0) (Fin 3)

private def testEmptyColumns : vectorGroupFunctor (ZMod 2) (Matrix (Fin 3) (Fin 0) (ZMod 2)) ≅
    additiveMatrixFunctor (ZMod 2) (Fin 3) (Fin 0) :=
  matrixVectorGroupIso (ZMod 2) (Fin 3) (Fin 0)

private def testEmptyMatrix : vectorGroupFunctor (ZMod 2) (Matrix (Fin 0) (Fin 0) (ZMod 2)) ≅
    additiveMatrixFunctor (ZMod 2) (Fin 0) (Fin 0) :=
  matrixVectorGroupIso (ZMod 2) (Fin 0) (Fin 0)

private def testRectangularZero : additiveMatrixFunctor (ZMod 2) (Fin 1) (Fin 2) ≅
    vectorGroupPointsFunctor (ZMod 2) (Matrix (Fin 1) (Fin 2) (ZMod 2)) :=
  matrixGroupPointsIso (ZMod 2) (Fin 1) (Fin 2)

private def testEmptyEndPoints : additiveEndFunctor (ZMod 2) (Fin 0 → ZMod 2) ≅
    vectorGroupPointsFunctor (ZMod 2) (Module.End (ZMod 2) (Fin 0 → ZMod 2)) :=
  endGroupPointsIso (ZMod 2) (Fin 0 → ZMod 2)

private theorem testZeroEndSubsingleton : Subsingleton (Multiplicative
    (Module.End (ZMod 1) ((ZMod 1) ⊗[ZMod 2] (Fin 1 → ZMod 2)))) :=
  inferInstance

private def testEmptyEndMatrix : additiveEndFunctor (ZMod 2) (Fin 0 → ZMod 2) ≅
    additiveMatrixFunctor (ZMod 2) (Fin 0) (Fin 0) :=
  endMatrixGroupIso (ZMod 2) (Fin 0 → ZMod 2) (Fin 0)
    (Pi.basisFun (ZMod 2) (Fin 0))

private def testEndFiniteDimensional : vectorGroupFunctor (ZMod 2) (Module.End (ZMod 2) (Fin 1 → ZMod 2)) ≅
    additiveEndFunctor (ZMod 2) (Fin 1 → ZMod 2) :=
  endVectorGroupIso (ZMod 2) (Fin 1 → ZMod 2)

private def testRectangularPoints : additiveMatrixFunctor (ZMod 2) (Fin 1) (Fin 2) ≅
    vectorGroupPointsFunctor (ZMod 2) (Matrix (Fin 1) (Fin 2) (ZMod 2)) :=
  matrixGroupPointsIso (ZMod 2) (Fin 1) (Fin 2)

private def testZeroRowsPoints : additiveMatrixFunctor (ZMod 2) (Fin 0) (Fin 1) ≅
    vectorGroupPointsFunctor (ZMod 2) (Matrix (Fin 0) (Fin 1) (ZMod 2)) :=
  matrixGroupPointsIso (ZMod 2) (Fin 0) (Fin 1)

private def testSquarePoints : additiveMatrixFunctor (ZMod 2) (Fin 1) (Fin 1) ≅
    vectorGroupPointsFunctor (ZMod 2) (Matrix (Fin 1) (Fin 1) (ZMod 2)) :=
  matrixGroupPointsIso (ZMod 2) (Fin 1) (Fin 1)

private theorem testZeroRingCoordinate (A : Matrix (Fin 1) (Fin 2) (ZMod 1)) :
    matrixCoordinateEval (ZMod 2) (Fin 1) (Fin 2) (ZMod 1) A
      (SymmetricAlgebra.ι (ZMod 2) _
        ((Matrix.stdBasis (ZMod 2) (Fin 1) (Fin 2)).dualBasis (0, 1))) = A 0 1 := by
  exact matrixCoordinateEval_ι (ZMod 2) (Fin 1) (Fin 2) (ZMod 1) A 0 1

theorem matrixEndTest_nonflatComp (f : Module.End (Polynomial (ZMod 2))
    (Polynomial (ZMod 2) ⊗[ZMod 2] (Fin 1 → ZMod 2))) (v : Fin 1 → ZMod 2) :
    endBaseChange (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2)) (ZMod 2)
      (Polynomial.aeval (0 : ZMod 2)) f (1 ⊗ₜ[ZMod 2] v) =
      ((Polynomial.aeval (0 : ZMod 2)).toLinearMap.rTensor (Fin 1 → ZMod 2))
        (f (1 ⊗ₜ[ZMod 2] v)) := by simp

private theorem testNonflatZeroComp (f : Module.End (Polynomial (ZMod 2))
    (Polynomial (ZMod 2) ⊗[ZMod 2] (Fin 1 → ZMod 2))) :
    endBaseChange (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2)) (ZMod 1)
      ((Algebra.ofId (ZMod 2) (ZMod 1)).comp (Polynomial.aeval (0 : ZMod 2))) f =
    endBaseChange (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2) (ZMod 1)
      (Algebra.ofId (ZMod 2) (ZMod 1))
      (endBaseChange (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2)) (ZMod 2)
        (Polynomial.aeval (0 : ZMod 2)) f) :=
  (endBaseChange_comp (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2))
    (ZMod 2) (ZMod 1) (Polynomial.aeval (0 : ZMod 2))
    (Algebra.ofId (ZMod 2) (ZMod 1)) f).symm

end Boundaries

end AlgebraicGeometry

#lint
