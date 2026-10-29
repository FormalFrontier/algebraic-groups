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

private theorem testEndBaseChangePure (g : R →ₐ[K] S)
    (f : Module.End R (R ⊗[K] V)) (s : S) (v : V) :
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

private def testEndVectorIso :
    vectorGroupFunctor K (Module.End K V) ≅ additiveEndFunctor K V :=
  endVectorGroupIso K V

private def testEndPointsIso :
    additiveEndFunctor K V ≅ vectorGroupPointsFunctor K (Module.End K V) :=
  endGroupPointsIso K V

private theorem testEndFiniteType :
    Algebra.FiniteType K (vectorGroupCoordinateRing K (Module.End K V)) := inferInstance

private theorem testEndLocallyFiniteType : LocallyOfFiniteType
    (vectorGroupUnderlyingScheme K (Module.End K V)).hom := inferInstance

omit finiteDimensional in
private theorem testEndQuasiCompact : QuasiCompact
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

private def testMatrixVectorIso :
    vectorGroupFunctor K (Matrix m n K) ≅ additiveMatrixFunctor K m n :=
  matrixVectorGroupIso K m n

private def testMatrixPointsIso : additiveMatrixFunctor K m n ≅
    vectorGroupPointsFunctor K (Matrix m n K) := matrixGroupPointsIso K m n

omit finiteM finiteN decidableM decidableN in
/-- Finite row and column indices suffice for finite-type matrix coordinates. -/
private theorem testMatrixFiniteType [Finite m] [Finite n] :
    Algebra.FiniteType K (vectorGroupCoordinateRing K (Matrix m n K)) :=
  inferInstance

omit finiteM finiteN decidableM decidableN in
/-- Finite row and column indices suffice for a locally finite-type matrix scheme. -/
private theorem testMatrixLocallyFiniteType [Finite m] [Finite n] :
    LocallyOfFiniteType (vectorGroupUnderlyingScheme K (Matrix m n K)).hom := inferInstance

omit finiteM finiteN decidableM decidableN in
/-- Affine matrix schemes are quasi-compact for arbitrary row and column indices. -/
private theorem testMatrixQuasiCompact :
    QuasiCompact (vectorGroupUnderlyingScheme K (Matrix m n K)).hom := inferInstance

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
/-- A matrix and its negative cancel for arbitrary row and column indices. -/
private theorem testMatrixPointsAddInverse (A : Matrix m n R) :
    (.ofAdd A : Multiplicative (Matrix m n R)) * .ofAdd (-A) = 1 := by simp

omit finiteM finiteN decidableM decidableN in
/-- Coefficient maps act entrywise for arbitrary row and column indices. -/
private theorem testMatrixFunctorMap (g : R →ₐ[K] S) (A : Matrix m n R) :
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

private theorem testMatrixCoordinateNaturality (g : R →ₐ[K] S)
    (A : Matrix m n R) (row : m) (col : n) :
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

private theorem testBasisCoordinateNaturality (g : R →ₐ[K] S)
    (f : Module.End R (R ⊗[K] V)) (row col : i) :
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

private def testEndFiniteDimensional :
    vectorGroupFunctor (ZMod 2) (Module.End (ZMod 2) (Fin 1 → ZMod 2)) ≅
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

/-!
## Matrix-coordinate values over semirings

The matrix-unit basis of the full matrix space uses finite row and column
indices. Scalar multiplication and representation already work over semirings;
the dual basis uses commutative semirings. Empty indices and the zero ring are
included, alongside nonzero rectangular matrices over the natural numbers.
-/

namespace AlgebraicGeometry.MatrixCoordinateValues

universe r s t

/-- The standard matrix basis with finite row and column types. -/
def basis (R : Type r) [Semiring R] (m : Type s) (n : Type t)
    [Finite m] [Finite n] : Module.Basis (m × n) R (Matrix m n R) := by
  classical
  letI := Fintype.ofFinite m
  exact Matrix.stdBasis R m n

/-- The dual of the standard matrix basis over a commutative semiring. -/
def dualBasis (R : Type r) [CommSemiring R] (m : Type s) (n : Type t)
    [Finite m] [Finite n] :
    Module.Basis (m × n) R (Module.Dual R (Matrix m n R)) := by
  classical
  exact (basis R m n).dualBasis

/-- A scalar multiple of a matrix basis vector has the supplied coefficient. -/
theorem basis_smul_repr (R : Type r) [Semiring R] (m : Type s) (n : Type t)
    [Finite m] [Finite n] (p : m × n) (c : R) :
    (basis R m n).repr (c • basis R m n p) p = c := by
  classical
  simp [-matrixStdBasis_repr]

/-- The matching dual matrix coordinate evaluates a scalar multiple of a basis vector. -/
theorem dualBasis_smul (R : Type r) [CommSemiring R] (m : Type s) (n : Type t)
    [Finite m] [Finite n] (p : m × n) (c : R) :
    dualBasis R m n p (c • basis R m n p) = c := by
  classical
  simp [-matrixStdBasis_repr, dualBasis]

/-- A two-by-three matrix over the natural numbers with distinct positive entries. -/
def naturalRectangle : Matrix (Fin 2) (Fin 3) ℕ :=
  fun row col ↦ 3 * row.val + col.val + 1

/-- The bottom-right entry of the natural-number rectangle is nonzero. -/
theorem naturalRectangle_entry : naturalRectangle 1 2 = 6 ∧ naturalRectangle 1 2 ≠ 0 := by
  simp [naturalRectangle]

/-- A matrix basis vector has value one at its index and zero at a different index. -/
theorem naturalBasis_values :
    basis ℕ (Fin 2) (Fin 3) (1, 2) 1 2 = 1 ∧
      basis ℕ (Fin 2) (Fin 3) (1, 2) 0 0 = 0 := by
  classical
  simp [basis, Matrix.stdBasis_eq_single]

/-- The bottom-right dual coordinate of the natural-number rectangle is six. -/
theorem naturalRectangle_dual :
    dualBasis ℕ (Fin 2) (Fin 3) (1, 2) naturalRectangle = 6 := by
  classical
  simp [-matrixStdBasis_repr, dualBasis, basis,
    Matrix.stdBasis, naturalRectangle]

/-- The bottom-right basis coefficient of the natural-number rectangle is six. -/
theorem naturalRectangle_repr :
    (basis ℕ (Fin 2) (Fin 3)).repr naturalRectangle (1, 2) = 6 := by
  classical
  simp [-matrixStdBasis_repr, basis, Matrix.stdBasis, naturalRectangle]

/-- A rectangular dual coordinate reads the sum of entries of arbitrary natural matrices. -/
theorem naturalRectangle_add_dual (A B : Matrix (Fin 2) (Fin 3) ℕ) :
    dualBasis ℕ (Fin 2) (Fin 3) (1, 2) (A + B) = A 1 2 + B 1 2 := by
  classical
  simp [-matrixStdBasis_repr, dualBasis, basis, Matrix.stdBasis]

/-- Every empty-row matrix has zero finitely-supported coefficients. -/
theorem emptyRows_repr (A : Matrix (Fin 0) (Fin 3) ℕ) :
    (basis ℕ (Fin 0) (Fin 3)).repr A = 0 := by
  ext p
  exact Fin.elim0 p.1

/-- Every empty-column matrix has zero finitely-supported coefficients. -/
theorem emptyColumns_repr (A : Matrix (Fin 2) (Fin 0) ℕ) :
    (basis ℕ (Fin 2) (Fin 0)).repr A = 0 := by
  ext p
  exact Fin.elim0 p.2

/-- The empty-row basis reconstructs the zero matrix from zero coefficients. -/
theorem emptyRows_reconstruction :
    (basis ℕ (Fin 0) (Fin 3)).repr.symm 0 = 0 :=
  map_zero _

/-- Every functional on empty-row matrices has zero dual-basis coefficients. -/
theorem emptyRows_dual_repr (φ : Module.Dual ℕ (Matrix (Fin 0) (Fin 3) ℕ)) :
    (dualBasis ℕ (Fin 0) (Fin 3)).repr φ = 0 := by
  ext p
  exact Fin.elim0 p.1

/-- A rectangular basis vector over the zero ring is the zero matrix. -/
theorem zeroRing_basis : basis (ZMod 1) (Fin 2) (Fin 3) (1, 2) = 0 :=
  Subsingleton.elim _ _

/-- The dual coordinate of the constant-one zero-ring matrix is zero. -/
theorem zeroRing_dual :
    dualBasis (ZMod 1) (Fin 2) (Fin 3) (1, 2) (fun _ _ ↦ 1) = 0 :=
  Subsingleton.elim _ _

/-- The basis coefficient of the constant-one zero-ring matrix is zero. -/
theorem zeroRing_repr :
    (basis (ZMod 1) (Fin 2) (Fin 3)).repr (fun _ _ ↦ 1) (1, 2) = 0 :=
  Subsingleton.elim _ _

/-- A rectangle with independently lifted row, column and scalar universes. -/
def liftedRectangle :
    Matrix (ULift.{r} (Fin 2)) (ULift.{s} (Fin 3)) (ULift.{t} ℕ) :=
  fun row col ↦ ⟨3 * row.down.val + col.down.val + 1⟩

/-- The lifted rectangle's dual coordinate is the lifted natural number six. -/
theorem liftedRectangle_dual :
    dualBasis (ULift.{t} ℕ) (ULift.{r} (Fin 2)) (ULift.{s} (Fin 3))
      (⟨1⟩, ⟨2⟩) liftedRectangle = ⟨6⟩ := by
  classical
  simp [-matrixStdBasis_repr, dualBasis, basis,
    Matrix.stdBasis, liftedRectangle]

/-- The lifted rectangle's basis coefficient is the lifted natural number six. -/
theorem liftedRectangle_repr :
    (basis (ULift.{t} ℕ) (ULift.{r} (Fin 2)) (ULift.{s} (Fin 3))).repr
      liftedRectangle (⟨1⟩, ⟨2⟩) = ⟨6⟩ := by
  classical
  simp [-matrixStdBasis_repr, basis, Matrix.stdBasis, liftedRectangle]

section Field

/-- The dual value and representation coefficient with field matrix coordinates. -/
def fieldEntries (K m n : Type r) [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) (row : m) (col : n) : K × K :=
  ((Matrix.stdBasis K m n).dualBasis (row, col) A,
    (Matrix.stdBasis K m n).repr A (row, col))

/-- The two field-coordinate descriptions give the same matrix-entry value. -/
theorem fieldEntries_apply (K m n : Type r) [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n K) (row : m) (col : n) :
    fieldEntries K m n A row col = (A row col, A row col) := by
  exact Prod.ext (matrixStdBasis_dual_apply K m n A row col)
    (matrixStdBasis_repr K m n A row col)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A nonzero two-by-three binary matrix with a nonzero last column. -/
def binaryRectangle : Matrix (Fin 2) (Fin 3) (ZMod 2) :=
  fun row col ↦ if row = 1 then 1 else if col = 2 then 1 else 0

/-- Dual and representation field coordinates evaluate the binary rectangle to one. -/
theorem binaryRectangle_entries :
    fieldEntries (ZMod 2) (Fin 2) (Fin 3) binaryRectangle 1 2 = (1, 1) := by
  rw [fieldEntries_apply]
  simp [binaryRectangle]

/-- The binary rectangle has a nonzero selected entry and a zero opposite corner. -/
theorem binaryRectangle_values : binaryRectangle 1 2 ≠ 0 ∧ binaryRectangle 0 0 = 0 := by
  simp [binaryRectangle]

/-- Symmetric-coordinate evaluation returns one on the binary rectangle. -/
theorem binaryRectangle_coordinate :
    matrixCoordinateEval (ZMod 2) (Fin 2) (Fin 3) (ZMod 2) binaryRectangle
      (SymmetricAlgebra.ι (ZMod 2) _
        ((Matrix.stdBasis (ZMod 2) (Fin 2) (Fin 3)).dualBasis (1, 2))) = 1 := by
  rw [matrixCoordinateEval_ι]
  simp [binaryRectangle]

attribute [local instance] AlgebraicGeometry.zeroRingAlgebra

/-- Symmetric-coordinate evaluation also takes a zero-ring value. -/
theorem zeroRing_coordinate :
    matrixCoordinateEval (ZMod 2) (Fin 2) (Fin 3) (ZMod 1) (fun _ _ ↦ 1)
      (SymmetricAlgebra.ι (ZMod 2) _
        ((Matrix.stdBasis (ZMod 2) (Fin 2) (Fin 3)).dualBasis (1, 2))) = 0 := by
  exact Subsingleton.elim _ _

end Field

end AlgebraicGeometry.MatrixCoordinateValues

namespace AlgebraicGeometry.MatrixEntryValues

universe r s t

/-- Matrix representation respects left scalar multiplication and addition over a semiring. -/
theorem repr_smul_add (R : Type r) (m : Type s) (n : Type t) [Semiring R]
    [Fintype m] [Finite n] (c : R) (A B : Matrix m n R) (i : m) (j : n) :
    (Matrix.stdBasis R m n).repr (c • A + B) (i, j) = c * A i j + B i j := by
  rw [matrixStdBasis_repr]
  rfl

/-- Dual matrix coordinates read sums with only decidable equality on the product index. -/
theorem dual_add (R : Type r) (m : Type s) (n : Type t) [CommSemiring R]
    [Fintype m] [Finite n] [DecidableEq (m × n)]
    (A B : Matrix m n R) (i : m) (j : n) :
    (Matrix.stdBasis R m n).dualBasis (i, j) (A + B) = A i j + B i j := by
  rw [matrixStdBasis_dual_apply]
  rfl

/-- The representation API reads six from the positive natural-number rectangle. -/
theorem naturalRectangle_repr :
    (Matrix.stdBasis ℕ (Fin 2) (Fin 3)).repr
      MatrixCoordinateValues.naturalRectangle (1, 2) = 6 := by
  rw [matrixStdBasis_repr]
  exact MatrixCoordinateValues.naturalRectangle_entry.1

/-- The dual-coordinate API reads six from the same natural-number rectangle. -/
theorem naturalRectangle_dual :
    (Matrix.stdBasis ℕ (Fin 2) (Fin 3)).dualBasis (1, 2)
      MatrixCoordinateValues.naturalRectangle = 6 := by
  rw [matrixStdBasis_dual_apply]
  exact MatrixCoordinateValues.naturalRectangle_entry.1

/-- A rectangular matrix with a nonzero off-diagonal matrix as every scalar coefficient. -/
def matrixScalarRectangle : Matrix (Fin 2) (Fin 3) (Matrix (Fin 2) (Fin 2) ℕ) :=
  Matrix.of fun _ _ ↦ Matrix.single 0 1 3

/-- Matrix-valued representation preserves the off-diagonal coefficient. -/
theorem matrixScalarRectangle_repr :
    (Matrix.stdBasis (Matrix (Fin 2) (Fin 2) ℕ) (Fin 2) (Fin 3)).repr
      matrixScalarRectangle (1, 2) = Matrix.single 0 1 3 := by
  rw [matrixStdBasis_repr]
  rfl

/-- The represented coefficient has off-diagonal entry three over the noncommutative semiring. -/
theorem matrixScalarRectangle_repr_entry :
    ((Matrix.stdBasis (Matrix (Fin 2) (Fin 2) ℕ) (Fin 2) (Fin 3)).repr
      matrixScalarRectangle (1, 2)) 0 1 = 3 := by
  rw [matrixStdBasis_repr]
  simp [matrixScalarRectangle]

end AlgebraicGeometry.MatrixEntryValues
