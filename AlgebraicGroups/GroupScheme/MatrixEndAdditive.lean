/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.MatrixEndBaseChange
public import AlgebraicGroups.GroupScheme.Vector
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Additive matrix and endomorphism functors

These are additive groups: `Multiplicative` is only the operation tag required by
`GrpCat`. The matrix comparison works for arbitrary finite, possibly empty,
index types and over every commutative algebra (including the zero ring).

Milne's item 2.7 gives additive rectangular matrix groups with polynomial
coordinates and the finite-dimensional additive End group via a chosen basis,
over a field and with positive matrix dimensions. Here the matrix and End
functors also cover empty finite indices and all commutative test algebras.
Their tensor/base-change and coordinate presentations use Mathlib's product,
matrix-basis, dual-basis and symmetric-algebra equivalences; the endomorphism
comparison uses its finite-free `IsBaseChange.end`.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.7 (additive matrix and
  finite-dimensional endomorphism groups).
- Mathlib, `Mathlib.LinearAlgebra.TensorProduct.Pi` (linear `TensorProduct.piRight`
  and `TensorProduct.piScalarRight` for finite products),
  `Mathlib.LinearAlgebra.Matrix.StdBasis` (matrix basis),
  `Mathlib.LinearAlgebra.Dual.Basis` (dual-basis entries),
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` (polynomial coordinates),
  and `Mathlib.RingTheory.TensorProduct.IsBaseChangeHom` (endomorphism base change).
-/

public section

noncomputable section

open CategoryTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

section Matrix

variable (m n : Type u) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The canonical coefficientwise scalar extension of a rectangular matrix. -/
def matrixScalarEquiv (R : Type u) [CommRing R] [Algebra K R] :
    (R ⊗[K] Matrix m n K) ≃ₗ[R] Matrix m n R :=
  ((Matrix.ofLinearEquiv K).symm.baseChange K R).trans
    ((TensorProduct.piRight K R R (fun _ : m ↦ n → K)).trans
      ((LinearEquiv.piCongrRight (fun _ : m ↦ TensorProduct.piScalarRight K R R n)).trans
        (Matrix.ofLinearEquiv R)))

@[simp]
theorem matrixScalarEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r : R) (A : Matrix m n K) (i : m) (j : n) :
    matrixScalarEquiv K m n R (r ⊗ₜ[K] A) i j = r * algebraMap K R (A i j) := by
  simpa [matrixScalarEquiv, TensorProduct.piRight, Algebra.smul_def] using
    (mul_comm (algebraMap K R (A i j)) r)

/-- The additive group of rectangular matrices, functorial in the coefficient algebra. -/
@[expose] def additiveMatrixFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative (Matrix m n R))
  map f := GrpCat.ofHom
    (AddMonoidHom.toMultiplicative (f.hom.toAddMonoidHom.mapMatrix))
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro A
    change ((𝟙 R : R ⟶ R).hom.toAddMonoidHom.mapMatrix A.toAdd) = A.toAdd
    ext i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro A
    change ((f ≫ g).hom.toAddMonoidHom.mapMatrix A.toAdd) =
      g.hom.toAddMonoidHom.mapMatrix (f.hom.toAddMonoidHom.mapMatrix A.toAdd)
    ext i j
    rfl

/-- Scalar extension from source-order tensors to matrices, retaining `K`-linearity. -/
@[expose] def matrixVectorLinearEquiv (R : Type u) [CommRing R] [Algebra K R] :
    (Matrix m n K ⊗[K] R) ≃ₗ[K] Matrix m n R :=
  (TensorProduct.comm K (Matrix m n K) R).trans
    ((matrixScalarEquiv K m n R).restrictScalars K)

/-- The additive matrix group is the scalar extension of the space of matrices. -/
@[expose] def matrixVectorMulEquiv (R : Type u) [CommRing R] [Algebra K R] :
    Multiplicative (Matrix m n K ⊗[K] R) ≃* Multiplicative (Matrix m n R) :=
  (matrixVectorLinearEquiv K m n R).toAddEquiv.toMultiplicative

@[simp]
theorem matrixVectorMulEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (A : Matrix m n K) (r : R) (i : m) (j : n) :
    (matrixVectorMulEquiv K m n R (.ofAdd (A ⊗ₜ[K] r))).toAdd i j =
      algebraMap K R (A i j) * r := by
  simp [matrixVectorMulEquiv, matrixVectorLinearEquiv, matrixScalarEquiv_tmul, mul_comm]

/-- Source-order tensor comparison with additive matrices, as a natural group isomorphism. -/
@[expose] def matrixVectorGroupIso :
    vectorGroupFunctor K (Matrix m n K) ≅ additiveMatrixFunctor K m n :=
  NatIso.ofComponents
    (fun R ↦ (matrixVectorMulEquiv K m n R).toGrpIso)
    (fun {R S} f ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      change matrixVectorMulEquiv K m n S (.ofAdd
          (TensorProduct.map (LinearMap.id : Matrix m n K →ₗ[K] Matrix m n K)
            f.hom.toLinearMap x.toAdd)) =
        .ofAdd (f.hom.toAddMonoidHom.mapMatrix
          (matrixVectorMulEquiv K m n R x).toAdd)
      have aux (y : Matrix m n K ⊗[K] R) :
          matrixVectorLinearEquiv K m n S
            (TensorProduct.map (LinearMap.id : Matrix m n K →ₗ[K] Matrix m n K)
              f.hom.toLinearMap y) =
          f.hom.toAddMonoidHom.mapMatrix (matrixVectorLinearEquiv K m n R y) := by
        induction y using TensorProduct.inductionOn with
        | tmul A r =>
          ext i j
          simp [matrixVectorLinearEquiv, matrixScalarEquiv_tmul, map_mul, mul_comm]
        | add y z hy hz =>
          simp only [map_add, hy, hz]
      exact congrArg Multiplicative.ofAdd (aux x.toAdd))

/-- The additive rectangular matrix functor is represented by the affine
vector-group scheme. This extends the positive-size matrix example in Milne,
*Algebraic Groups* (2017), item 2.7, to empty finite index types. -/
@[expose] def matrixGroupPointsIso :
    additiveMatrixFunctor K m n ≅ vectorGroupPointsFunctor K (Matrix m n K) :=
  (matrixVectorGroupIso K m n).symm ≪≫ vectorGroupPointsIso K (Matrix m n K)

/-- Polynomial coordinates on rectangular matrices, indexed by row and column. -/
def matrixCoordinateRingEquiv :
    vectorGroupCoordinateRing K (Matrix m n K) ≃ₐ[K] MvPolynomial (m × n) K :=
  SymmetricAlgebra.equivMvPolynomial (Matrix.stdBasis K m n).dualBasis

theorem matrixCoordinateRingEquiv_ι (i : m) (j : n) :
    matrixCoordinateRingEquiv K m n
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (i, j))) =
        MvPolynomial.X (i, j) := by
  exact SymmetricAlgebra.equivMvPolynomial_ι_apply
    (Matrix.stdBasis K m n).dualBasis (i, j)

/-- A matrix point evaluates the dual symmetric coordinate ring. -/
@[expose] def matrixCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (A : Matrix m n R) : vectorGroupCoordinateRing K (Matrix m n K) →ₐ[K] R :=
  (vectorGroupMulEquivAlgHom K (Matrix m n K) R
    ((matrixVectorMulEquiv K m n R).symm (.ofAdd A))).ofConv

/-- The represented matrix point is precisely the coordinate evaluation map. -/
theorem matrixGroupPointsIso_apply_left (R : CommAlgCat K) (A : Matrix m n R) :
    ((matrixGroupPointsIso K m n).hom.app R (.ofAdd A)).left =
      Spec.map (CommRingCat.ofHom (matrixCoordinateEval K m n R A).toRingHom) :=
  rfl

theorem matrixStdBasis_dual_apply (A : Matrix m n K) (i : m) (j : n) :
    (Matrix.stdBasis K m n).dualBasis (i, j) A = A i j := by
  rw [Module.Basis.dualBasis_apply]
  simp [Matrix.stdBasis]

@[simp]
theorem matrixStdBasis_repr (A : Matrix m n K) (i : m) (j : n) :
    (Matrix.stdBasis K m n).repr A (i, j) = A i j := by
  simpa only [Module.Basis.dualBasis_apply] using matrixStdBasis_dual_apply K m n A i j

/-- Basis-dual evaluation reads the corresponding rectangular matrix entry. -/
theorem matrixTensorEntry (R : Type u) [CommRing R] [Algebra K R]
    (x : Matrix m n K ⊗[K] R) (i : m) (j : n) :
    vectorGroupTensorDualEquiv K (Matrix m n K) R x
      ((Matrix.stdBasis K m n).dualBasis (i, j)) =
        matrixVectorLinearEquiv K m n R x i j := by
  induction x using TensorProduct.inductionOn with
  | tmul A r =>
    simp [vectorGroupTensorDualEquiv_tmul, matrixVectorLinearEquiv,
      matrixScalarEquiv_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    simpa only [map_add, LinearMap.add_apply, Matrix.add_apply] using
      congrArg₂ (· + ·) hx hy

theorem matrixCoordinateEval_ι (R : Type u) [CommRing R] [Algebra K R]
    (A : Matrix m n R) (i : m) (j : n) :
    matrixCoordinateEval K m n R A
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (i, j))) = A i j := by
  let x := ((matrixVectorMulEquiv K m n R).symm (.ofAdd A)).toAdd
  have h := matrixTensorEntry K m n R x i j
  change (vectorGroupMulEquivAlgHom K (Matrix m n K) R (.ofAdd x)).ofConv
    (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K m n).dualBasis (i, j))) = A i j
  rw [vectorGroupMulEquivAlgHom_ι]
  rw [h]
  change (matrixVectorLinearEquiv K m n R)
    (((matrixVectorLinearEquiv K m n R).symm A)) i j = A i j
  simp

/-- Formal polynomial substitution represents matrix-coordinate evaluation;
this does not identify polynomials with functions on field-valued points. -/
theorem matrixCoordinateEval_polynomial (R : Type u) [CommRing R] [Algebra K R]
    (A : Matrix m n R) :
    (matrixCoordinateEval K m n R A).comp (matrixCoordinateRingEquiv K m n).symm.toAlgHom =
      MvPolynomial.aeval (fun p : m × n ↦ A p.1 p.2) := by
  apply MvPolynomial.algHom_ext
  intro p
  rcases p with ⟨row, col⟩
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, MvPolynomial.aeval_X]
  change matrixCoordinateEval K m n R A
    ((SymmetricAlgebra.equivMvPolynomial (Matrix.stdBasis K m n).dualBasis).symm
      (MvPolynomial.X (row, col))) = A row col
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  exact matrixCoordinateEval_ι K m n R A row col

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The rectangular generic matrix evaluates at the supplied entries. -/
theorem matrixPolynomialX_evaluation (R : Type u) [CommRing R] [Algebra K R]
    (A : Matrix m n R) :
    (Matrix.mvPolynomialX m n K).map
      (MvPolynomial.aeval (fun p : m × n ↦ A p.1 p.2)) = A := by
  exact Matrix.mvPolynomialX_map_eval₂ _ A

end Matrix

section End

variable (V : Type u) [AddCommGroup V] [Module K V]

/-- The additive group of endomorphisms of scalar extension, functorial for
every algebra map; finite dimension is not needed for this definition. -/
@[expose] def additiveEndFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative (Module.End R (R ⊗[K] V)))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    (endBaseChangeAddHom K V _ _ f.hom))
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change endBaseChange K V R R (AlgHom.id K R) x = x
    exact endBaseChange_id K V R x
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change endBaseChange K V _ _ (g.hom.comp f.hom) x =
      endBaseChange K V _ _ g.hom (endBaseChange K V _ _ f.hom x)
    exact (endBaseChange_comp K V _ _ _ f.hom g.hom x).symm

variable [FiniteDimensional K V]

/-- The existing finite-free endomorphism equivalence, expressed in source tensor order. -/
def endVectorLinearEquiv (R : Type u) [CommRing R] [Algebra K R] :
    (Module.End K V ⊗[K] R) ≃ₗ[K] Module.End R (R ⊗[K] V) :=
  (TensorProduct.comm K (Module.End K V) R).trans
    (((TensorProduct.isBaseChange K V R).end).equiv.restrictScalars K)

/-- An explicit pure-tensor action; the finite-free equivalence is not reproved. -/
@[simp]
theorem endVectorLinearEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r s : R) (f : Module.End K V) (v : V) :
    endVectorLinearEquiv K V R (f ⊗ₜ[K] r) (s ⊗ₜ[K] v) =
      (r * s) ⊗ₜ[K] f v := by
  change (((TensorProduct.isBaseChange K V R).end).equiv (r ⊗ₜ[K] f))
    (s ⊗ₜ[K] v) = (r * s) ⊗ₜ[K] f v
  rw [IsBaseChange.equiv_tmul]
  have h : ((TensorProduct.isBaseChange K V R).endHom f) (s ⊗ₜ[K] v) =
      s ⊗ₜ[K] f v := by
    conv_lhs => rw [TensorProduct.tmul_eq_smul_one_tmul s v]
    rw [map_smul]
    have hv := (TensorProduct.isBaseChange K V R).endHom_comp_apply f v
    rw [TensorProduct.mk_apply] at hv
    rw [hv]
    exact (TensorProduct.tmul_eq_smul_one_tmul s (f v)).symm
  change r • ((TensorProduct.isBaseChange K V R).endHom f) (s ⊗ₜ[K] v) = _
  rw [h, TensorProduct.smul_tmul']
  rfl

/-- The additive group comparison for finite-dimensional endomorphisms. -/
@[expose] def endVectorMulEquiv (R : Type u) [CommRing R] [Algebra K R] :
    Multiplicative (Module.End K V ⊗[K] R) ≃*
      Multiplicative (Module.End R (R ⊗[K] V)) :=
  (endVectorLinearEquiv K V R).toAddEquiv.toMultiplicative

/-- Naturality of finite-free endomorphism scalar extension for every algebra map. -/
theorem endVectorLinearEquiv_naturality (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (x : Module.End K V ⊗[K] R) :
    endVectorLinearEquiv K V S
      (TensorProduct.map (LinearMap.id : Module.End K V →ₗ[K] Module.End K V)
        g.toLinearMap x) =
      endBaseChange K V R S g (endVectorLinearEquiv K V R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f r =>
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s v =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        endVectorLinearEquiv_tmul, endBaseChange_tmul]
      simp only [mul_one, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']
      congr 1
      change g r * s = s * g r
      exact mul_comm _ _
    | add y z hy hz =>
      simp only [map_add, hy, hz]
  | add x y hx hy =>
    simp only [map_add]
    change _ = (endBaseChangeAddHom K V R S g)
      (endVectorLinearEquiv K V R x + endVectorLinearEquiv K V R y)
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

/-- Natural additive End/vector-group equivalence, independent of basis. -/
@[expose] def endVectorGroupIso :
    vectorGroupFunctor K (Module.End K V) ≅ additiveEndFunctor K V :=
  NatIso.ofComponents (fun R ↦ (endVectorMulEquiv K V R).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      change endVectorLinearEquiv K V S
        (TensorProduct.map (LinearMap.id : Module.End K V →ₗ[K] Module.End K V)
          g.hom.toLinearMap x) =
        endBaseChange K V R S g.hom (endVectorLinearEquiv K V R x)
      exact endVectorLinearEquiv_naturality K V R S g.hom x)

/-- The finite-dimensional additive End functor is represented by the existing
basis-independent vector-group scheme and its finite-type coordinate ring,
refining the chosen-basis matrix comparison of Milne, *Algebraic Groups*
(2017), item 2.7, without choosing a basis. -/
@[expose] def endGroupPointsIso :
    additiveEndFunctor K V ≅ vectorGroupPointsFunctor K (Module.End K V) :=
  (endVectorGroupIso K V).symm ≪≫ vectorGroupPointsIso K (Module.End K V)

/-- The canonical basis-independent coordinate evaluation of an End point. -/
@[expose] def endCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) :
    vectorGroupCoordinateRing K (Module.End K V) →ₐ[K] R :=
  (vectorGroupMulEquivAlgHom K (Module.End K V) R
    ((endVectorMulEquiv K V R).symm (.ofAdd f))).ofConv

/-- Under the represented group isomorphism, End coordinates give its scheme point. -/
theorem endGroupPointsIso_apply_left (R : CommAlgCat K)
    (f : Module.End R (R ⊗[K] V)) :
    ((endGroupPointsIso K V).hom.app R (.ofAdd f)).left =
      Spec.map (CommRingCat.ofHom (endCoordinateEval K V R f).toRingHom) :=
  rfl

section Basis

variable (i : Type u) [Fintype i] [DecidableEq i] (b : Module.Basis i K V)

/-- Chosen-basis additive coordinates on scalar-extended endomorphisms. -/
@[expose] def endMatrixLinearEquiv (R : Type u) [CommRing R] [Algebra K R] :
    Module.End R (R ⊗[K] V) ≃ₗ[R] Matrix i i R :=
  (LinearMap.toMatrixAlgEquiv ((TensorProduct.isBaseChange K V R).basis b)).toLinearEquiv

omit [FiniteDimensional K V] in
theorem endMatrixLinearEquiv_apply (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) (row col : i) :
    endMatrixLinearEquiv K V i b R f row col =
      ((TensorProduct.isBaseChange K V R).basis b).repr
        (f ((TensorProduct.isBaseChange K V R).basis b col)) row := by
  exact LinearMap.toMatrix_apply _ _ f row col

/-- On a pure tensor, the chosen-basis `(row,col)` entry is the scalar
coefficient times the base-changed matrix coefficient of the original map. -/
@[simp]
theorem endMatrixLinearEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r : R) (f : Module.End K V) (row col : i) :
    endMatrixLinearEquiv K V i b R (endVectorLinearEquiv K V R (f ⊗ₜ[K] r)) row col =
      r * algebraMap K R (b.repr (f (b col)) row) := by
  change endMatrixLinearEquiv K V i b R
    (((TensorProduct.isBaseChange K V R).end).equiv (r ⊗ₜ[K] f)) row col = _
  rw [IsBaseChange.equiv_tmul, map_smul, Matrix.smul_apply]
  change r • (((TensorProduct.isBaseChange K V R).endHom f).toMatrix
    ((TensorProduct.isBaseChange K V R).basis b)
    ((TensorProduct.isBaseChange K V R).basis b)) row col = _
  rw [IsBaseChange.endHom_toMatrix]
  simp [LinearMap.toMatrix_apply]

/-- Chosen-basis coordinate transport commutes with every coefficient algebra map. -/
theorem endMatrixLinearEquiv_naturality (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (R ⊗[K] V)) :
    endMatrixLinearEquiv K V i b S (endBaseChange K V R S g f) =
      g.toAddMonoidHom.mapMatrix (endMatrixLinearEquiv K V i b R f) := by
  obtain ⟨x, rfl⟩ := (endVectorLinearEquiv K V R).surjective f
  rw [← endVectorLinearEquiv_naturality K V R S g x]
  induction x using TensorProduct.inductionOn with
  | tmul h r =>
    apply Matrix.ext
    intro row col
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      AddMonoidHom.mapMatrix_apply, Matrix.map_apply, endMatrixLinearEquiv_tmul]
    change g r * algebraMap K S (b.repr (h (b col)) row) =
      g (r * algebraMap K R (b.repr (h (b col)) row))
    simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- A chosen basis identifies the additive End functor with additive square
matrices, as in Milne, *Algebraic Groups* (2017), item 2.7. This natural
isomorphism also includes zero-dimensional spaces and all test algebras. -/
@[expose] def endMatrixGroupIso : additiveEndFunctor K V ≅ additiveMatrixFunctor K i i :=
  NatIso.ofComponents
    (fun R ↦ ((endMatrixLinearEquiv K V i b R).toAddEquiv.toMultiplicative).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      change endMatrixLinearEquiv K V i b S (endBaseChange K V R S g.hom x) =
        g.hom.toAddMonoidHom.mapMatrix (endMatrixLinearEquiv K V i b R x)
      exact endMatrixLinearEquiv_naturality K V i b R S g.hom x)

/-- A chosen basis exhibits the End group as the represented square-matrix
group; the representation `endGroupPointsIso` needs no basis. -/
def endMatrixGroupPointsIso :
    additiveEndFunctor K V ≅ vectorGroupPointsFunctor K (Matrix i i K) :=
  (endMatrixGroupIso K V i b) ≪≫ matrixGroupPointsIso K i i

/-- Polynomial coordinates of an endomorphism relative to a chosen basis. -/
def endMatrixCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) :
    vectorGroupCoordinateRing K (Matrix i i K) →ₐ[K] R :=
  matrixCoordinateEval K i i R (endMatrixLinearEquiv K V i b R f)

omit [FiniteDimensional K V] in
theorem endMatrixCoordinateEval_ι (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) (row col : i) :
    endMatrixCoordinateEval K V i b R f
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
        endMatrixLinearEquiv K V i b R f row col :=
  matrixCoordinateEval_ι K i i R (endMatrixLinearEquiv K V i b R f) row col

theorem endMatrixCoordinateEval_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r : R) (f : Module.End K V) (row col : i) :
    endMatrixCoordinateEval K V i b R (endVectorLinearEquiv K V R (f ⊗ₜ[K] r))
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
        r * algebraMap K R (b.repr (f (b col)) row) :=
  (endMatrixCoordinateEval_ι K V i b R _ row col).trans
    (endMatrixLinearEquiv_tmul K V i b R r f row col)

variable (j : Type u) [Fintype j] [DecidableEq j] (c : Module.Basis j K V)

/-- Coordinates associated with two bases differ by a natural change of basis;
the canonical End representation itself has no chosen basis. -/
def endMatrixBasisChangeIso :
    additiveMatrixFunctor K i i ≅ additiveMatrixFunctor K j j :=
  (endMatrixGroupIso K V i b).symm ≪≫ endMatrixGroupIso K V j c

@[simp]
theorem endMatrixBasisChangeIso_apply (R : CommAlgCat K)
    (f : Module.End R (R ⊗[K] V)) :
    (endMatrixBasisChangeIso K V i b j c).hom.app R
      (.ofAdd (endMatrixLinearEquiv K V i b R f)) =
        .ofAdd (endMatrixLinearEquiv K V j c R f) := by
  change Multiplicative.ofAdd
      (endMatrixLinearEquiv K V j c R
        ((endMatrixLinearEquiv K V i b R).symm (endMatrixLinearEquiv K V i b R f))) =
      Multiplicative.ofAdd (endMatrixLinearEquiv K V j c R f)
  simp

/-- The second basis's polynomial generators evaluate to its own coordinates
after the explicit natural change-of-basis isomorphism. -/
theorem endMatrixBasisChangeCoordinate_ι (R : CommAlgCat K)
    (f : Module.End R (R ⊗[K] V)) (row col : j) :
    matrixCoordinateEval K j j R
      ((endMatrixBasisChangeIso K V i b j c).hom.app R
        (.ofAdd (endMatrixLinearEquiv K V i b R f))).toAdd
      (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K j j).dualBasis (row, col))) =
        endMatrixLinearEquiv K V j c R f row col := by
  rw [endMatrixBasisChangeIso_apply]
  exact matrixCoordinateEval_ι K j j R (endMatrixLinearEquiv K V j c R f) row col

end Basis

end End

end AlgebraicGeometry

#lint
