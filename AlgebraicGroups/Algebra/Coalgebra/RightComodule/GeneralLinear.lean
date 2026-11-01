/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.CoefficientMatrixUnit
public import AlgebraicGroups.Algebra.Coalgebra.Evaluation.Action
public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# General linear coordinates of a based right comodule

A finite basis of a right comodule over a commutative Hopf algebra gives an
algebra map from the determinant-localization coordinate ring of the general
linear group. Its matrix entries are the coefficients of the given coaction,
with the coordinate functional indexing rows and the input basis vector
indexing columns.

For every commutative coefficient algebra, evaluation of the whole coordinate
ring gives the matrix of the comodule's point action on the scalar extension
of the original module. The matrix comparison uses `Units.mapEquiv` and
`LinearMap.toMatrixAlgEquiv` with `Algebra.TensorProduct.basis`. Decoding this
matrix recovers the point action on every tensor, naturally in the coefficient
algebra. The module, basis index, Hopf algebra, and coefficient algebras have
independent universes. Empty bases and zero rings are included.

## References

* The coefficient and point-action constructions in
  `AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients`,
  `AlgebraicGroups.Algebra.Coalgebra.CoefficientMatrixUnit`, and
  `AlgebraicGroups.Algebra.Coalgebra.Evaluation.Action`.
* `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing`, for evaluation on
  the determinant localization and its algebra-map extensionality theorem.
* Mathlib's `Algebra.TensorProduct.basis`, `LinearMap.toMatrixAlgEquiv`, and
  `Units.mapEquiv`, for the based matrix presentation of invertible operators.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u a v w r s

namespace Coalgebra.RightComodule

variable {K : Type u} {A : Type a} {U : Type v} {I : Type w}
variable [CommRing K] [CommRing A] [HopfAlgebra K A]
variable [AddCommMonoid U] [Module K U] [Fintype I] [DecidableEq I]

/-- General linear coordinates of the coefficient matrix of a based right
comodule, evaluated at its Hopf coefficient matrix unit. -/
def generalLinearCoordinateHom (X : RightComodule K A U) (b : Module.Basis I K U) :
    GeneralLinearCoordinateRing.CoordinateRing K I →ₐ[K] A :=
  GeneralLinearCoordinateRing.evaluate
    (HopfAlgebra.coefficientMatrixUnit (R := K)
      (fun i j ↦ X.coefficient (b.coord i) (b j))
      (X.comul_coefficient_basis b) (X.counit_coefficient_basis b))

/-- An entry coordinate evaluates to the corresponding coefficient of the
specified coaction. -/
theorem generalLinearCoordinateHom_matrix (X : RightComodule K A U)
    (b : Module.Basis I K U) (i j : I) :
    X.generalLinearCoordinateHom b (GeneralLinearCoordinateRing.matrix K I i j) =
      X.coefficient (b.coord i) (b j) :=
  GeneralLinearCoordinateRing.evaluate_matrix _ i j

/-- Evaluating the universal invertible matrix recovers the Hopf coefficient
matrix unit. Its inverse is entrywise antipode, without a transpose. -/
@[simp] theorem toGL_generalLinearCoordinateHom (X : RightComodule K A U)
    (b : Module.Basis I K U) :
    GeneralLinearCoordinateRing.toGL (X.generalLinearCoordinateHom b) =
      HopfAlgebra.coefficientMatrixUnit (R := K)
        (fun i j ↦ X.coefficient (b.coord i) (b j))
        (X.comul_coefficient_basis b) (X.counit_coefficient_basis b) :=
  GeneralLinearCoordinateRing.toGL_evaluate _

/-- The inverse-determinant coordinate evaluates to the inverse determinant of
the Hopf coefficient matrix unit. -/
@[simp] theorem generalLinearCoordinateHom_detInverse (X : RightComodule K A U)
    (b : Module.Basis I K U) :
    X.generalLinearCoordinateHom b (GeneralLinearCoordinateRing.detInverse K I) =
      ↑(Matrix.GeneralLinearGroup.det
        (HopfAlgebra.coefficientMatrixUnit (R := K)
          (fun i j ↦ X.coefficient (b.coord i) (b j))
          (X.comul_coefficient_basis b) (X.counit_coefficient_basis b)))⁻¹ :=
  GeneralLinearCoordinateRing.evaluate_detInverse _

variable {R : Type r} [CommRing R] [Algebra K R]

/-- The matrix of the point action in the scalar-extended basis is the
entrywise evaluation of the original coefficient matrix. -/
theorem pointAction_toMatrix (X : RightComodule K A U) (b : Module.Basis I K U)
    (α : A →ₐ[K] R) (i j : I) :
    (Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
      (X.pointAction (WithConv.toConv α))) i j =
        α (X.coefficient (b.coord i) (b j)) := by
  have hcoaction : X.coaction (b j) =
      ∑ k, b k ⊗ₜ[K] X.coefficient (b.coord k) (b j) := by
    rw [X.coaction_eq_sum_basis b (b j),
      Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
    simp only [X.equivFinsuppOfBasisLeft_coaction_apply]
  change LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)
    (X.pointAction (WithConv.toConv α)).val i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply, Algebra.TensorProduct.basis_apply,
    X.pointAction_one_tmul, hcoaction]
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, eq_comm]

/-- The based point-action matrix is the image of the Hopf coefficient matrix
unit under the coefficient algebra map. -/
theorem pointAction_toMatrix_eq_map (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) :
    Units.mapEquiv
        (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
        (X.pointAction (WithConv.toConv α)) =
      Matrix.GeneralLinearGroup.map α.toRingHom
        (HopfAlgebra.coefficientMatrixUnit (R := K)
          (fun i j ↦ X.coefficient (b.coord i) (b j))
          (X.comul_coefficient_basis b) (X.counit_coefficient_basis b)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact X.pointAction_toMatrix b α i j

/-- An inverse entry of the based point-action matrix evaluates the source
antipode of the corresponding coefficient, without a transpose. -/
theorem pointAction_toMatrix_inv (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) (i j : I) :
    (Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
      (X.pointAction (WithConv.toConv α)))⁻¹ i j =
        α (HopfAlgebra.antipode K (X.coefficient (b.coord i) (b j))) := by
  rw [X.pointAction_toMatrix_eq_map b α, ← Matrix.GeneralLinearGroup.map_inv,
    Matrix.GeneralLinearGroup.map_apply]
  let M : Matrix I I A := fun k l ↦ X.coefficient (b.coord k) (b l)
  change α ((↑((HopfAlgebra.coefficientMatrixUnit (R := K) M
    (X.comul_coefficient_basis b) (X.counit_coefficient_basis b))⁻¹) : Matrix I I A) i j) =
      α (HopfAlgebra.antipode K (M i j))
  exact congrArg α (HopfAlgebra.coefficientMatrixUnit_inv_apply
    (R := K) (A := A) (ι := I) M
    (X.comul_coefficient_basis b) (X.counit_coefficient_basis b) i j)

/-- Over every commutative coefficient algebra, the whole coordinate map is
evaluation at the matrix of the point action on the given scalar extension. -/
theorem generalLinearCoordinateHom_comp (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) :
    α.comp (X.generalLinearCoordinateHom b) =
      GeneralLinearCoordinateRing.evaluate
        (Units.mapEquiv
          (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
          (X.pointAction (WithConv.toConv α))) := by
  apply GeneralLinearCoordinateRing.hom_ext
  intro i j
  rw [AlgHom.comp_apply, X.generalLinearCoordinateHom_matrix,
    GeneralLinearCoordinateRing.evaluate_matrix, X.pointAction_toMatrix]

/-- The invertible matrix obtained from the coordinate map is the based matrix
of the point action over the coefficient algebra. -/
theorem toGL_generalLinearCoordinateHom_comp (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) :
    GeneralLinearCoordinateRing.toGL (α.comp (X.generalLinearCoordinateHom b)) =
      Units.mapEquiv
        (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
        (X.pointAction (WithConv.toConv α)) := by
  rw [X.generalLinearCoordinateHom_comp b α, GeneralLinearCoordinateRing.toGL_evaluate]

/-- Decoding the evaluated coordinate matrix returns the point action on the
original scalar-extended module. -/
theorem generalLinearCoordinateHom_decode (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) :
    (Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        (GeneralLinearCoordinateRing.toGL (α.comp (X.generalLinearCoordinateHom b))) =
      X.pointAction (WithConv.toConv α) := by
  rw [X.toGL_generalLinearCoordinateHom_comp b α, MulEquiv.symm_apply_apply]

/-- The decoded endomorphism is coefficient evaluation on every tensor. -/
theorem generalLinearCoordinateHom_decode_val (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) :
    ((Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        (GeneralLinearCoordinateRing.toGL (α.comp (X.generalLinearCoordinateHom b)))).val =
      X.evaluate α.toLinearMap := by
  rw [X.generalLinearCoordinateHom_decode b α, X.pointAction_val]

/-- On a pure tensor, decoding evaluates the given coaction and then multiplies
by its scalar factor. -/
theorem generalLinearCoordinateHom_decode_tmul (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R) (t : R) (x : U) :
    ((Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        (GeneralLinearCoordinateRing.toGL (α.comp (X.generalLinearCoordinateHom b)))).val
          (t ⊗ₜ[K] x) =
      t • _root_.TensorProduct.map α.toLinearMap (LinearMap.id : U →ₗ[K] U)
        (TensorProduct.comm K U A (X.coaction x)) := by
  rw [X.generalLinearCoordinateHom_decode_val b α, X.evaluate_tmul]

/-- The point-action matrices commute with arbitrary change of coefficient
algebra, including coefficient algebras in an independent universe. -/
theorem pointAction_toMatrix_natural (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R)
    {S : Type s} [CommRing S] [Algebra K S] (q : R →ₐ[K] S) :
    Units.mapEquiv
        (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis S b)).toMulEquiv
        (X.pointAction (WithConv.toConv (q.comp α))) =
      Matrix.GeneralLinearGroup.map q.toRingHom
        (Units.mapEquiv
          (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv
          (X.pointAction (WithConv.toConv α))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rewrite [Matrix.GeneralLinearGroup.map_apply, X.pointAction_toMatrix,
    X.pointAction_toMatrix, AlgHom.comp_apply]
  rfl

/-- Coefficient change intertwines the decoded operators on every tensor; no
injectivity of the coefficient map or of a tensor inclusion is assumed. -/
theorem generalLinearCoordinateHom_decode_naturality (X : RightComodule K A U)
    (b : Module.Basis I K U) (α : A →ₐ[K] R)
    {S : Type s} [CommRing S] [Algebra K S] (q : R →ₐ[K] S) (z : R ⊗[K] U) :
    _root_.TensorProduct.map q.toLinearMap (LinearMap.id : U →ₗ[K] U)
        (((Units.mapEquiv
          (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
            (GeneralLinearCoordinateRing.toGL (α.comp (X.generalLinearCoordinateHom b)))).val z) =
      ((Units.mapEquiv
        (LinearMap.toMatrixAlgEquiv (Algebra.TensorProduct.basis S b)).toMulEquiv).symm
          (GeneralLinearCoordinateRing.toGL ((q.comp α).comp
            (X.generalLinearCoordinateHom b)))).val
        (_root_.TensorProduct.map q.toLinearMap (LinearMap.id : U →ₗ[K] U) z) := by
  rw [X.generalLinearCoordinateHom_decode_val b α,
    X.generalLinearCoordinateHom_decode_val b (q.comp α)]
  simpa only [AlgHom.comp_toLinearMap] using X.evaluate_naturality_apply α.toLinearMap q z

end Coalgebra.RightComodule
