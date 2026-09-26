/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearBaseChange
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.MatrixEndAdditive
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Finite-basis general linear groups

A chosen finite basis identifies automorphisms of the scalar extension of a
module with invertible matrices, naturally in every commutative coefficient
algebra. Composing with the existing matrix GL representation gives affine
group-scheme points; the construction does not require a field or flatness.
-/

public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

/-- The basis induced on a scalar extension, including the empty basis. -/
@[expose] def generalLinearScalarBasis (R : Type u) [CommRing R] [Algebra K R] :
    Module.Basis indexType R (SourceOrderTensor K V R) :=
  (TensorProduct.isBaseChange K V R).basis basis

omit [Fintype indexType] [DecidableEq indexType] in
@[simp] theorem generalLinearScalarBasis_apply (R : Type u) [CommRing R] [Algebra K R]
    (index : indexType) :
    generalLinearScalarBasis K V indexType basis R index = 1 ⊗ₜ[K] basis index :=
  IsBaseChange.basis_apply basis (TensorProduct.isBaseChange K V R) index

omit [Fintype indexType] [DecidableEq indexType] in
/-- Coefficients of scalar-extended tensors commute with every algebra homomorphism. -/
theorem generalLinearScalarBasis_repr_rTensor
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (x : SourceOrderTensor K V R) (index : indexType) :
    (generalLinearScalarBasis K V indexType basis S).repr
        ((g.toLinearMap.rTensor V) x) index =
      g ((generalLinearScalarBasis K V indexType basis R).repr x index) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    have basis_repr (T : Type u) [CommRing T] [Algebra K T] :
        (generalLinearScalarBasis K V indexType basis T).repr (1 ⊗ₜ[K] v) index =
          algebraMap K T (basis.repr v index) :=
      IsBaseChange.basis_repr_comp_apply basis (TensorProduct.isBaseChange K V T) v index
    rw [LinearMap.rTensor_tmul]
    conv_lhs => rw [TensorProduct.tmul_eq_smul_one_tmul]
    conv_rhs => rw [TensorProduct.tmul_eq_smul_one_tmul]
    simp only [map_smul, Finsupp.smul_apply, Algebra.smul_def, basis_repr]
    simp
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Matrix of an endomorphism after scalar extension, over arbitrary commutative rings. -/
theorem generalLinearScalarBasis_endBaseChange_matrix
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderTensor K V R)) :
    (LinearMap.toMatrixAlgEquiv (generalLinearScalarBasis K V indexType basis S))
        (endBaseChange K V R S g f) =
      ((LinearMap.toMatrixAlgEquiv (generalLinearScalarBasis K V indexType basis R)) f).map g := by
  ext row column
  rw [LinearMap.toMatrixAlgEquiv_apply]
  simp only [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply]
  rw [generalLinearScalarBasis_apply, generalLinearScalarBasis_apply,
    endBaseChange_tmul, one_smul, generalLinearScalarBasis_repr_rTensor]

/-- The matrix comparison uses the native algebra equivalence and native units. -/
@[expose] def generalLinearModuleMatrixEquiv (R : Type u) [CommRing R] [Algebra K R] :
    LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R) ≃*
      Matrix.GeneralLinearGroup indexType R :=
  Units.mapEquiv
    (LinearMap.toMatrixAlgEquiv (generalLinearScalarBasis K V indexType basis R)).toMulEquiv

@[simp] theorem generalLinearModuleMatrixEquiv_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) (row column : indexType) :
    generalLinearModuleMatrixEquiv K V indexType basis R f row column =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f.val ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  exact LinearMap.toMatrixAlgEquiv_apply _ _ row column

/-- A matrix acts on basis coordinates by the original module automorphism. -/
theorem generalLinearModuleMatrixEquiv_action (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (x : SourceOrderTensor K V R) :
    (generalLinearModuleMatrixEquiv K V indexType basis R f).val *ᵥ
        (generalLinearScalarBasis K V indexType basis R).repr x =
      (generalLinearScalarBasis K V indexType basis R).repr (f.val x) :=
  LinearMap.toMatrix_mulVec_repr _ _ f.val x

/-- Chosen-basis matrix comparison commutes with every coefficient map. -/
theorem generalLinearModuleMatrixEquiv_natural (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleMatrixEquiv K V indexType basis S
        (generalLinearModuleBaseChange K V R S g f) =
      Matrix.GeneralLinearGroup.map g.toRingHom
        (generalLinearModuleMatrixEquiv K V indexType basis R f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrArg (fun matrix : Matrix indexType indexType S ↦ matrix row column)
    (generalLinearScalarBasis_endBaseChange_matrix K V indexType basis R S g f.val)

/-- A finite chosen basis gives a natural group isomorphism to matrix GL. -/
@[expose] def generalLinearModuleMatrixIso :
    generalLinearModuleFunctor K V ≅ generalLinearGroupFunctor K indexType :=
  NatIso.ofComponents
    (fun R ↦ (generalLinearModuleMatrixEquiv K V indexType basis R).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      exact generalLinearModuleMatrixEquiv_natural K V indexType basis R S g.hom f)

/-- The literal tensor order has the same chosen-basis matrix presentation. -/
def sourceOrderedGeneralLinearMatrixIso :
    sourceOrderedGeneralLinearFunctor K V ≅ generalLinearGroupFunctor K indexType :=
  sourceOrderedGeneralLinearIso K V ≪≫ generalLinearModuleMatrixIso K V indexType basis

/-- The group of automorphisms is represented, after choosing a finite basis,
by the existing finite-type general linear group scheme. -/
@[expose] def generalLinearModulePointsIso :
    generalLinearModuleFunctor K V ≅ generalLinearGroupPointsFunctor K indexType :=
  (generalLinearModuleMatrixIso K V indexType basis) ≪≫ generalLinearGroupPointsIso K indexType

/-- Coordinate evaluation of an automorphism, through its chosen-basis matrix. -/
@[expose] def generalLinearModuleCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    CoordinateRing K indexType →ₐ[K] R :=
  evaluate (K := K) (generalLinearModuleMatrixEquiv K V indexType basis R f)

theorem generalLinearModuleCoordinateEval_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (row column : indexType) :
    generalLinearModuleCoordinateEval K V indexType basis R f
        (matrix K indexType row column) =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f.val ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  exact (evaluate_matrix _ _ _).trans
    (generalLinearModuleMatrixEquiv_entry K V indexType basis R f row column)

@[simp] theorem generalLinearModuleCoordinateEval_detInverse (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleCoordinateEval K V indexType basis R f (detInverse K indexType) =
      ↑(Matrix.GeneralLinearGroup.det
        (generalLinearModuleMatrixEquiv K V indexType basis R f))⁻¹ :=
  evaluate_detInverse _

/-- The represented point has the expected `Spec.map` on its underlying schemes. -/
theorem generalLinearModulePointsIso_apply_left (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    ((generalLinearModulePointsIso K V indexType basis).hom.app R f).left =
      Spec.map (CommRingCat.ofHom
        (generalLinearModuleCoordinateEval K V indexType basis R f).toRingHom) := rfl

/-- Pullback of an entry coordinate at the represented automorphism point. -/
theorem generalLinearModulePoint_preimage_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (row column : indexType) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K indexType R
      (generalLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
        (matrix K indexType row column) =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f.val ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  exact (generalLinearGroupPoint_preimage_entry K indexType R
    (generalLinearModuleMatrixEquiv K V indexType basis R f) row column).trans
    (generalLinearModuleMatrixEquiv_entry K V indexType basis R f row column)

/-- Pullback of the inverse determinant coordinate, not a determinant scheme morphism. -/
theorem generalLinearModulePoint_preimage_detInverse (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K indexType R
      (generalLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
        (detInverse K indexType) =
      ↑(Matrix.GeneralLinearGroup.det
        (generalLinearModuleMatrixEquiv K V indexType basis R f))⁻¹ := by
  exact generalLinearGroupPoint_preimage_detInverse K indexType R
    (generalLinearModuleMatrixEquiv K V indexType basis R f)

/-- The literal-order module is represented by the same group scheme after transport. -/
def sourceOrderedGeneralLinearPointsIso :
    sourceOrderedGeneralLinearFunctor K V ≅ generalLinearGroupPointsFunctor K indexType :=
  sourceOrderedGeneralLinearIso K V ≪≫ generalLinearModulePointsIso K V indexType basis

variable (otherBasis thirdBasis : Module.Basis indexType K V)

/-- The change of chosen matrix presentation of the same automorphism group. -/
def generalLinearModuleChangeBasis (R : Type u) [CommRing R] [Algebra K R] :
    Matrix.GeneralLinearGroup indexType R ≃* Matrix.GeneralLinearGroup indexType R :=
  (generalLinearModuleMatrixEquiv K V indexType basis R).symm.trans
    (generalLinearModuleMatrixEquiv K V indexType otherBasis R)

@[simp] theorem generalLinearModuleChangeBasis_apply (R : Type u)
    [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleChangeBasis K V indexType basis otherBasis R
        (generalLinearModuleMatrixEquiv K V indexType basis R f) =
      generalLinearModuleMatrixEquiv K V indexType otherBasis R f := by
  simp [generalLinearModuleChangeBasis]

theorem generalLinearModuleChangeBasis_id (R : Type u) [CommRing R] [Algebra K R] :
    generalLinearModuleChangeBasis K V indexType basis basis R = MulEquiv.refl _ := by
  ext f
  simp [generalLinearModuleChangeBasis]

theorem generalLinearModuleChangeBasis_comp (R : Type u) [CommRing R] [Algebra K R] :
    (generalLinearModuleChangeBasis K V indexType basis otherBasis R).trans
        (generalLinearModuleChangeBasis K V indexType otherBasis thirdBasis R) =
      generalLinearModuleChangeBasis K V indexType basis thirdBasis R := by
  ext f
  simp [generalLinearModuleChangeBasis]

/-- Change of matrix coordinates is natural in coefficient algebras. -/
theorem generalLinearModuleChangeBasis_natural
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Matrix.GeneralLinearGroup indexType R) :
    generalLinearModuleChangeBasis K V indexType basis otherBasis S
        (Matrix.GeneralLinearGroup.map g.toRingHom f) =
      Matrix.GeneralLinearGroup.map g.toRingHom
        (generalLinearModuleChangeBasis K V indexType basis otherBasis R f) := by
  obtain ⟨h, rfl⟩ := (generalLinearModuleMatrixEquiv K V indexType basis R).surjective f
  rw [← generalLinearModuleMatrixEquiv_natural K V indexType basis R S g h]
  simp only [generalLinearModuleChangeBasis_apply]
  exact generalLinearModuleMatrixEquiv_natural K V indexType otherBasis R S g h

/-- Natural change between finite-basis matrix presentations. -/
def generalLinearModuleChangeBasisIso :
    generalLinearGroupFunctor K indexType ≅ generalLinearGroupFunctor K indexType :=
  (generalLinearModuleMatrixIso K V indexType basis).symm ≪≫
    generalLinearModuleMatrixIso K V indexType otherBasis

theorem generalLinearModulePointsIso_changeBasis (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModulePointsIso K V indexType otherBasis).hom.app R f =
      (generalLinearGroupPointsIso K indexType).hom.app R
        (generalLinearModuleChangeBasis K V indexType basis otherBasis R
          (generalLinearModuleMatrixEquiv K V indexType basis R f)) := by
  simp only [generalLinearModulePointsIso, generalLinearModuleChangeBasis,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- Matrix entries after a change of basis are coefficients of the same automorphism. -/
theorem generalLinearModuleChangeBasis_entry (R : Type u) [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (row column : indexType) :
    generalLinearModuleChangeBasis K V indexType basis otherBasis R
        (generalLinearModuleMatrixEquiv K V indexType basis R f) row column =
      (generalLinearScalarBasis K V indexType otherBasis R).repr
        (f.val ((generalLinearScalarBasis K V indexType otherBasis R) column)) row := by
  rw [generalLinearModuleChangeBasis_apply, generalLinearModuleMatrixEquiv_entry]

/-- Changing the presentation does not change the automorphism acting on vectors. -/
theorem generalLinearModuleChangeBasis_action (R : Type u) [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (x : SourceOrderTensor K V R) :
    (generalLinearModuleChangeBasis K V indexType basis otherBasis R
      (generalLinearModuleMatrixEquiv K V indexType basis R f)).val *ᵥ
        (generalLinearScalarBasis K V indexType otherBasis R).repr x =
      (generalLinearScalarBasis K V indexType otherBasis R).repr (f.val x) := by
  rw [generalLinearModuleChangeBasis_apply]
  exact generalLinearModuleMatrixEquiv_action K V indexType otherBasis R f x

section FieldComparison

variable (F : Type u) [Field F] (W : Type u) [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] (coordinates : Module.Basis indexType F W)

omit [FiniteDimensional F W] in
/-- In the field case the GL entries are the accepted additive End coordinates. -/
theorem generalLinearModuleMatrixEquiv_endMatrixLinearEquiv
    (R : Type u) [CommRing R] [Algebra F R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor F W R)) :
    (generalLinearModuleMatrixEquiv F W indexType coordinates R f).val =
      endMatrixLinearEquiv F W indexType coordinates R f.val := rfl

end FieldComparison

end AlgebraicGeometry

#lint
