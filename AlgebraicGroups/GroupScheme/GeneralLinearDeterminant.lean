/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.Multiplicative

/-!
# The determinant character of the finite general linear group scheme

For any commutative ring and finite matrix index type, determinant induces a morphism
from the general linear group scheme to the multiplicative group scheme. The
coordinate map sends the Laurent generator to the determinant of the universal
matrix; its point map is the unit-valued determinant on every coefficient algebra.

The coordinate map goes from the Laurent algebra to the localized GL algebra;
`hopfSpec` reverses this direction. Group-likeness is an identity in the
coordinate tensor algebra, obtained from the universal matrix multiplication,
not from values at rational points. Empty index types and zero base rings are included.

## References

* J. S. Milne, *Algebraic Groups*, §2.8 (finite-matrix GL coordinates over a field).
* J. S. Milne, *Basic Theory of Affine Group Schemes*, VII §4, Proposition 4.1
  (generic field-base kernel quotient) and Example 4.3 (the determinant
  morphism and its special-linear kernel).
* The Stacks Project, Example 39.5.5 (tag 022X), gives the determinant
  morphism of positive-size general linear group schemes over any base.
* Mathlib, `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` (`det`, `map_det`),
  `RingTheory/Bialgebra/MonoidAlgebra.lean` and
  `RingTheory/HopfAlgebra/MonoidAlgebra.lean` (the Laurent Hopf coordinates),
  and `AlgebraicGeometry/Group/Affine.lean` (`hopfSpec`). The local finite GL
  and multiplicative-group coordinate/point APIs supply the remaining readbacks.
-/

public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant of the universal invertible matrix as a unit. -/
def generalLinearDeterminantUnit : (CoordinateRing K n)ˣ :=
  Matrix.GeneralLinearGroup.det (universal K n)

/-- The coordinate-algebra map underlying the determinant character. -/
@[expose] def generalLinearDeterminantCoordinateMap :
    multiplicativeGroupCoordinateRing K →ₐ[K] CoordinateRing K n :=
  (multiplicativeGroupMulEquivAlgHom K (CoordinateRing K n)
    (generalLinearDeterminantUnit K n)).ofConv

@[simp] theorem generalLinearDeterminantCoordinateMap_coordinate :
    generalLinearDeterminantCoordinateMap K n (multiplicativeGroupCoordinate K) =
      (matrix K n).det := by
  rw [generalLinearDeterminantCoordinateMap,
    multiplicativeGroupMulEquivAlgHom_coordinate]
  rfl

@[simp] theorem generalLinearDeterminantCoordinateMap_inverse :
    generalLinearDeterminantCoordinateMap K n (LaurentPolynomial.T (-1)) =
      detInverse K n := by
  have hinv : (multiplicativeGroupCoordinate K) * LaurentPolynomial.T (-1) = 1 := by
    change (LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) :
      LaurentPolynomial K) = 1
    rw [← LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  have h := congrArg (generalLinearDeterminantCoordinateMap K n) hinv
  rw [map_mul, map_one, generalLinearDeterminantCoordinateMap_coordinate] at h
  exact (isUnit_matrix_det K n).mul_left_cancel
    (h.trans (det_mul_detInverse K n).symm)

/-- The universal determinant is group-like for the GL coalgebra. This follows
from `Matrix.det_mul` and determinant compatibility with algebra maps, applied
to the comultiplication of the universal matrix in the tensor coordinate ring. -/
theorem generalLinearDeterminant_comul :
    Coalgebra.comul (R := K) (matrix K n).det =
      (matrix K n).det ⊗ₜ[K] (matrix K n).det := by
  change comul K n (matrix K n).det = _
  rw [comul, evaluate_det]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
  change ((Algebra.TensorProduct.includeLeft (R := K)
      (S := K) (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom.mapMatrix
      (matrix K n)).det *
    ((Algebra.TensorProduct.includeRight (R := K)
      (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom.mapMatrix
      (matrix K n)).det = _
  rw [← RingHom.map_det (Algebra.TensorProduct.includeLeft (R := K)
    (S := K) (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom (matrix K n),
    ← RingHom.map_det (Algebra.TensorProduct.includeRight (R := K)
      (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom (matrix K n)]
  change ((matrix K n).det ⊗ₜ[K] (1 : CoordinateRing K n)) *
    ((1 : CoordinateRing K n) ⊗ₜ[K] (matrix K n).det) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

theorem generalLinearDeterminant_counit :
    Coalgebra.counit (R := K) (matrix K n).det = 1 := by
  change counit K n (matrix K n).det = 1
  rw [counit, evaluate_det]
  simp

/-- The actual GL antipode takes the universal determinant to its inverse coordinate. -/
theorem generalLinearDeterminant_antipode :
    HopfAlgebra.antipode K (matrix K n).det = detInverse K n := by
  change antipode K n (matrix K n).det = _
  rw [antipode, evaluate_det]
  have h := congrArg (fun unit : (CoordinateRing K n)ˣ ↦
    (unit : CoordinateRing K n))
    (map_inv (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup n (CoordinateRing K n) →*
        (CoordinateRing K n)ˣ) (universal K n))
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_inv,
    detInverse_eq_detUnitInv] using h

private theorem generalLinearDeterminant_coordinate_ext {R : Type u} [CommRing R]
    [Algebra K R] {f g : multiplicativeGroupCoordinateRing K →ₐ[K] R}
    (h : f (multiplicativeGroupCoordinate K) = g (multiplicativeGroupCoordinate K)) :
    f = g := by
  let e := multiplicativeGroupMulEquivAlgHom K R
  let uf := e.symm (WithConv.toConv f)
  let ug := e.symm (WithConv.toConv g)
  have hu : uf = ug := by
    apply Units.ext
    rw [← multiplicativeGroupMulEquivAlgHom_coordinate K R uf,
      ← multiplicativeGroupMulEquivAlgHom_coordinate K R ug]
    simpa [uf, ug, e] using h
  have := congrArg (fun v : Rˣ ↦ (e v).ofConv) hu
  simpa [uf, ug, e] using this

/-- The determinant coordinate map preserves counit and comultiplication. -/
@[expose] def generalLinearDeterminantBialgHom :
    multiplicativeGroupCoordinateRing K →ₐc[K] CoordinateRing K n :=
  BialgHom.ofAlgHom (generalLinearDeterminantCoordinateMap K n)
    (by
      apply generalLinearDeterminant_coordinate_ext K
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
        generalLinearDeterminantCoordinateMap_coordinate,
        generalLinearDeterminant_counit, multiplicativeGroupCoordinate_counit])
    (by
      apply generalLinearDeterminant_coordinate_ext K
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        multiplicativeGroupCoordinate_comul,
        Algebra.TensorProduct.map_tmul,
        generalLinearDeterminantCoordinateMap_coordinate,
        generalLinearDeterminant_comul])

/-- The determinant character as a group-scheme morphism over `Spec K`.
Milne, *Basic Theory of Affine Group Schemes*, VII §4, Example 4.3,
gives the field-base morphism; the Stacks Project, Example 39.5.5 (tag 022X),
gives the positive-size arbitrary-base morphism. Here the Laurent-coordinate
bialgebra map and Mathlib's `hopfSpec` include the empty-index case. -/
@[expose] def generalLinearDeterminantSchemeHom :
    generalLinearGroupScheme K n ⟶ multiplicativeGroupScheme K :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom
      (generalLinearDeterminantBialgHom K n)))

/-- The underlying affine map reverses the determinant coordinate map. -/
@[simp] theorem generalLinearDeterminantSchemeHom_left :
    (generalLinearDeterminantSchemeHom K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantCoordinateMap K n).toRingHom) := rfl

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The determinant character sends every affine GL point to its unit-valued
determinant; compare the field case in Milne, *Basic Theory of Affine Group
Schemes*, VII §4, Example 4.3, and the arbitrary-base character in the Stacks
Project, Example 39.5.5 (tag 022X). -/
theorem generalLinearDeterminant_point (g : Matrix.GeneralLinearGroup n R) :
    generalLinearGroupMulEquivPoints K n R g ≫ (generalLinearDeterminantSchemeHom K n).hom.hom =
      multiplicativeGroupMulEquivPoints K R (Matrix.GeneralLinearGroup.det g) := by
  have h : (generalLinearGroupMulEquivAlgHom K n R g).ofConv.comp
      (generalLinearDeterminantCoordinateMap K n) =
      (multiplicativeGroupMulEquivAlgHom K R (Matrix.GeneralLinearGroup.det g)).ofConv := by
    apply generalLinearDeterminant_coordinate_ext K
    rw [AlgHom.comp_apply, generalLinearDeterminantCoordinateMap_coordinate,
      multiplicativeGroupMulEquivAlgHom_coordinate]
    exact evaluate_det g
  apply Over.OverMorphism.ext
  rw [Over.comp_left, generalLinearGroupMulEquivPoints_apply_left,
    multiplicativeGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom
    (generalLinearGroupMulEquivAlgHom K n R g).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantCoordinateMap K n).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (multiplicativeGroupMulEquivAlgHom K R
          (Matrix.GeneralLinearGroup.det g)).ofConv.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun hom : multiplicativeGroupCoordinateRing K →ₐ[K] R ↦
    Spec.map (CommRingCat.ofHom hom.toRingHom)) h

/-- The unit-valued determinant of a GL point commutes with every coefficient map. -/
theorem generalLinearDeterminant_natural {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (g : Matrix.GeneralLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Units.map f (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det f.toRingHom g

/-- The determinant character on native matrix groups is natural in the coefficient algebra. -/
def generalLinearDeterminantFunctorHom :
    generalLinearGroupFunctor K n ⟶ multiplicativeGroupFunctor K where
  app R := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact Matrix.GeneralLinearGroup.map_det f.hom.toRingHom g

end AlgebraicGeometry

#lint
