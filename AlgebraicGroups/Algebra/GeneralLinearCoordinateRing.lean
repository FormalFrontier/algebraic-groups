/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coordinates of the finite general linear group

The generic matrix over the multivariate polynomial algebra becomes invertible
after localizing at its determinant. The construction works over any commutative
ring, including the zero ring, and for an empty finite index type. Algebra maps
from this localization evaluate at invertible matrices over any commutative
algebra. The ordered matrix product gives the coproduct; commutativity of the
coordinate algebra does not make the general linear group commutative.
The localization is also finitely presented, stronger than the finite-type
property needed for the group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8, p. 41: determinant
  localization/quotient, universal invertible matrix, and coproduct equation (8)
  over a field.
* Mathlib, `LinearAlgebra/Matrix/MvPolynomial`,
  `LinearAlgebra/Matrix/GeneralLinearGroup/Defs`, and
  `LinearAlgebra/Matrix/NonsingularInverse`: generic matrices, matrix units,
  and the adjugate formula.
* Mathlib, `RingTheory/Localization/Basic`,
  `RingTheory/Localization/Away/Basic`, and
  `RingTheory/Localization/Away/AdjoinRoot`: algebra-map extensionality,
  localization evaluation, and its quotient presentation.
* Mathlib, `Algebra/MvPolynomial/Equiv`, `RingTheory/Bialgebra/Basic`, and
  `RingTheory/HopfAlgebra/Basic`: extra polynomial coordinates and the
  algebraic structures used for the group laws.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The polynomial ring in the entries of a square matrix. -/
abbrev PolynomialRing := MvPolynomial (n × n) K

/-- The determinant of the generic square matrix. -/
def determinant : PolynomialRing K n := (Matrix.mvPolynomialX n n K).det

/-- The determinant localization representing invertible matrices over
commutative algebras; see Milne, *Algebraic Groups*, item 2.8. -/
abbrev CoordinateRing := Localization.Away (determinant K n)

instance finiteType : Algebra.FiniteType K (CoordinateRing K n) := inferInstance

instance finitePresentation : Algebra.FinitePresentation K (CoordinateRing K n) :=
  inferInstance

/-- The universal matrix, with entries in the determinant localization. -/
def matrix : Matrix n n (CoordinateRing K n) :=
  (Matrix.mvPolynomialX n n K).map (algebraMap (PolynomialRing K n) (CoordinateRing K n))

@[simp] theorem matrix_apply (i j : n) :
    matrix K n i j = algebraMap (PolynomialRing K n) (CoordinateRing K n)
      (MvPolynomial.X (i, j)) := rfl

@[simp] theorem matrix_det :
    (matrix K n).det = algebraMap (PolynomialRing K n) (CoordinateRing K n)
      (determinant K n) := by
  exact (RingHom.map_det
    (algebraMap (PolynomialRing K n) (CoordinateRing K n))
    (Matrix.mvPolynomialX n n K)).symm

theorem isUnit_matrix_det : IsUnit (matrix K n).det := by
  rw [matrix_det]
  exact IsLocalization.Away.algebraMap_isUnit (determinant K n)

/-- The universal invertible matrix as a matrix general linear group element. -/
def universal : Matrix.GeneralLinearGroup n (CoordinateRing K n) :=
  Matrix.GeneralLinearGroup.mk'' (matrix K n) (isUnit_matrix_det K n)

@[simp] theorem universal_apply (i j : n) :
    universal K n i j = matrix K n i j := rfl

@[simp] theorem universal_det :
    ((universal K n : Matrix.GeneralLinearGroup n (CoordinateRing K n)) :
      Matrix n n (CoordinateRing K n)).det = (matrix K n).det := rfl

/-- The inverse-determinant coordinate. -/
def detInverse : CoordinateRing K n :=
  IsLocalization.Away.invSelf (determinant K n)

theorem det_mul_detInverse :
    (matrix K n).det * detInverse K n = 1 := by
  rw [matrix_det]
  exact IsLocalization.Away.mul_invSelf (determinant K n)

/-- The quotient presentation by `det(X) * T - 1` in Milne, *Algebraic Groups*,
item 2.8, via Mathlib's `Localization.awayEquivAdjoin`. -/
def quotientEquiv : CoordinateRing K n ≃ₐ[K]
    AdjoinRoot (Polynomial.C (determinant K n) * Polynomial.X - 1) :=
  (Localization.awayEquivAdjoin (determinant K n)).restrictScalars K

/-- Adding a single variable to the matrix-entry polynomial ring is the
ordinary polynomial algebra over that entry algebra. -/
def extraVariableEquiv :
    MvPolynomial (Option (n × n)) K ≃ₐ[K] Polynomial (PolynomialRing K n) :=
  MvPolynomial.optionEquivLeft K (n × n)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem extraVariableEquiv_entry (i j : n) :
    extraVariableEquiv K n (MvPolynomial.X (some (i, j))) =
      Polynomial.C (MvPolynomial.X (i, j)) :=
  MvPolynomial.optionEquivLeft_X_some K (n × n) (i, j)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem extraVariableEquiv_inverseVariable :
    extraVariableEquiv K n (MvPolynomial.X none) = Polynomial.X :=
  MvPolynomial.optionEquivLeft_X_none K (n × n)

theorem quotientEquiv_matrix (i j : n) :
    quotientEquiv K n (matrix K n i j) =
      AdjoinRoot.of _ (MvPolynomial.X (i, j)) := by
  exact (Localization.awayEquivAdjoin (determinant K n)).commutes _

@[simp] theorem quotientEquiv_detInverse :
    quotientEquiv K n (detInverse K n) =
      AdjoinRoot.root (Polynomial.C (determinant K n) * Polynomial.X - 1) := by
  have h : IsUnit (AdjoinRoot.of
      (Polynomial.C (determinant K n) * Polynomial.X - 1) (determinant K n)) := by
    convert IsUnit.map (quotientEquiv K n).toRingHom
      (IsLocalization.Away.algebraMap_isUnit (determinant K n)) using 1
    exact ((Localization.awayEquivAdjoin (determinant K n)).commutes
      (determinant K n)).symm
  have hc : (quotientEquiv K n)
      (algebraMap (PolynomialRing K n) (CoordinateRing K n) (determinant K n)) =
      AdjoinRoot.of _ (determinant K n) :=
    (Localization.awayEquivAdjoin (determinant K n)).commutes _
  have hl : AdjoinRoot.of _ (determinant K n) *
      (quotientEquiv K n) (detInverse K n) = 1 := by
    rw [← hc, ← map_mul]
    simpa only [detInverse, map_one] using congrArg (quotientEquiv K n)
      (IsLocalization.Away.mul_invSelf (determinant K n))
  exact h.mul_left_cancel (hl.trans (AdjoinRoot.root_isInv (determinant K n)).symm)

@[simp] theorem quotientEquiv_symm_entry (i j : n) :
    (quotientEquiv K n).symm (AdjoinRoot.of _ (MvPolynomial.X (i, j))) =
      matrix K n i j := by
  rw [← quotientEquiv_matrix K n i j, AlgEquiv.symm_apply_apply]

@[simp] theorem quotientEquiv_symm_inverseVariable :
    (quotientEquiv K n).symm
      (AdjoinRoot.root (Polynomial.C (determinant K n) * Polynomial.X - 1)) =
        detInverse K n := by
  rw [← quotientEquiv_detInverse K n, AlgEquiv.symm_apply_apply]

variable {K n}

/-- An algebra map out of the coordinate ring is determined by the entries
of the universal matrix, without any nontriviality assumption. -/
theorem hom_ext {R : Type u} [CommRing R] [Algebra K R]
    {f g : CoordinateRing K n →ₐ[K] R}
    (h : ∀ i j, f (matrix K n i j) = g (matrix K n i j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (determinant K n))
  apply MvPolynomial.algHom_ext
  intro ⟨i, j⟩
  exact h i j

/-- Evaluation of coordinates at an invertible matrix. -/
def evaluate {R : Type u} [CommRing R] [Algebra K R]
    (g : Matrix.GeneralLinearGroup n R) : CoordinateRing K n →ₐ[K] R :=
  IsLocalization.Away.liftAlgHom (determinant K n)
    (f := MvPolynomial.aeval fun ij : n × n ↦ (g : Matrix n n R) ij.1 ij.2)
    (by
      change IsUnit ((MvPolynomial.aeval fun ij : n × n ↦ (g : Matrix n n R) ij.1 ij.2)
        (determinant K n))
      rw [determinant, AlgHom.map_det]
      simpa only [Matrix.mvPolynomialX_mapMatrix_aeval,
        Matrix.GeneralLinearGroup.val_det_apply] using
        (Matrix.GeneralLinearGroup.det g).isUnit)

theorem evaluate_matrix {R : Type u} [CommRing R] [Algebra K R]
    (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    evaluate g (matrix K n i j) = g i j := by
  change (IsLocalization.Away.liftAlgHom (determinant K n)
    (f := MvPolynomial.aeval fun ij : n × n ↦ (g : Matrix n n R) ij.1 ij.2) _)
    (algebraMap (PolynomialRing K n) (CoordinateRing K n) (MvPolynomial.X (i, j))) = _
  simp [IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq]

@[simp] theorem evaluate_detInverse {R : Type u} [CommRing R] [Algebra K R]
    (g : Matrix.GeneralLinearGroup n R) :
    evaluate g (detInverse K n) = ↑(Matrix.GeneralLinearGroup.det g)⁻¹ := by
  have e : evaluate g (matrix K n).det = (g : Matrix n n R).det := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    exact evaluate_matrix g i j
  have h := congrArg (evaluate g) (det_mul_detInverse K n)
  rw [map_mul, map_one, e] at h
  have h' : (g : Matrix n n R).det * ↑(Matrix.GeneralLinearGroup.det g)⁻¹ = 1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_inv] using
      (Matrix.GeneralLinearGroup.det g).mul_inv
  exact (Matrix.GeneralLinearGroup.det g).isUnit.mul_left_cancel
    (h.trans h'.symm)

theorem evaluate_det {R : Type u} [CommRing R] [Algebra K R]
    (g : Matrix.GeneralLinearGroup n R) :
    evaluate (K := K) g (matrix K n).det = (g : Matrix n n R).det := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  exact evaluate_matrix g i j

/-- Evaluation of the universal matrix gives an invertible matrix. -/
def toGL {R : Type u} [CommRing R] [Algebra K R]
    (f : CoordinateRing K n →ₐ[K] R) : Matrix.GeneralLinearGroup n R :=
  Matrix.GeneralLinearGroup.map f.toRingHom (universal K n)

@[simp] theorem toGL_apply {R : Type u} [CommRing R] [Algebra K R]
    (f : CoordinateRing K n →ₐ[K] R) (i j : n) :
    toGL f i j = f (matrix K n i j) := rfl

/-- The universal invertible-matrix property of the determinant localization
(Milne, *Algebraic Groups*, item 2.8), for every commutative coefficient algebra. -/
def homEquiv {R : Type u} [CommRing R] [Algebra K R] :
    (CoordinateRing K n →ₐ[K] R) ≃ Matrix.GeneralLinearGroup n R where
  toFun := toGL
  invFun := evaluate
  left_inv f := by
    apply hom_ext
    intro i j
    rw [evaluate_matrix, toGL_apply]
  right_inv g := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact evaluate_matrix g i j

@[simp] theorem toGL_evaluate {R : Type u} [CommRing R] [Algebra K R]
    (g : Matrix.GeneralLinearGroup n R) : toGL (evaluate (K := K) g) = g :=
  (homEquiv (K := K) (n := n)).apply_symm_apply g

@[simp] theorem evaluate_toGL {R : Type u} [CommRing R] [Algebra K R]
    (f : CoordinateRing K n →ₐ[K] R) : evaluate (toGL f) = f :=
  (homEquiv (K := K) (n := n)).symm_apply_apply f

theorem toGL_comp {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (f : CoordinateRing K n →ₐ[K] R)
    (g : R →ₐ[K] S) :
    toGL (g.comp f) = Matrix.GeneralLinearGroup.map g.toRingHom (toGL f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Evaluation commutes with arbitrary homomorphisms of test algebras. -/
theorem evaluate_natural {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (g : R →ₐ[K] S)
    (x : Matrix.GeneralLinearGroup n R) :
    evaluate (K := K) (Matrix.GeneralLinearGroup.map g.toRingHom x) =
      g.comp (evaluate (K := K) x) := by
  apply hom_ext
  intro i j
  rw [evaluate_matrix, AlgHom.comp_apply, evaluate_matrix]
  rfl

variable (K n)

/-- The matrix of generators embedded in the left tensor factor. -/
def tensorLeft : Matrix.GeneralLinearGroup n
    (CoordinateRing K n ⊗[K] CoordinateRing K n) :=
  Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeft (R := K) (S := K)
      (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom
    (universal K n)

/-- The matrix of generators embedded in the right tensor factor. -/
def tensorRight : Matrix.GeneralLinearGroup n
    (CoordinateRing K n ⊗[K] CoordinateRing K n) :=
  Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeRight (R := K)
      (A := CoordinateRing K n) (B := CoordinateRing K n)).toRingHom
    (universal K n)

/-- Comultiplication is evaluation at the product of the two universal matrices. -/
def comul : CoordinateRing K n →ₐ[K]
    (CoordinateRing K n ⊗[K] CoordinateRing K n) :=
  evaluate (K := K) (tensorLeft K n * tensorRight K n)

/-- The identity matrix evaluates the counit. -/
def counit : CoordinateRing K n →ₐ[K] K := evaluate (K := K) 1

/-- Matrix inversion evaluates the antipode. -/
def antipode : CoordinateRing K n →ₐ[K] CoordinateRing K n :=
  evaluate (K := K) (universal K n)⁻¹

/-- The ordered coproduct on matrix entries: Milne, *Algebraic Groups*,
item 2.8, equation (8). -/
theorem comul_matrix (i j : n) :
    comul K n (matrix K n i j) =
      ∑ index : n, matrix K n i index ⊗ₜ[K] matrix K n index j := by
  rw [comul, evaluate_matrix]
  simp [Matrix.mul_apply, tensorLeft, tensorRight,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem counit_matrix (i j : n) :
    counit K n (matrix K n i j) = (1 : Matrix n n K) i j := by
  rw [counit, evaluate_matrix]
  rfl

theorem antipode_matrix (i j : n) :
    antipode K n (matrix K n i j) =
      ((universal K n)⁻¹ : Matrix.GeneralLinearGroup n (CoordinateRing K n)) i j := by
  exact evaluate_matrix _ _ _

theorem detInverse_eq_detUnitInv :
    detInverse K n = ↑(Matrix.GeneralLinearGroup.det (universal K n))⁻¹ := by
  apply Units.eq_inv_of_mul_eq_one_left
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, universal_det] using
    det_mul_detInverse K n

/-- The inverse matrix is the adjugate multiplied by the inverse-determinant
coordinate, over arbitrary commutative bases. -/
theorem universal_inv_apply (i j : n) :
    (universal K n)⁻¹ i j = detInverse K n * (matrix K n).adjugate i j := by
  change ((matrix K n)⁻¹) i j = _
  have h := congrArg
    (fun M : Matrix n n (CoordinateRing K n) ↦ M i j)
    (Matrix.nonsing_inv_apply (matrix K n) (isUnit_matrix_det K n))
  rw [Matrix.smul_apply, smul_eq_mul] at h
  have hd : (↑(isUnit_matrix_det K n).unit⁻¹ : CoordinateRing K n) =
      detInverse K n := by
    apply Units.inv_eq_of_mul_eq_one_right
    simpa only [IsUnit.unit_spec] using det_mul_detInverse K n
  rwa [hd] at h

@[simp] theorem comul_detInverse :
    comul K n (detInverse K n) =
      detInverse K n ⊗ₜ[K] detInverse K n := by
  rw [comul, evaluate_detInverse]
  simp [detInverse_eq_detUnitInv, tensorLeft, tensorRight,
    Matrix.GeneralLinearGroup.map_det, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

@[simp] theorem counit_detInverse : counit K n (detInverse K n) = 1 := by
  rw [counit, evaluate_detInverse]
  simp

@[simp] theorem antipode_detInverse :
    antipode K n (detInverse K n) = (matrix K n).det := by
  rw [antipode, evaluate_detInverse]
  simp only [map_inv, inv_inv, Matrix.GeneralLinearGroup.val_det_apply, universal_det]

/-- The coordinate ring carries the multiplication/identity coalgebra structure. -/
instance bialgebra : Bialgebra K (CoordinateRing K n) :=
  Bialgebra.ofAlgHom (comul K n) (counit K n)
    (by
      apply hom_ext (K := K) (n := n)
        (R := CoordinateRing K n ⊗[K]
          (CoordinateRing K n ⊗[K] CoordinateRing K n))
      intro i j
      simp only [AlgHom.comp_apply]
      rw [comul_matrix]
      simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.assoc_tmul, comul_matrix,
        TensorProduct.sum_tmul, TensorProduct.tmul_sum]
      rw [Finset.sum_comm])
    (by
      apply hom_ext (K := K) (n := n)
      intro i j
      change (Algebra.TensorProduct.map (counit K n) (AlgHom.id K _))
        ((comul K n) (matrix K n i j)) = (Algebra.TensorProduct.lid K _).symm
          (matrix K n i j)
      rw [comul_matrix]
      simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        counit_matrix, Matrix.one_apply]
      simp [TensorProduct.ite_tmul, Algebra.TensorProduct.lid_symm_apply])
    (by
      apply hom_ext (K := K) (n := n)
      intro i j
      change (Algebra.TensorProduct.map (AlgHom.id K _) (counit K n))
        ((comul K n) (matrix K n i j)) = (Algebra.TensorProduct.rid K K _).symm
          (matrix K n i j)
      rw [comul_matrix]
      simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        counit_matrix, Matrix.one_apply]
      simp [TensorProduct.tmul_ite, Algebra.TensorProduct.rid_symm_apply])

theorem comulAlgHom_eq :
    Bialgebra.comulAlgHom K (CoordinateRing K n) = comul K n := rfl

theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom K (CoordinateRing K n) = counit K n := rfl

/-- The determinant-localized coordinate algebra has the Hopf structure of
the finite general linear group, with antipode induced by matrix inversion. -/
instance hopfAlgebra : HopfAlgebra K (CoordinateRing K n) :=
  HopfAlgebra.ofAlgHom (antipode K n)
    (by
      rw [comulAlgHom_eq K n, counitAlgHom_eq K n]
      apply hom_ext (K := K) (n := n)
      intro i j
      simp only [AlgHom.comp_apply]
      rw [comul_matrix]
      simp only [map_sum]
      show (∑ index : n,
          (Algebra.TensorProduct.lift (antipode K n) (AlgHom.id K _)
            (fun _ _ ↦ Commute.all _ _))
            (matrix K n i index ⊗ₜ[K] matrix K n index j)) =
          (algebraMap K (CoordinateRing K n)) ((counit K n) (matrix K n i j))
      calc
        _ = ∑ index : n, (antipode K n) (matrix K n i index) *
            matrix K n index j := by
          apply Finset.sum_congr rfl
          intro index _
          exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
        _ = (algebraMap K (CoordinateRing K n)) ((counit K n) (matrix K n i j)) := by
          rw [counit_matrix, Matrix.one_apply]
          simp only [antipode_matrix]
          have h := congrArg
            (fun x : Matrix.GeneralLinearGroup n (CoordinateRing K n) ↦
              (x : Matrix n n (CoordinateRing K n)) i j)
            (inv_mul_cancel (universal K n))
          by_cases hij : i = j
          · simpa only [hij, ite_true, map_one, Matrix.GeneralLinearGroup.coe_mul,
              Matrix.GeneralLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply,
              Matrix.GeneralLinearGroup.coe_inv, universal_apply] using h
          · simpa only [hij, ite_false, map_zero, Matrix.GeneralLinearGroup.coe_mul,
              Matrix.GeneralLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply,
              Matrix.GeneralLinearGroup.coe_inv, universal_apply] using h)
    (by
      rw [comulAlgHom_eq K n, counitAlgHom_eq K n]
      apply hom_ext (K := K) (n := n)
      intro i j
      simp only [AlgHom.comp_apply]
      rw [comul_matrix]
      simp only [map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
      rw [counit_matrix, Matrix.one_apply]
      simp only [antipode_matrix]
      have h := congrArg
        (fun x : Matrix.GeneralLinearGroup n (CoordinateRing K n) ↦
          (x : Matrix n n (CoordinateRing K n)) i j)
        (mul_inv_cancel (universal K n))
      by_cases hij : i = j
      · simpa only [hij, ite_true, map_one, Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply,
          Matrix.GeneralLinearGroup.coe_inv, universal_apply] using h
      · simpa only [hij, ite_false, map_zero, Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply,
          Matrix.GeneralLinearGroup.coe_inv, universal_apply] using h)

theorem native_comul_matrix (i j : n) :
    Coalgebra.comul (R := K) (matrix K n i j) =
      ∑ index : n, matrix K n i index ⊗ₜ[K] matrix K n index j :=
  comul_matrix K n i j

theorem native_counit_matrix (i j : n) :
    Coalgebra.counit (R := K) (matrix K n i j) = (1 : Matrix n n K) i j :=
  counit_matrix K n i j

theorem native_antipode_matrix (i j : n) :
    HopfAlgebra.antipode K (matrix K n i j) = (universal K n)⁻¹ i j :=
  antipode_matrix K n i j

theorem native_comul_detInverse :
    Coalgebra.comul (R := K) (detInverse K n) =
      detInverse K n ⊗ₜ[K] detInverse K n := comul_detInverse K n

theorem native_counit_detInverse :
    Coalgebra.counit (R := K) (detInverse K n) = 1 := counit_detInverse K n

theorem native_antipode_detInverse :
    HopfAlgebra.antipode K (detInverse K n) = (matrix K n).det :=
  antipode_detInverse K n

end GeneralLinearCoordinateRing

#lint
