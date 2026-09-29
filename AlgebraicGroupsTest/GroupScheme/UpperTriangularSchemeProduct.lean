/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
public import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

namespace UpperTriangularSchemeProductClient

variable (K : Type) [CommRing K] (n : Type) [Fintype n] [LinearOrder n]

private theorem arbitrary_test_twisted_law {test : Over (Spec (.of K))}
    (unit unit' : test ⟶ unitriangularGroupUnderlyingScheme K n)
    (diag diag' : test ⟶ diagonalGroupUnderlyingScheme K n) :
    lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
        (diag * diag') ≫ (upperTriangularUFirstIso K n).hom =
      (lift unit diag ≫ (upperTriangularUFirstIso K n).hom) *
        (lift unit' diag' ≫ (upperTriangularUFirstIso K n).hom) :=
  upperTriangularUFirstIso_mul_lift K n unit unit' diag diag'

private theorem arbitrary_test_diagram :
    upperTriangularUFirstTwistedMul K n ≫ (upperTriangularUFirstIso K n).hom =
      ((upperTriangularUFirstIso K n).hom ⊗ₘ
        (upperTriangularUFirstIso K n).hom) ≫
        μ[upperTriangularGroupUnderlyingScheme K n] :=
  upperTriangularUFirstTwistedMul_comp_hom K n

private theorem arbitrary_test_normalization :
    ((upperTriangularUFirstIso K n).inv ≫
      fst (unitriangularGroupUnderlyingScheme K n) (diagonalGroupUnderlyingScheme K n)) ≫
        (unitriangularToUpperTriangular K n).hom.hom =
      𝟙 (upperTriangularGroupUnderlyingScheme K n) *
        ((upperTriangularDiagonalProjection K n).hom.hom ≫
          (upperTriangularDiagonalSection K n).hom.hom)⁻¹ :=
  upperTriangularUFirstIso_inv_fst_comp_inclusion K n

variable (R : Type) [CommRing R] [Algebra K R]

private theorem fin0_inverse (matrix : Matrix.UpperTriangularGroup (Fin 0) R) :
    (upperTriangularGroupMulEquivPoints K (Fin 0) R matrix ≫
      (upperTriangularUFirstIso K (Fin 0)).inv) ≫
        fst (unitriangularGroupUnderlyingScheme K (Fin 0))
          (diagonalGroupUnderlyingScheme K (Fin 0)) =
      unitriangularGroupMulEquivPoints K (Fin 0) R
        (Matrix.UpperTriangularGroup.unipotentPart matrix) :=
  upperTriangularUFirstIso_inv_fst_point K (Fin 0) R matrix

private theorem fin0_unit (unit : Matrix.UnitriangularGroup (Fin 0) R) : unit = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin1_inverse (matrix : Matrix.UpperTriangularGroup (Fin 1) R) :
    (upperTriangularGroupMulEquivPoints K (Fin 1) R matrix ≫
      (upperTriangularUFirstIso K (Fin 1)).inv) ≫
        snd (unitriangularGroupUnderlyingScheme K (Fin 1))
          (diagonalGroupUnderlyingScheme K (Fin 1)) =
      diagonalGroupMulEquivPoints K (Fin 1) R
        (Matrix.UpperTriangularGroup.diagonal matrix) :=
  upperTriangularUFirstIso_inv_snd_point K (Fin 1) R matrix

private theorem fin1_unit (unit : Matrix.UnitriangularGroup (Fin 1) R) : unit = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  have hrow : row = 0 := Subsingleton.elim _ _
  have hcol : col = 0 := Subsingleton.elim _ _
  subst row
  subst col
  simpa using unit.2.2 0

private theorem zero_ring_inverse (matrix : Matrix.UpperTriangularGroup (Fin 2) (ZMod 1)) :
    upperTriangularGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1) matrix ≫
      (upperTriangularUFirstIso (ZMod 1) (Fin 2)).inv =
        lift (unitriangularGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1)
          (Matrix.UpperTriangularGroup.unipotentPart matrix))
          (diagonalGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1)
            (Matrix.UpperTriangularGroup.diagonal matrix)) :=
  upperTriangularUFirstIso_inv_point (ZMod 1) (Fin 2) (ZMod 1) matrix

private def shear (a : R) : Matrix.UnitriangularGroup (Fin 2) R :=
  Matrix.UnitriangularGroup.elementary 2 R 0 1 (by decide) a

private theorem shear_entry (a : R) : (shear R a).1 0 1 = a := by
  simp [shear, Matrix.UnitriangularGroup.elementary_coe, Matrix.add_apply]

private def independentDiagonal (first second : Rˣ) :
    Matrix.DiagonalGroup (Fin 2) R :=
  (Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
    (Fin 2 → Rˣ)).symm (fun index => if index = 0 then first else second)

private theorem independentDiagonal_first (first second : Rˣ) :
    (independentDiagonal R first second).1 0 0 = first := by
  simp [independentDiagonal, Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private theorem independentDiagonal_second (first second : Rˣ) :
    (independentDiagonal R first second).1 1 1 = second := by
  simp [independentDiagonal, Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private theorem shear_twist_entry (first second : Rˣ) (a : R) :
    (Matrix.UpperTriangularGroup.diagonalAction
      (independentDiagonal R first second) (shear R a)).1 0 1 =
        (first : R) * a * (((second⁻¹ : Rˣ) : R)) := by
  have hfirst : Matrix.DiagonalGroup.unitsEquiv
      (independentDiagonal R first second) 0 = first := by
    apply Units.ext
    rw [Matrix.DiagonalGroup.unitsEquiv_apply_val,
      independentDiagonal_first]
  have hsecond : Matrix.DiagonalGroup.unitsEquiv
      (independentDiagonal R first second) 1 = second := by
    apply Units.ext
    rw [Matrix.DiagonalGroup.unitsEquiv_apply_val,
      independentDiagonal_second]
  rw [Matrix.UpperTriangularGroup.diagonalAction_apply,
    shear_entry, hfirst, hsecond]

private theorem fin2_forward (first second : Rˣ) (a : R) :
    lift (unitriangularGroupMulEquivPoints K (Fin 2) R (shear R a))
        (diagonalGroupMulEquivPoints K (Fin 2) R
          (independentDiagonal R first second)) ≫
          (upperTriangularUFirstIso K (Fin 2)).hom =
      upperTriangularGroupMulEquivPoints K (Fin 2) R
        (Matrix.UpperTriangularGroup.semidirEquiv
          (⟨shear R a, independentDiagonal R first second⟩ :
            Matrix.UnitriangularGroup (Fin 2) R ⋊[Matrix.UpperTriangularGroup.diagonalAction]
              Matrix.DiagonalGroup (Fin 2) R)) :=
  upperTriangularUFirstIso_point K (Fin 2) R _ _

private theorem fin2_action_bridge (first second : Rˣ) (a : R) :
    lift (diagonalGroupMulEquivPoints K (Fin 2) R
        (independentDiagonal R first second))
        (unitriangularGroupMulEquivPoints K (Fin 2) R (shear R a)) ≫
          upperTriangularDiagonalConj K (Fin 2) =
      unitriangularGroupMulEquivPoints K (Fin 2) R
        (Matrix.UpperTriangularGroup.diagonalAction
          (independentDiagonal R first second) (shear R a)) :=
  upperTriangularDiagonalConj_point K (Fin 2) R _ _

private theorem sign_twist_entry :
    (Matrix.UpperTriangularGroup.diagonalAction
      (independentDiagonal ℤ (-1) 1) (shear ℤ 1)).1 0 1 = -1 := by
  rw [shear_twist_entry]
  norm_num

private theorem sign_twist_not_direct :
    Matrix.UpperTriangularGroup.diagonalAction
        (independentDiagonal ℤ (-1) 1) (shear ℤ 1) ≠ shear ℤ 1 := by
  intro equality
  have hentry := congrArg (fun unit : Matrix.UnitriangularGroup (Fin 2) ℤ =>
    unit.1 0 1) equality
  rw [sign_twist_entry, shear_entry] at hentry
  norm_num at hentry

private theorem dual_epsilon_nonzero : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro equality
  have second := congrArg TrivSqZeroExt.snd equality
  norm_num at second

private theorem dual_epsilon_square : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by
  simp

private theorem dual_shear_nonzero :
    (shear (DualNumber ℤ) DualNumber.eps).1 0 1 ≠ 0 := by
  rw [shear_entry]
  exact dual_epsilon_nonzero

private theorem dual_action_bridge :
    lift (diagonalGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ)
        (independentDiagonal (DualNumber ℤ) (-1) 1))
        (unitriangularGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ)
          (shear (DualNumber ℤ) DualNumber.eps)) ≫
          upperTriangularDiagonalConj ℤ (Fin 2) =
      unitriangularGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ)
        (Matrix.UpperTriangularGroup.diagonalAction
          (independentDiagonal (DualNumber ℤ) (-1) 1)
          (shear (DualNumber ℤ) DualNumber.eps)) :=
  upperTriangularDiagonalConj_point ℤ (Fin 2) (DualNumber ℤ) _ _

private theorem dual_twist_nonzero :
    (Matrix.UpperTriangularGroup.diagonalAction
      (independentDiagonal (DualNumber ℤ) (-1) 1)
      (shear (DualNumber ℤ) DualNumber.eps)).1 0 1 ≠ 0 := by
  rw [shear_twist_entry]
  simpa using (neg_ne_zero.mpr dual_epsilon_nonzero)

private theorem dual_twist_square_zero :
    (Matrix.UpperTriangularGroup.diagonalAction
      (independentDiagonal (DualNumber ℤ) (-1) 1)
      (shear (DualNumber ℤ) DualNumber.eps)).1 0 1 ^ 2 = 0 := by
  rw [shear_twist_entry]
  simp

private theorem reduction_not_injective :
    ¬ Function.Injective (Algebra.ofId ℤ (ZMod 2)) := by
  intro injective
  have equal : (Algebra.ofId ℤ (ZMod 2)) 0 =
      (Algebra.ofId ℤ (ZMod 2)) 2 := by
    change (0 : ZMod 2) = 2
    decide
  have distinct := injective equal
  norm_num at distinct

private theorem reduction_action_bridge
    (diag : Matrix.DiagonalGroup (Fin 2) ℤ)
    (unit : Matrix.UnitriangularGroup (Fin 2) ℤ) :
    lift (diagonalGroupMulEquivPoints ℤ (Fin 2) (ZMod 2)
        (Matrix.DiagonalGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom diag))
        (unitriangularGroupMulEquivPoints ℤ (Fin 2) (ZMod 2)
          (Matrix.UnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom unit)) ≫
          upperTriangularDiagonalConj ℤ (Fin 2) =
      unitriangularGroupMulEquivPoints ℤ (Fin 2) (ZMod 2)
        (Matrix.UnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom
          (Matrix.UpperTriangularGroup.diagonalAction diag unit)) := by
  rw [upperTriangularDiagonalConj_point]
  rw [Matrix.UpperTriangularGroup.diagonalAction_map]

private theorem reduction_inverse_bridge (matrix : Matrix.UpperTriangularGroup (Fin 2) ℤ) :
    (upperTriangularGroupMulEquivPoints ℤ (Fin 2) (ZMod 2)
      (Matrix.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom matrix) ≫
        (upperTriangularUFirstIso ℤ (Fin 2)).inv) ≫
          fst (unitriangularGroupUnderlyingScheme ℤ (Fin 2))
            (diagonalGroupUnderlyingScheme ℤ (Fin 2)) =
      unitriangularGroupMulEquivPoints ℤ (Fin 2) (ZMod 2)
        (Matrix.UnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom
          (Matrix.UpperTriangularGroup.unipotentPart matrix)) := by
  rw [upperTriangularUFirstIso_inv_fst_point]
  rw [Matrix.UpperTriangularGroup.unipotentPart_map]

end UpperTriangularSchemeProductClient
