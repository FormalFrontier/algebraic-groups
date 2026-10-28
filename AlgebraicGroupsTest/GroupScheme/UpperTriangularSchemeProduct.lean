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

open TauCeti.GeneralLinear.UpperTriangular

variable (K : Type) [CommRing K] (n : ℕ)

private theorem arbitrary_test_twisted_law {test : Over (Spec (.of K))}
    (unit unit' : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
    (diag diag' : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift (Fin n))).X) :
    lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
        (diag * diag') ≫ (upperTriangularUFirstIso K n).hom =
      (lift unit diag ≫ (upperTriangularUFirstIso K n).hom) *
        (lift unit' diag' ≫ (upperTriangularUFirstIso K n).hom) :=
  upperTriangularUFirstIso_mul_lift K n unit unit' diag diag'

private theorem arbitrary_test_diagram :
    upperTriangularUFirstTwistedMul K n ≫ (upperTriangularUFirstIso K n).hom =
      ((upperTriangularUFirstIso K n).hom ⊗ₘ
        (upperTriangularUFirstIso K n).hom) ≫
        μ[(groupScheme K n).X] :=
  upperTriangularUFirstTwistedMul_comp_hom K n

private theorem arbitrary_test_normalization :
    ((upperTriangularUFirstIso K n).inv ≫
      fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
        ((TauCeti.SplitTorus.groupScheme K (ULift (Fin n))).X)) ≫
        (unitriangularInclusion K n).hom.hom =
      𝟙 ((groupScheme K n).X) *
        ((diagonalProjection K n).hom.hom ≫
          (diagonalTorus K n).hom.hom)⁻¹ :=
  upperTriangularUFirstIso_inv_fst_comp_inclusion K n

variable (R : Type) [CommRing R] [Algebra K R]

private theorem fin0_inverse (matrix : TauCeti.upperTriangularGroup (Fin 0) R) :
    ((Spec.mapMulEquiv ((TauCeti.GeneralLinear.UpperTriangular.pointsMulEquiv (R := K) (n :=
      0) (A := R)).symm matrix)) ≫
      (upperTriangularUFirstIso K 0).inv) ≫
        fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin
          0)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift (Fin 0))).X) =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 0) (A := R)).symm
        (TauCeti.UpperTriangularGroup.unipotentPart matrix))) :=
  upperTriangularUFirstIso_inv_fst_point K 0 R matrix

private theorem fin0_unit (unit : TauCeti.upperUnitriangularGroup (Fin 0) R) : unit = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin1_inverse (matrix : TauCeti.upperTriangularGroup (Fin 1) R) :
    ((Spec.mapMulEquiv ((TauCeti.GeneralLinear.UpperTriangular.pointsMulEquiv (R := K) (n :=
      1) (A := R)).symm matrix)) ≫
      (upperTriangularUFirstIso K 1).inv) ≫
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin
          1)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift (Fin 1))).X) =
      (Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ := ULift (Fin
        1))).symm (fun i => ((TauCeti.UpperTriangularGroup.diag matrix)) i.down))) :=
  upperTriangularUFirstIso_inv_snd_point K 1 R matrix

private theorem fin1_unit (unit : TauCeti.upperUnitriangularGroup (Fin 1) R) : unit = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  have hrow : row = 0 := Subsingleton.elim _ _
  have hcol : col = 0 := Subsingleton.elim _ _
  subst row
  subst col
  simp

private theorem zero_ring_inverse (matrix : TauCeti.upperTriangularGroup (Fin 2) (ZMod 1)) :
    (Spec.mapMulEquiv ((TauCeti.GeneralLinear.UpperTriangular.pointsMulEquiv (R := (ZMod 1))
      (n := 2) (A := (ZMod 1))).symm matrix)) ≫
      (upperTriangularUFirstIso (ZMod 1) 2).inv =
        lift ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv (ZMod 1) (Fin 2)
          (A := (ZMod
          1))).symm (TauCeti.UpperTriangularGroup.unipotentPart matrix))))
          ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := (ZMod 1)) (A := (ZMod
            1)) (σ := ULift (Fin 2))).symm (fun i => ((TauCeti.UpperTriangularGroup.diag
            matrix)) i.down)))) :=
  upperTriangularUFirstIso_inv_point (ZMod 1) 2 (ZMod 1) matrix

private def shear (a : R) : TauCeti.upperUnitriangularGroup (Fin 2) R :=
  TauCeti.UpperUnitriangularGroup.elementary 2 R 0 1 (by decide) a

private theorem shear_entry (a : R) : (shear R a).1 0 1 = a := by
  simp [shear, TauCeti.UpperUnitriangularGroup.elementary_coe, Matrix.add_apply]

private def independentDiagonal (first second : Rˣ) : Fin 2 → Rˣ :=
  fun index => if index = 0 then first else second

private theorem independentDiagonal_first (first second : Rˣ) :
    independentDiagonal R first second 0 = first := by simp [independentDiagonal]

private theorem independentDiagonal_second (first second : Rˣ) :
    independentDiagonal R first second 1 = second := by simp [independentDiagonal]

private theorem shear_twist_entry (first second : Rˣ) (a : R) :
    (TauCeti.UpperTriangularGroup.diagonalAction
      ((independentDiagonal R first second)) (shear R a)).1 0 1 =
        (first : R) * a * (((second⁻¹ : Rˣ) : R)) := by
  rw [TauCeti.UpperTriangularGroup.diagonalAction_apply,
    shear_entry, independentDiagonal_first, independentDiagonal_second]

private theorem fin2_forward (first second : Rˣ) (a : R) :
    lift ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 2) (A :=
      R)).symm (shear R a))))
        ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ := ULift
          (Fin 2))).symm (fun i => (independentDiagonal R first second) i.down)))) ≫
          (upperTriangularUFirstIso K 2).hom =
      (Spec.mapMulEquiv ((TauCeti.GeneralLinear.UpperTriangular.pointsMulEquiv (R := K) (n :=
        2) (A := R)).symm (TauCeti.UpperTriangularGroup.semidirEquiv
          (⟨shear R a, (independentDiagonal R first second)⟩ :
            TauCeti.upperUnitriangularGroup (Fin 2) R ⋊[TauCeti.UpperTriangularGroup.diagonalAction]
              (Fin 2 → Rˣ))))) :=
  upperTriangularUFirstIso_point K 2 R _ _

private theorem fin2_action_bridge (first second : Rˣ) (a : R) :
    lift ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ := ULift
      (Fin 2))).symm (fun i => (independentDiagonal R first second) i.down))))
        ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 2) (A :=
          R)).symm (shear R a)))) ≫
          upperTriangularDiagonalConj K 2 =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 2) (A := R)).symm
        (TauCeti.UpperTriangularGroup.diagonalAction
          ((independentDiagonal R first second)) (shear R a)))) :=
  upperTriangularDiagonalConj_point K 2 R _ _

private theorem sign_twist_entry :
    (TauCeti.UpperTriangularGroup.diagonalAction
      ((independentDiagonal ℤ (-1) 1)) (shear ℤ 1)).1 0 1 = -1 := by
  rw [shear_twist_entry]
  norm_num

private theorem sign_twist_not_direct :
    TauCeti.UpperTriangularGroup.diagonalAction
        ((independentDiagonal ℤ (-1) 1)) (shear ℤ 1) ≠ shear ℤ 1
          := by
  intro equality
  have hentry := congrArg (fun unit : TauCeti.upperUnitriangularGroup (Fin 2) ℤ =>
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
    lift ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := ℤ) (A := (DualNumber ℤ))
      (σ := ULift (Fin 2))).symm (fun i => (independentDiagonal (DualNumber ℤ) (-1) 1) i.down))))
        ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A :=
          (DualNumber ℤ))).symm (shear (DualNumber ℤ) DualNumber.eps)))) ≫
          upperTriangularDiagonalConj ℤ 2 =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A :=
        (DualNumber ℤ))).symm (TauCeti.UpperTriangularGroup.diagonalAction
          ((independentDiagonal (DualNumber ℤ) (-1) 1))
          (shear (DualNumber ℤ) DualNumber.eps)))) :=
  upperTriangularDiagonalConj_point ℤ 2 (DualNumber ℤ) _ _

private theorem dual_twist_nonzero :
    (TauCeti.UpperTriangularGroup.diagonalAction
      ((independentDiagonal (DualNumber ℤ) (-1) 1))
      (shear (DualNumber ℤ) DualNumber.eps)).1 0 1 ≠ 0 := by
  rw [shear_twist_entry]
  simpa using (neg_ne_zero.mpr dual_epsilon_nonzero)

private theorem dual_twist_square_zero :
    (TauCeti.UpperTriangularGroup.diagonalAction
      ((independentDiagonal (DualNumber ℤ) (-1) 1))
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
    (diag : (Fin 2 → ℤˣ))
    (unit : TauCeti.upperUnitriangularGroup (Fin 2) ℤ) :
    lift ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := ℤ) (A := (ZMod 2)) (σ :=
      ULift (Fin 2))).symm (fun i => ((fun i => Units.map (Algebra.ofId ℤ (ZMod
      2)).toMonoidHom (diag i))) i.down))))
        ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A := (ZMod
          2))).symm (TauCeti.UpperUnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom
          unit)))) ≫
          upperTriangularDiagonalConj ℤ 2 =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A := (ZMod
        2))).symm (TauCeti.UpperUnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom
          (TauCeti.UpperTriangularGroup.diagonalAction (diag)
            unit)))) := by
  erw [upperTriangularDiagonalConj_point ℤ 2 (ZMod 2)
    (fun i => Units.map (Algebra.ofId ℤ (ZMod 2)).toMonoidHom (diag i))
    (TauCeti.UpperUnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom unit)]
  rw [TauCeti.UpperTriangularGroup.diagonalAction_map]

private theorem reduction_inverse_bridge (matrix : TauCeti.upperTriangularGroup (Fin 2) ℤ) :
    ((Spec.mapMulEquiv ((TauCeti.GeneralLinear.UpperTriangular.pointsMulEquiv (R := ℤ) (n :=
      2) (A := (ZMod 2))).symm (TauCeti.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod
      2)).toRingHom matrix))) ≫
        (upperTriangularUFirstIso ℤ 2).inv) ≫
          fst ((TauCeti.UpperUnitriangular.groupScheme ℤ (Fin 2)).X)
            ((TauCeti.SplitTorus.groupScheme ℤ (ULift (Fin 2))).X) =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A := (ZMod
        2))).symm (TauCeti.UpperUnitriangularGroup.map (Algebra.ofId ℤ (ZMod 2)).toRingHom
          (TauCeti.UpperTriangularGroup.unipotentPart matrix)))) := by
  rw [upperTriangularUFirstIso_inv_fst_point]
  rw [TauCeti.UpperTriangularGroup.unipotentPart_map]

end UpperTriangularSchemeProductClient
