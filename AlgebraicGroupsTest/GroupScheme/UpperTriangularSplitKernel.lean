/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import AlgebraicGroups.GroupTheory.UpperTriangular
public import GeneralLinearGroups.Elementary
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

namespace AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel

variable (K : Type) [CommRing K] (n : ℕ)

open TauCeti.GeneralLinear.UpperTriangular

private theorem group_splitting :
    diagonalTorus K n ≫ diagonalProjection K n =
      𝟙 (TauCeti.SplitTorus.groupScheme K (ULift (Fin n))) :=
  diagonalTorus_comp_diagonalProjection K n

private theorem actual_group_kernel :
    IsPullback (unitriangularInclusion K n)
      (0 : TauCeti.UpperUnitriangular.groupScheme K (Fin n) ⟶
        Grp.trivial (Over (Spec (.of K))))
      (diagonalProjection K n)
      (0 : Grp.trivial (Over (Spec (.of K))) ⟶
        TauCeti.SplitTorus.groupScheme K (ULift (Fin n))) :=
  isPullback_diagonalProjection_group K n

private theorem actual_scheme_kernel :
    IsPullback (unitriangularInclusion K n).hom.hom.left
      (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X.hom
      (diagonalProjection K n).hom.hom.left
      η[(TauCeti.SplitTorus.groupScheme K (ULift (Fin n))).X].left :=
  isPullback_diagonalProjection K n

private theorem actual_over_kernel :
    IsPullback (unitriangularInclusion K n).hom.hom
      (toUnit (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
      (diagonalProjection K n).hom.hom
      η[(TauCeti.SplitTorus.groupScheme K (ULift (Fin n))).X] :=
  isPullback_diagonalProjection_over K n

private theorem actual_closed_inclusion :
    IsClosedImmersion (unitriangularInclusion K n).hom.hom.left := inferInstance

private theorem unit_in_GL :
    unitriangularInclusion K n ≫ inclusion K n = TauCeti.UpperUnitriangular.inclusion K n :=
  unitriangularInclusion_comp_inclusion K n

private theorem diagonal_in_GL :
    diagonalTorus K n ≫ inclusion K n =
      TauCeti.GeneralLinear.diagonalTorus (R := K) (N := n) :=
  diagonalTorus_comp_inclusion K n

variable (R : Type) [CommRing R] [Algebra K R]

private theorem projection_all_algebras (s : TauCeti.upperTriangularGroup (Fin n) R) :
    Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s) ≫
      (diagonalProjection K n).hom.hom =
        Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R)).symm
          (fun i : ULift (Fin n) ↦ TauCeti.UpperTriangularGroup.diag s i.down)) :=
  diagonalProjection_point K n s

private theorem section_all_algebras (s : ULift (Fin n) → Rˣ) :
    Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R)).symm s) ≫
      (diagonalTorus K n).hom.hom =
        Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := R)).symm
          (TauCeti.UpperTriangularGroup.diagonalHom (fun i ↦ s (ULift.up i)))) :=
  diagonalTorus_point K n s

private theorem kernel_all_algebras (s : TauCeti.upperUnitriangularGroup (Fin n) R) :
    Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm s) ≫
      (unitriangularInclusion K n).hom.hom =
        Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := R)).symm
          ((Subgroup.inclusion
            TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) s)) :=
  unitriangularInclusion_point K n s

private theorem projection_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : TauCeti.upperTriangularGroup (Fin n) R) :
    TauCeti.UpperTriangularGroup.diag (TauCeti.UpperTriangularGroup.map v.toRingHom s) =
      fun i ↦ Units.map v.toRingHom.toMonoidHom (TauCeti.UpperTriangularGroup.diag s i) :=
  TauCeti.UpperTriangularGroup.diag_map v.toRingHom s

private theorem section_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Fin n → Rˣ) :
    TauCeti.UpperTriangularGroup.map v.toRingHom
      (TauCeti.UpperTriangularGroup.diagonalHom s) =
        TauCeti.UpperTriangularGroup.diagonalHom
          (fun i ↦ Units.map v.toRingHom.toMonoidHom (s i)) :=
  TauCeti.UpperTriangularGroup.diagonalHom_map v.toRingHom s

private theorem kernel_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : TauCeti.upperUnitriangularGroup (Fin n) R) :
    TauCeti.UpperTriangularGroup.map v.toRingHom
      ((Subgroup.inclusion
        TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) s) =
        (Subgroup.inclusion
          TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup)
          (TauCeti.UpperUnitriangularGroup.map v.toRingHom s) :=
  TauCeti.UpperTriangularGroup.inclusion_map v.toRingHom s

private theorem fin0_point (s : TauCeti.upperTriangularGroup (Fin 0) R) :
    TauCeti.UpperTriangularGroup.diag s = 1 := by
  funext i
  exact Fin.elim0 i

private theorem fin1_point (s : TauCeti.upperTriangularGroup (Fin 1) R) :
    TauCeti.UpperTriangularGroup.diagonalHom (TauCeti.UpperTriangularGroup.diag s) = s := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i
  fin_cases j
  simp [TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_apply,
    TauCeti.UpperTriangularGroup.diag_apply_val]

private def shear (a : R) : TauCeti.upperTriangularGroup (Fin 2) R :=
  ⟨Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a, by
    apply TauCeti.UpperTriangularGroup.mem_iff.mpr
    change (1 + Matrix.single (0 : Fin 2) 1 a : Matrix (Fin 2) (Fin 2) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add
      (Matrix.blockTriangular_single (by decide : (0 : Fin 2) ≤ 1) _)⟩

private def independentDiagonal (first second : Rˣ) : Fin 2 → Rˣ :=
  fun i ↦ if i = 0 then first else second

private theorem independentDiagonal_first (first second : Rˣ) :
    TauCeti.diagGL (independentDiagonal R first second) 0 0 = first := by
  simp [independentDiagonal, TauCeti.diagGL_apply]

private theorem independentDiagonal_second (first second : Rˣ) :
    TauCeti.diagGL (independentDiagonal R first second) 1 1 = second := by
  simp [independentDiagonal, TauCeti.diagGL_apply]

private theorem shear_entry (a : R) : (shear R a).1 0 1 = a := by
  simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private theorem sheared_independent_upper (first second : Rˣ) (a : R) :
    (shear R a * TauCeti.UpperTriangularGroup.diagonalHom
      (independentDiagonal R first second)).1 0 1 = a * second := by
  simp [independentDiagonal, TauCeti.UpperTriangularGroup.coe_diagonalHom,
    shear,
    Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply,
    Matrix.mul_diagonal, Subgroup.coe_mul, Units.val_mul]

private theorem sheared_independent_first (first second : Rˣ) (a : R) :
    ((TauCeti.UpperTriangularGroup.diag
      (shear R a * TauCeti.UpperTriangularGroup.diagonalHom
        (fun i ↦ if i = 0 then first else second)) 0 : Rˣ) : R) = first := by
  rw [TauCeti.UpperTriangularGroup.diag_apply_val]
  simp [TauCeti.UpperTriangularGroup.coe_diagonalHom,
    shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply,
    Matrix.mul_diagonal, Subgroup.coe_mul, Units.val_mul]

private theorem sheared_independent_second (first second : Rˣ) (a : R) :
    ((TauCeti.UpperTriangularGroup.diag
      (shear R a * TauCeti.UpperTriangularGroup.diagonalHom
        (fun i ↦ if i = 0 then first else second)) 1 : Rˣ) : R) = second := by
  rw [TauCeti.UpperTriangularGroup.diag_apply_val]
  simp [TauCeti.UpperTriangularGroup.coe_diagonalHom,
    shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply,
    Matrix.mul_diagonal, Subgroup.coe_mul, Units.val_mul]

private theorem shear_diagonal_point (first second : Rˣ) (a : R) :
    Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := 2) (A := R)).symm
      (shear R a * TauCeti.UpperTriangularGroup.diagonalHom
        (independentDiagonal R first second))) ≫
      (diagonalProjection K 2).hom.hom =
    Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R)).symm
      (fun i : ULift (Fin 2) ↦ TauCeti.UpperTriangularGroup.diag
        (shear R a * TauCeti.UpperTriangularGroup.diagonalHom
          (independentDiagonal R first second)) i.down)) :=
  diagonalProjection_point K 2 _

private theorem zero_ring_kernel :
    IsPullback (unitriangularInclusion (ZMod 1) 0)
      (0 : TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0) ⟶
        Grp.trivial (Over (Spec (.of (ZMod 1)))))
      (diagonalProjection (ZMod 1) 0)
      (0 : Grp.trivial (Over (Spec (.of (ZMod 1)))) ⟶
        TauCeti.SplitTorus.groupScheme (ZMod 1) (ULift (Fin 0))) :=
  isPullback_diagonalProjection_group (ZMod 1) 0

private theorem zero_ring_point (s : TauCeti.upperTriangularGroup (Fin 2) (ZMod 1)) :
    Spec.mapMulEquiv ((pointsMulEquiv (R := ZMod 1) (n := 2) (A := ZMod 1)).symm s) ≫
      (diagonalProjection (ZMod 1) 2).hom.hom =
    Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := ZMod 1) (A := ZMod 1)).symm
      (fun i : ULift (Fin 2) ↦ TauCeti.UpperTriangularGroup.diag s i.down)) :=
  diagonalProjection_point (ZMod 1) 2 s

private theorem dual_epsilon_nonzero : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro h
  have hs := congrArg TrivSqZeroExt.snd h
  norm_num at hs

private theorem dual_epsilon_square : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by
  simp

private theorem dual_shear_nonzero :
    (shear (DualNumber ℤ) DualNumber.eps).1 0 1 ≠ 0 := by
  rw [shear_entry]
  exact dual_epsilon_nonzero

private def dualUnit : TauCeti.upperUnitriangularGroup (Fin 2) (DualNumber ℤ) :=
  TauCeti.UpperTriangularGroup.unipotentPart
    (shear (DualNumber ℤ) DualNumber.eps)

private theorem dualUnit_is_shear :
    (Subgroup.inclusion
      TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) dualUnit =
      shear (DualNumber ℤ) DualNumber.eps := by
  rw [dualUnit, TauCeti.UpperTriangularGroup.inUpperTriangular_unipotentPart]
  have hdiag : TauCeti.UpperTriangularGroup.diag
    (shear (DualNumber ℤ) DualNumber.eps) = 1 := by
    funext i
    apply Units.ext
    fin_cases i <;> simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val,
      Matrix.add_apply, TauCeti.UpperTriangularGroup.diag_apply_val]
  simp [hdiag]

private theorem dual_unit_nonzero :
    ((Subgroup.inclusion
      TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) dualUnit).1 0
      1 ≠ 0 := by
  rw [dualUnit_is_shear]
  exact dual_shear_nonzero

private theorem dual_kernel_point :
    Spec.mapMulEquiv
      ((TauCeti.UpperUnitriangular.pointsMulEquiv ℤ (Fin 2) (A := DualNumber ℤ)).symm dualUnit) ≫
      (unitriangularInclusion ℤ 2).hom.hom =
    Spec.mapMulEquiv ((pointsMulEquiv (R := ℤ) (n := 2) (A := DualNumber ℤ)).symm
      ((Subgroup.inclusion
        TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) dualUnit)) :=
  unitriangularInclusion_point ℤ 2 dualUnit

private theorem reduction_not_injective :
    ¬ Function.Injective (Algebra.ofId ℤ (ZMod 1)) := by
  intro h
  have h01 := h (show (Algebra.ofId ℤ (ZMod 1)) 0 =
    (Algebra.ofId ℤ (ZMod 1)) 1 from Subsingleton.elim _ _)
  norm_num at h01

private theorem reduction_projection_natural
    (s : TauCeti.upperTriangularGroup (Fin 2) ℤ) :
    TauCeti.UpperTriangularGroup.diag
      (TauCeti.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) =
      fun i ↦ Units.map (Algebra.ofId ℤ (ZMod 1)).toRingHom.toMonoidHom
        (TauCeti.UpperTriangularGroup.diag s i) :=
  TauCeti.UpperTriangularGroup.diag_map _ s

private theorem reduction_section_natural (s : Fin 2 → ℤˣ) :
    TauCeti.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      (TauCeti.UpperTriangularGroup.diagonalHom s) =
    TauCeti.UpperTriangularGroup.diagonalHom
      (fun i ↦ Units.map (Algebra.ofId ℤ (ZMod 1)).toRingHom.toMonoidHom (s i)) :=
  TauCeti.UpperTriangularGroup.diagonalHom_map _ s

private theorem reduction_kernel_natural (s : TauCeti.upperUnitriangularGroup (Fin 2) ℤ) :
    TauCeti.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      ((Subgroup.inclusion
        TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) s) =
    (Subgroup.inclusion
      TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup)
      (TauCeti.UpperUnitriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) :=
  TauCeti.UpperTriangularGroup.inclusion_map _ s

end AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel
