/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import GeneralLinearGroups.Elementary
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

namespace AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel

variable (K : Type) [CommRing K] (n : Type) [Fintype n] [LinearOrder n]

private theorem group_splitting :
    upperTriangularDiagonalSection K n ≫ upperTriangularDiagonalProjection K n =
      𝟙 (diagonalGroupScheme K n) :=
  upperTriangularDiagonal_section K n

private theorem actual_group_kernel :
    IsPullback (unitriangularToUpperTriangular K n)
      (unitriangularToTrivialGroupHom K n)
      (upperTriangularDiagonalProjection K n) (diagonalUnitGroupHom K n) :=
  upperTriangularDiagonalSquare_isPullback_group K n

private theorem actual_scheme_kernel :
    IsPullback (unitriangularToUpperTriangular K n).hom.hom.left
      (unitriangularGroupUnderlyingScheme K n).hom
      (upperTriangularDiagonalProjection K n).hom.hom.left
      η[diagonalGroupUnderlyingScheme K n].left :=
  upperTriangularDiagonalSquare_isPullback K n

private theorem actual_over_kernel :
    IsPullback (unitriangularToUpperTriangular K n).hom.hom
      (toUnit (unitriangularGroupScheme K n).toMon.X)
      (upperTriangularDiagonalProjection K n).hom.hom
      η[(diagonalGroupScheme K n).toMon.X] :=
  upperTriangularDiagonalSquare_isPullback_over K n

private theorem actual_closed_inclusion :
    IsClosedImmersion (unitriangularToUpperTriangular K n).hom.hom.left :=
  unitriangularToUpperTriangular_isClosedImmersion K n

private theorem unit_in_GL :
    unitriangularToUpperTriangular K n ≫ upperTriangularInclusion K n =
      unitriangularInclusion K n :=
  unitriangularToUpperTriangular_inclusion K n

private theorem diagonal_in_GL :
    upperTriangularDiagonalSection K n ≫ upperTriangularInclusion K n =
      diagonalInclusion K n :=
  upperTriangularDiagonalSection_inclusion K n

variable (R : Type) [CommRing R] [Algebra K R]

private theorem projection_all_algebras (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R s ≫
      (upperTriangularDiagonalProjection K n).hom.hom =
        diagonalGroupMulEquivPoints K n R (Matrix.UpperTriangularGroup.diagonal s) :=
  upperTriangularDiagonalProjection_point K n R s

private theorem section_all_algebras (s : Matrix.DiagonalGroup n R) :
    diagonalGroupMulEquivPoints K n R s ≫
      (upperTriangularDiagonalSection K n).hom.hom =
        upperTriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonalSection s) :=
  upperTriangularDiagonalSection_point K n R s

private theorem kernel_all_algebras (s : Matrix.UnitriangularGroup n R) :
    unitriangularGroupMulEquivPoints K n R s ≫
      (unitriangularToUpperTriangular K n).hom.hom =
        upperTriangularGroupMulEquivPoints K n R
          (Matrix.UnitriangularGroup.inUpperTriangular s) :=
  unitriangularToUpperTriangular_point K n R s

private theorem projection_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UpperTriangularGroup n R) :
    Matrix.UpperTriangularGroup.diagonal
      (Matrix.UpperTriangularGroup.map v.toRingHom s) =
        Matrix.DiagonalGroup.map v.toRingHom
          (Matrix.UpperTriangularGroup.diagonal s) :=
  Matrix.UpperTriangularGroup.diagonal_map v.toRingHom s

private theorem section_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.DiagonalGroup n R) :
    Matrix.UpperTriangularGroup.map v.toRingHom
      (Matrix.UpperTriangularGroup.diagonalSection s) =
        Matrix.UpperTriangularGroup.diagonalSection
          (Matrix.DiagonalGroup.map v.toRingHom s) :=
  Matrix.UpperTriangularGroup.diagonalSection_map v.toRingHom s

private theorem kernel_natural (S : Type) [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup n R) :
    Matrix.UpperTriangularGroup.map v.toRingHom
      (Matrix.UnitriangularGroup.inUpperTriangular s) =
        Matrix.UnitriangularGroup.inUpperTriangular
          (Matrix.UnitriangularGroup.map v.toRingHom s) :=
  Matrix.UnitriangularGroup.inUpperTriangular_map v.toRingHom s

private theorem fin0_point (s : Matrix.UpperTriangularGroup (Fin 0) R) :
    Matrix.UpperTriangularGroup.diagonal s = 1 := by
  apply Matrix.DiagonalGroup.ext
  intro i
  exact Fin.elim0 i

private theorem fin1_point (s : Matrix.UpperTriangularGroup (Fin 1) R) :
    Matrix.UpperTriangularGroup.diagonalSection
      (Matrix.UpperTriangularGroup.diagonal s) = s := by
  apply Matrix.UpperTriangularGroup.ext
  intro i j
  fin_cases i
  fin_cases j
  exact Matrix.UpperTriangularGroup.diagonal_apply_diag s 0

private def shear (a : R) : Matrix.UpperTriangularGroup (Fin 2) R :=
  ⟨Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a, by
    change (1 + Matrix.single (0 : Fin 2) 1 a : Matrix (Fin 2) (Fin 2) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add
      (Matrix.blockTriangular_single (by decide : (0 : Fin 2) ≤ 1) _)⟩

private def independentDiagonal (first second : Rˣ) :
    Matrix.DiagonalGroup (Fin 2) R :=
  (Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
    (Fin 2 → Rˣ)).symm (fun i => if i = 0 then first else second)

private theorem independentDiagonal_first (first second : Rˣ) :
    (independentDiagonal R first second).1 0 0 = first := by
  simp [independentDiagonal, Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private theorem independentDiagonal_second (first second : Rˣ) :
    (independentDiagonal R first second).1 1 1 = second := by
  simp [independentDiagonal, Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private theorem shear_entry (a : R) : (shear R a).1 0 1 = a := by
  simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private theorem sheared_independent_upper (first second : Rˣ) (a : R) :
    (shear R a * Matrix.UpperTriangularGroup.diagonalSection
      (independentDiagonal R first second)).1 0 1 = a * second := by
  change ((shear R a).1 * (independentDiagonal R first second).1 :
    Matrix (Fin 2) (Fin 2) R) 0 1 = _
  have hzero : (independentDiagonal R first second).1 0 1 = 0 :=
    (independentDiagonal R first second).2 0 1 (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_two, hzero, mul_zero, zero_add,
    shear_entry, independentDiagonal_second]

private theorem sheared_independent_first (first second : Rˣ) (a : R) :
    (Matrix.UpperTriangularGroup.diagonal
      (shear R a * Matrix.UpperTriangularGroup.diagonalSection
        (independentDiagonal R first second))).1 0 0 = first := by
  rw [Matrix.UpperTriangularGroup.diagonal_apply_diag]
  change ((shear R a).1 * (independentDiagonal R first second).1 :
    Matrix (Fin 2) (Fin 2) R) 0 0 = first
  have hzero : (independentDiagonal R first second).1 1 0 = 0 :=
    (independentDiagonal R first second).2 1 0 (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_two, hzero, mul_zero, add_zero,
    independentDiagonal_first]
  simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private theorem sheared_independent_second (first second : Rˣ) (a : R) :
    (Matrix.UpperTriangularGroup.diagonal
      (shear R a * Matrix.UpperTriangularGroup.diagonalSection
        (independentDiagonal R first second))).1 1 1 = second := by
  rw [Matrix.UpperTriangularGroup.diagonal_apply_diag]
  change ((shear R a).1 * (independentDiagonal R first second).1 :
    Matrix (Fin 2) (Fin 2) R) 1 1 = second
  have hzero : (shear R a).1 1 0 = 0 := (shear R a).2 (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_two, hzero, zero_mul, zero_add,
    independentDiagonal_second]
  simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private theorem shear_diagonal_point (first second : Rˣ) (a : R) :
    upperTriangularGroupMulEquivPoints K (Fin 2) R
        (shear R a * Matrix.UpperTriangularGroup.diagonalSection
          (independentDiagonal R first second)) ≫
      (upperTriangularDiagonalProjection K (Fin 2)).hom.hom =
    diagonalGroupMulEquivPoints K (Fin 2) R
      (Matrix.UpperTriangularGroup.diagonal
        (shear R a * Matrix.UpperTriangularGroup.diagonalSection
          (independentDiagonal R first second))) :=
  upperTriangularDiagonalProjection_point K (Fin 2) R _

private theorem zero_ring_kernel :
    IsPullback (unitriangularToUpperTriangular (ZMod 1) (Fin 0))
      (unitriangularToTrivialGroupHom (ZMod 1) (Fin 0))
      (upperTriangularDiagonalProjection (ZMod 1) (Fin 0))
      (diagonalUnitGroupHom (ZMod 1) (Fin 0)) :=
  upperTriangularDiagonalSquare_isPullback_group (ZMod 1) (Fin 0)

private theorem zero_ring_point (s : Matrix.UpperTriangularGroup (Fin 2) (ZMod 1)) :
    upperTriangularGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1) s ≫
      (upperTriangularDiagonalProjection (ZMod 1) (Fin 2)).hom.hom =
    diagonalGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1)
      (Matrix.UpperTriangularGroup.diagonal s) :=
  upperTriangularDiagonalProjection_point (ZMod 1) (Fin 2) (ZMod 1) s

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

private def dualUnit : Matrix.UnitriangularGroup (Fin 2) (DualNumber ℤ) :=
  Matrix.UpperTriangularGroup.unipotentPart
    (shear (DualNumber ℤ) DualNumber.eps)

private theorem dualUnit_is_shear :
    Matrix.UnitriangularGroup.inUpperTriangular dualUnit =
      shear (DualNumber ℤ) DualNumber.eps := by
  rw [dualUnit, Matrix.UpperTriangularGroup.inUpperTriangular_unipotentPart]
  have hdiag : Matrix.UpperTriangularGroup.diagonal
    (shear (DualNumber ℤ) DualNumber.eps) = 1 := by
    apply Matrix.DiagonalGroup.ext
    intro i
    fin_cases i <;> simp [shear, Matrix.GeneralLinearGroup.elementaryUnit_val,
      Matrix.add_apply, Matrix.UpperTriangularGroup.diagonal_apply_diag]
  simp [hdiag]

private theorem dual_unit_nonzero :
    (Matrix.UnitriangularGroup.inUpperTriangular dualUnit).1 0 1 ≠ 0 := by
  rw [dualUnit_is_shear]
  exact dual_shear_nonzero

private theorem dual_kernel_point :
    unitriangularGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ)
      dualUnit ≫
      (unitriangularToUpperTriangular ℤ (Fin 2)).hom.hom =
    upperTriangularGroupMulEquivPoints ℤ (Fin 2) (DualNumber ℤ)
      (Matrix.UnitriangularGroup.inUpperTriangular dualUnit) :=
  unitriangularToUpperTriangular_point ℤ (Fin 2) (DualNumber ℤ) dualUnit

private theorem reduction_not_injective :
    ¬ Function.Injective (Algebra.ofId ℤ (ZMod 1)) := by
  intro h
  have h01 := h (show (Algebra.ofId ℤ (ZMod 1)) 0 =
    (Algebra.ofId ℤ (ZMod 1)) 1 from Subsingleton.elim _ _)
  norm_num at h01

private theorem reduction_projection_natural
    (s : Matrix.UpperTriangularGroup (Fin 2) ℤ) :
    Matrix.UpperTriangularGroup.diagonal
      (Matrix.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) =
    Matrix.DiagonalGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      (Matrix.UpperTriangularGroup.diagonal s) :=
  Matrix.UpperTriangularGroup.diagonal_map _ s

private theorem reduction_section_natural (s : Matrix.DiagonalGroup (Fin 2) ℤ) :
    Matrix.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      (Matrix.UpperTriangularGroup.diagonalSection s) =
    Matrix.UpperTriangularGroup.diagonalSection
      (Matrix.DiagonalGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) :=
  Matrix.UpperTriangularGroup.diagonalSection_map _ s

private theorem reduction_kernel_natural (s : Matrix.UnitriangularGroup (Fin 2) ℤ) :
    Matrix.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom
      (Matrix.UnitriangularGroup.inUpperTriangular s) =
    Matrix.UnitriangularGroup.inUpperTriangular
      (Matrix.UnitriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) :=
  Matrix.UnitriangularGroup.inUpperTriangular_map _ s

end AlgebraicGroupsTest.GroupScheme.UpperTriangularSplitKernel
