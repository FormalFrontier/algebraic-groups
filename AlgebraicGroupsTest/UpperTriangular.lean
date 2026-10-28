/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UpperTriangular
public import GeneralLinearGroups.Elementary
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import clients of native upper-triangular groups -/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGroupsTest.UpperTriangular

open Matrix hiding diag
open TauCeti
open TauCeti.UpperTriangularGroup
open scoped DualNumber

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem general_kernel :
    (diag (m := ι) (R := R)).ker =
      (upperUnitriangularGroup ι R).subgroupOf (upperTriangularGroup ι R) := ker_diag

private theorem general_column (matrix : upperTriangularGroup ι R) (row col : ι) :
    (TauCeti.UpperTriangularGroup.unipotentPart matrix).1 row col = matrix.1 row col *
      (((diag matrix col)⁻¹ : Rˣ) : R) :=
  TauCeti.UpperTriangularGroup.unipotentPart_apply matrix row col

private theorem general_action (d : (ι → Rˣ))
    (unit : upperUnitriangularGroup ι R) (row col : ι) :
    (diagonalAction d unit).1 row col =
      (d row : Rˣ) * unit.1 row col *
        (((d col)⁻¹ : Rˣ) : R) :=
  diagonalAction_apply d unit row col

private theorem general_naturality (ringHom : R →+* S)
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction]
      (ι → Rˣ)) :
    TauCeti.UpperTriangularGroup.map ringHom (TauCeti.UpperTriangularGroup.semidirEquiv coords) =
      TauCeti.UpperTriangularGroup.semidirEquiv (TauCeti.UpperTriangularGroup.semidirMap ringHom
        coords) :=
  TauCeti.UpperTriangularGroup.semidirEquiv_map ringHom coords

private theorem general_inverse_naturality (ringHom : R →+* S)
    (matrix : upperTriangularGroup ι R) :
    TauCeti.UpperTriangularGroup.semidirMap ringHom
      (TauCeti.UpperTriangularGroup.semidirEquiv.symm matrix) =
      TauCeti.UpperTriangularGroup.semidirEquiv.symm (TauCeti.UpperTriangularGroup.map ringHom
        matrix) :=
  TauCeti.UpperTriangularGroup.semidirEquiv_symm_map ringHom matrix

private theorem general_section_naturality (ringHom : R →+* S)
    (d : (ι → Rˣ)) :
    TauCeti.UpperTriangularGroup.map ringHom (diagonalHom d) =
      diagonalHom ((fun i ↦ Units.map ringHom.toMonoidHom (d i))) :=
  diagonalHom_map ringHom d

private theorem general_projection_naturality (ringHom : R →+* S)
    (matrix : upperTriangularGroup ι R) :
    diag (TauCeti.UpperTriangularGroup.map ringHom matrix) =
      (fun i ↦ Units.map ringHom.toMonoidHom (diag matrix i)) :=
  diag_map ringHom matrix

private theorem general_inclusion_naturality (ringHom : R →+* S)
    (unit : upperUnitriangularGroup ι R) :
    TauCeti.UpperTriangularGroup.map ringHom ((Subgroup.inclusion
      upperUnitriangularGroup_le_upperTriangularGroup) unit) =
      (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
        (UpperUnitriangularGroup.map ringHom unit) :=
  inclusion_map ringHom unit

private theorem general_splitting (d : (ι → Rˣ)) :
    diag (diagonalHom d) = d :=
  diag_diagonalHom d

private theorem general_factorization (matrix : upperTriangularGroup ι R) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
      (TauCeti.UpperTriangularGroup.unipotentPart matrix) *
      diagonalHom (diag matrix) =
        matrix :=
  TauCeti.UpperTriangularGroup.unipotentPart_factor matrix

private theorem general_two_triangles
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction]
      (ι → Rˣ)) (matrix : upperTriangularGroup ι R) :
    TauCeti.UpperTriangularGroup.semidirEquiv.symm (TauCeti.UpperTriangularGroup.semidirEquiv
      coords) =
        coords ∧
      TauCeti.UpperTriangularGroup.semidirEquiv (TauCeti.UpperTriangularGroup.semidirEquiv.symm
        matrix) =
        matrix :=
  ⟨MulEquiv.symm_apply_apply _ coords, MulEquiv.apply_symm_apply _ matrix⟩

private theorem general_action_naturality (ringHom : R →+* S)
    (d : (ι → Rˣ)) (unit : upperUnitriangularGroup ι R) :
    UpperUnitriangularGroup.map ringHom (diagonalAction d unit) =
      diagonalAction ((fun i ↦ Units.map ringHom.toMonoidHom (d i)))
        (UpperUnitriangularGroup.map ringHom unit) :=
  diagonalAction_map ringHom d unit

variable {Coeff : Type} [CommRing Coeff]

private theorem fin0_upper_trivial (left right : upperTriangularGroup (Fin 0) Coeff) :
    left = right := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_diagonal_trivial (left right : ((Fin 0) → Coeffˣ)) :
    left = right := by
  funext row
  exact Fin.elim0 row

private theorem fin0_unitriangular_trivial (left right : upperUnitriangularGroup (Fin 0) Coeff) :
    left = right := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_semidirect_trivial (left right :
    upperUnitriangularGroup (Fin 0) Coeff ⋊[diagonalAction]
      ((Fin 0) → Coeffˣ)) : left = right := by
  apply SemidirectProduct.ext
  · exact fin0_unitriangular_trivial _ _
  · exact fin0_diagonal_trivial _ _

private theorem fin1_unitriangular_trivial (unit : upperUnitriangularGroup (Fin 1) Coeff) :
    unit = 1 := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row col
  fin_cases row
  fin_cases col
  simp

private def fin1_upper_diagonal_equiv :
    upperTriangularGroup (Fin 1) Coeff ≃* ((Fin 1) → Coeffˣ) :=
  MulEquiv.ofBijective diag (by
    constructor
    · intro left right equal
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro row col
      have same : row = col := Subsingleton.elim row col
      subst col
      have entries := congrArg (fun d : ((Fin 1) → Coeffˣ) =>
        (d row : Coeff)) equal
      simpa [diag_apply_val] using entries
    · exact diag_surjective)

private theorem fin2_column (matrix : upperTriangularGroup (Fin 2) Coeff) :
    (TauCeti.UpperTriangularGroup.unipotentPart matrix).1 0 1 = matrix.1 0 1 *
      (((diag matrix 1)⁻¹ : Coeffˣ) : Coeff) :=
  TauCeti.UpperTriangularGroup.unipotentPart_apply matrix 0 1

private theorem fin2_action (d : ((Fin 2) → Coeffˣ))
    (unit : upperUnitriangularGroup (Fin 2) Coeff) :
    (diagonalAction d unit).1 0 1 =
      (d 0 : Coeffˣ) * unit.1 0 1 *
        (((d 1)⁻¹ : Coeffˣ) : Coeff) :=
  diagonalAction_apply d unit 0 1

private theorem fin2_section_projection (d : ((Fin 2) → Coeffˣ)) :
    diag (diagonalHom d) = d :=
  diag_diagonalHom d

private theorem fin2_product (first second :
    upperUnitriangularGroup (Fin 2) Coeff ⋊[diagonalAction]
      ((Fin 2) → Coeffˣ)) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) first.left *
        diagonalHom first.right *
        ((Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) second.left *
          diagonalHom second.right) =
      (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
          (first.left * diagonalAction first.right second.left) *
        diagonalHom (first.right * second.right) :=
  TauCeti.UpperTriangularGroup.semidirEquiv_mul_formula first second

private theorem zero_ring_fin2 (matrix : upperTriangularGroup (Fin 2) (ZMod 1)) :
    matrix = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Subsingleton.elim _ _

private theorem zero_ring_fin0 (matrix : upperTriangularGroup (Fin 0) (ZMod 1)) :
    matrix = 1 := fin0_upper_trivial _ _

private def dualUnit : (DualNumber ℤ)ˣ :=
  ⟨1 + DualNumber.eps, 1 - DualNumber.eps,
    by
      calc
        (1 + DualNumber.eps) * (1 - DualNumber.eps) =
            (1 : DualNumber ℤ) - DualNumber.eps * DualNumber.eps := by ring
        _ = 1 := by simp,
    by
      calc
        (1 - DualNumber.eps) * (1 + DualNumber.eps) =
            (1 : DualNumber ℤ) - DualNumber.eps * DualNumber.eps := by ring
        _ = 1 := by simp⟩

private def dualDiagonal : ((Fin 2) → (DualNumber ℤ)ˣ) :=
  fun row => if row = 0 then dualUnit else 1

private def dualUpperOne : upperUnitriangularGroup (Fin 2) (DualNumber ℤ) :=
  ⟨GeneralLinearGroup.elementaryUnit 0 1 (by decide) 1, by
    rw [UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def]
    refine ⟨?_, ?_⟩
    · change (1 + Matrix.single (0 : Fin 2) 1 (1 : DualNumber ℤ) :
        Matrix (Fin 2) (Fin 2) (DualNumber ℤ)).IsUpperTriangular
      exact Matrix.blockTriangular_one.add
        (Matrix.blockTriangular_single (by decide : (0 : Fin 2) ≤ 1) _)
    · intro row
      change (1 + Matrix.single (0 : Fin 2) 1 (1 : DualNumber ℤ) :
        Matrix (Fin 2) (Fin 2) (DualNumber ℤ)) row row = 1
      have different : ¬ ((0 : Fin 2) = row ∧ (1 : Fin 2) = row) :=
        fun equal => (by decide : (0 : Fin 2) ≠ 1) (equal.1.trans equal.2.symm)
      simp [Matrix.add_apply, different]⟩

private theorem dual_upper_entry : dualUpperOne.1 0 1 = (1 : DualNumber ℤ) := by
  simp [dualUpperOne, GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private theorem dual_action_retains_epsilon :
    (diagonalAction dualDiagonal dualUpperOne).1 0 1 =
      1 + DualNumber.eps := by
  rw [diagonalAction_apply, dual_upper_entry]
  simp [dualDiagonal, dualUnit]

private theorem dual_epsilon_nonzero :
    (diagonalAction dualDiagonal dualUpperOne).1 0 1 ≠
      (1 : DualNumber ℤ) := by
  rw [dual_action_retains_epsilon]
  intro equal
  have coefficient := congrArg TrivSqZeroExt.snd equal
  norm_num at coefficient

private def quotientHom : ℤ →+* ZMod 1 := Int.castRingHom (ZMod 1)

private theorem quotientHom_noninjective : ¬ Function.Injective quotientHom := by
  intro injective
  have equal : (0 : ℤ) = 1 := injective (Subsingleton.elim _ _)
  norm_num at equal

private theorem noninjective_square (coords :
    upperUnitriangularGroup (Fin 2) ℤ ⋊[diagonalAction]
      ((Fin 2) → ℤˣ)) :
    TauCeti.UpperTriangularGroup.map quotientHom (TauCeti.UpperTriangularGroup.semidirEquiv
      coords) =
      TauCeti.UpperTriangularGroup.semidirEquiv
        (TauCeti.UpperTriangularGroup.semidirMap quotientHom coords) :=
  TauCeti.UpperTriangularGroup.semidirEquiv_map quotientHom coords

end AlgebraicGroupsTest.UpperTriangular
