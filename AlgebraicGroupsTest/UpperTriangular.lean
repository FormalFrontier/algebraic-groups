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

open Matrix
open scoped DualNumber

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem general_kernel :
    (UnitriangularGroup.inUpperTriangular (ι := ι) (R := R)).range =
      (UpperTriangularGroup.diagonal (ι := ι) (R := R)).ker :=
  UpperTriangularGroup.range_unitriangular

private theorem general_column (matrix : UpperTriangularGroup ι R) (row col : ι) :
    (UpperTriangularGroup.unipotentPart matrix).1 row col = matrix.1 row col *
      (((DiagonalGroup.unitsEquiv (UpperTriangularGroup.diagonal matrix) col)⁻¹ : Rˣ) : R) :=
  UpperTriangularGroup.unipotentPart_apply matrix row col

private theorem general_action (diag : DiagonalGroup ι R)
    (unit : UnitriangularGroup ι R) (row col : ι) :
    (UpperTriangularGroup.diagonalAction diag unit).1 row col =
      (DiagonalGroup.unitsEquiv diag row : Rˣ) * unit.1 row col *
        (((DiagonalGroup.unitsEquiv diag col)⁻¹ : Rˣ) : R) :=
  UpperTriangularGroup.diagonalAction_apply diag unit row col

private theorem general_naturality (ringHom : R →+* S)
    (coords : UnitriangularGroup ι R ⋊[UpperTriangularGroup.diagonalAction]
      DiagonalGroup ι R) :
    UpperTriangularGroup.map ringHom (UpperTriangularGroup.semidirEquiv coords) =
      UpperTriangularGroup.semidirEquiv (UpperTriangularGroup.semidirMap ringHom coords) :=
  UpperTriangularGroup.semidirEquiv_map ringHom coords

private theorem general_inverse_naturality (ringHom : R →+* S)
    (matrix : UpperTriangularGroup ι R) :
    UpperTriangularGroup.semidirMap ringHom (UpperTriangularGroup.semidirEquiv.symm matrix) =
      UpperTriangularGroup.semidirEquiv.symm (UpperTriangularGroup.map ringHom matrix) :=
  UpperTriangularGroup.semidirEquiv_symm_map ringHom matrix

private theorem general_section_naturality (ringHom : R →+* S)
    (diag : DiagonalGroup ι R) :
    UpperTriangularGroup.map ringHom (UpperTriangularGroup.diagonalSection diag) =
      UpperTriangularGroup.diagonalSection (DiagonalGroup.map ringHom diag) :=
  UpperTriangularGroup.diagonalSection_map ringHom diag

private theorem general_projection_naturality (ringHom : R →+* S)
    (matrix : UpperTriangularGroup ι R) :
    UpperTriangularGroup.diagonal (UpperTriangularGroup.map ringHom matrix) =
      DiagonalGroup.map ringHom (UpperTriangularGroup.diagonal matrix) :=
  UpperTriangularGroup.diagonal_map ringHom matrix

private theorem general_inclusion_naturality (ringHom : R →+* S)
    (unit : UnitriangularGroup ι R) :
    UpperTriangularGroup.map ringHom (UnitriangularGroup.inUpperTriangular unit) =
      UnitriangularGroup.inUpperTriangular (UnitriangularGroup.map ringHom unit) :=
  UnitriangularGroup.inUpperTriangular_map ringHom unit

private theorem general_splitting (diag : DiagonalGroup ι R) :
    UpperTriangularGroup.diagonal (UpperTriangularGroup.diagonalSection diag) = diag :=
  UpperTriangularGroup.diagonal_section diag

private theorem general_factorization (matrix : UpperTriangularGroup ι R) :
    UnitriangularGroup.inUpperTriangular (UpperTriangularGroup.unipotentPart matrix) *
      UpperTriangularGroup.diagonalSection (UpperTriangularGroup.diagonal matrix) =
        matrix :=
  UpperTriangularGroup.unipotentPart_factor matrix

private theorem general_two_triangles
    (coords : UnitriangularGroup ι R ⋊[UpperTriangularGroup.diagonalAction]
      DiagonalGroup ι R) (matrix : UpperTriangularGroup ι R) :
    UpperTriangularGroup.semidirEquiv.symm (UpperTriangularGroup.semidirEquiv coords) =
        coords ∧
      UpperTriangularGroup.semidirEquiv (UpperTriangularGroup.semidirEquiv.symm matrix) =
        matrix :=
  ⟨MulEquiv.symm_apply_apply _ coords, MulEquiv.apply_symm_apply _ matrix⟩

private theorem general_action_naturality (ringHom : R →+* S)
    (diag : DiagonalGroup ι R) (unit : UnitriangularGroup ι R) :
    UnitriangularGroup.map ringHom (UpperTriangularGroup.diagonalAction diag unit) =
      UpperTriangularGroup.diagonalAction (DiagonalGroup.map ringHom diag)
        (UnitriangularGroup.map ringHom unit) :=
  UpperTriangularGroup.diagonalAction_map ringHom diag unit

variable {Coeff : Type} [CommRing Coeff]

private theorem fin0_upper_trivial (left right : UpperTriangularGroup (Fin 0) Coeff) :
    left = right := by
  apply UpperTriangularGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_diagonal_trivial (left right : DiagonalGroup (Fin 0) Coeff) :
    left = right := by
  apply DiagonalGroup.ext
  intro row
  exact Fin.elim0 row

private theorem fin0_unitriangular_trivial (left right : UnitriangularGroup (Fin 0) Coeff) :
    left = right := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_semidirect_trivial (left right :
    UnitriangularGroup (Fin 0) Coeff ⋊[UpperTriangularGroup.diagonalAction]
      DiagonalGroup (Fin 0) Coeff) : left = right := by
  apply SemidirectProduct.ext
  · exact fin0_unitriangular_trivial _ _
  · exact fin0_diagonal_trivial _ _

private theorem fin1_unitriangular_trivial (unit : UnitriangularGroup (Fin 1) Coeff) :
    unit = 1 := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row col
  fin_cases row
  fin_cases col
  simpa using unit.2.2 0

private def fin1_upper_diagonal_equiv :
    UpperTriangularGroup (Fin 1) Coeff ≃* DiagonalGroup (Fin 1) Coeff :=
  MulEquiv.ofBijective UpperTriangularGroup.diagonal (by
    constructor
    · intro left right equal
      apply UpperTriangularGroup.ext
      intro row col
      have same : row = col := Subsingleton.elim row col
      subst col
      have entries := congrArg (fun diag : DiagonalGroup (Fin 1) Coeff =>
        diag.1 row row) equal
      simpa [UpperTriangularGroup.diagonal_apply_diag] using entries
    · exact UpperTriangularGroup.diagonal_surjective)

private theorem fin2_column (matrix : UpperTriangularGroup (Fin 2) Coeff) :
    (UpperTriangularGroup.unipotentPart matrix).1 0 1 = matrix.1 0 1 *
      (((DiagonalGroup.unitsEquiv (UpperTriangularGroup.diagonal matrix) 1)⁻¹ : Coeffˣ) : Coeff) :=
  UpperTriangularGroup.unipotentPart_apply matrix 0 1

private theorem fin2_action (diag : DiagonalGroup (Fin 2) Coeff)
    (unit : UnitriangularGroup (Fin 2) Coeff) :
    (UpperTriangularGroup.diagonalAction diag unit).1 0 1 =
      (DiagonalGroup.unitsEquiv diag 0 : Coeffˣ) * unit.1 0 1 *
        (((DiagonalGroup.unitsEquiv diag 1)⁻¹ : Coeffˣ) : Coeff) :=
  UpperTriangularGroup.diagonalAction_apply diag unit 0 1

private theorem fin2_section_projection (diag : DiagonalGroup (Fin 2) Coeff) :
    UpperTriangularGroup.diagonal (UpperTriangularGroup.diagonalSection diag) = diag :=
  UpperTriangularGroup.diagonal_section diag

private theorem fin2_product (first second :
    UnitriangularGroup (Fin 2) Coeff ⋊[UpperTriangularGroup.diagonalAction]
      DiagonalGroup (Fin 2) Coeff) :
    UnitriangularGroup.inUpperTriangular first.left *
        UpperTriangularGroup.diagonalSection first.right *
        (UnitriangularGroup.inUpperTriangular second.left *
          UpperTriangularGroup.diagonalSection second.right) =
      UnitriangularGroup.inUpperTriangular
          (first.left * UpperTriangularGroup.diagonalAction first.right second.left) *
        UpperTriangularGroup.diagonalSection (first.right * second.right) :=
  UpperTriangularGroup.semidirEquiv_mul_formula first second

private theorem zero_ring_fin2 (matrix : UpperTriangularGroup (Fin 2) (ZMod 1)) :
    matrix = 1 := by
  apply UpperTriangularGroup.ext
  intro row col
  exact Subsingleton.elim _ _

private theorem zero_ring_fin0 (matrix : UpperTriangularGroup (Fin 0) (ZMod 1)) :
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

private def dualDiagonal : DiagonalGroup (Fin 2) (DualNumber ℤ) :=
  (DiagonalGroup.unitsEquiv (R := DualNumber ℤ)).symm
    (fun row => if row = 0 then dualUnit else 1)

private def dualUpperOne : UnitriangularGroup (Fin 2) (DualNumber ℤ) :=
  ⟨GeneralLinearGroup.elementaryUnit 0 1 (by decide) 1, by
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
    (UpperTriangularGroup.diagonalAction dualDiagonal dualUpperOne).1 0 1 =
      1 + DualNumber.eps := by
  rw [UpperTriangularGroup.diagonalAction_apply, dual_upper_entry]
  simp [dualDiagonal, dualUnit]

private theorem dual_epsilon_nonzero :
    (UpperTriangularGroup.diagonalAction dualDiagonal dualUpperOne).1 0 1 ≠
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
    UnitriangularGroup (Fin 2) ℤ ⋊[UpperTriangularGroup.diagonalAction]
      DiagonalGroup (Fin 2) ℤ) :
    UpperTriangularGroup.map quotientHom (UpperTriangularGroup.semidirEquiv coords) =
      UpperTriangularGroup.semidirEquiv
        (UpperTriangularGroup.semidirMap quotientHom coords) :=
  UpperTriangularGroup.semidirEquiv_map quotientHom coords

end AlgebraicGroupsTest.UpperTriangular
