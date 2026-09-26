/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinearKernel

/-!
# External clients of the finite special linear group scheme

Exercises the determinant-one Hopf quotient, degenerate finite index and coefficient
rings, a nontrivial shear, affine `Spec` points, and actual scheme/group-scheme
kernel pullbacks without importing source-specific research.
-/

public section

noncomputable section

open AlgebraicGeometry SpecialLinearCoordinateRing CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGroupsTest.SpecialLinear

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

example : (determinantOneIdeal K n).IsHopfIdeal K := inferInstance

example (i j : n) : polynomialEquiv K n
      ((Ideal.Quotient.mkₐ K (polynomialIdeal K n)) (MvPolynomial.X (i, j))) =
    entry K n i j := polynomialEquiv_variable K n i j

example : Matrix.det
    (fun i j ↦ entry K n i j : Matrix n n (CoordinateRing K n)) = 1 :=
  determinant_entry K n

example : CategoryTheory.IsPullback
    (specialLinearInclusion K n).hom.hom.left
    (specialLinearGroupUnderlyingScheme K n).hom
    (generalLinearDeterminantSchemeHom K n).hom.hom.left
    η[multiplicativeGroupUnderlyingScheme K].left :=
  specialLinearDeterminantSquare_isPullback K n

example : CategoryTheory.IsPullback
    (specialLinearInclusion K n) (specialLinearToTrivialGroupHom K n)
    (generalLinearDeterminantSchemeHom K n) (multiplicativeUnitGroupHom K) :=
  specialLinearDeterminantSquare_isPullback_group K n

variable (R : Type u) [CommRing R] [Algebra K R]

example (s : Matrix.SpecialLinearGroup n R) (i j : n) :
    (specialLinearGroupMulEquivAlgHom K n R s).ofConv (entry K n i j) = s i j :=
  specialLinearGroupMulEquivAlgHom_entry K n R s i j

example (s : Matrix.SpecialLinearGroup n R) :
    specialLinearGroupMulEquivPoints K n R s ≫ (specialLinearInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R (Matrix.SpecialLinearGroup.toGL s) :=
  specialLinearInclusion_point K n R s

example (H : Grp (Over (Spec (.of K))))
    (f : H ⟶ generalLinearGroupScheme K n)
    (hf : f ≫ generalLinearDeterminantSchemeHom K n =
      CartesianMonoidalCategory.toUnit H ≫ multiplicativeUnitGroupHom K) :
    ∃! lift : H ⟶ specialLinearGroupScheme K n,
      lift ≫ specialLinearInclusion K n = f :=
  specialLinearGroupKernel_universal K n H f hf

example : Matrix.SpecialLinearGroup (Fin 0) (ZMod 1) ≃*
      WithConv (CoordinateRing ℤ (Fin 0) →ₐ[ℤ] ZMod 1) :=
  specialLinearGroupMulEquivAlgHom ℤ (Fin 0) (ZMod 1)

example : Matrix.SpecialLinearGroup (Fin 0) ℤ ≃*
      WithConv (CoordinateRing ℤ (Fin 0) →ₐ[ℤ] ℤ) :=
  specialLinearGroupMulEquivAlgHom ℤ (Fin 0) ℤ

/-- A determinant-one integer shear, not the identity matrix. -/
def shear : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  Matrix.SpecialLinearGroup.transvection
    (show (0 : Fin 2) ≠ 1 by decide) 1

theorem shear_ne_one : shear ≠ 1 := by
  intro equality
  have entryEquality := congrArg
    (fun s : Matrix.SpecialLinearGroup (Fin 2) ℤ ↦ s 0 1) equality
  norm_num [shear, Matrix.SpecialLinearGroup.transvection_coe] at entryEquality

theorem shear_coefficient_map_ne_one :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 5)) shear ≠ 1 := by
  intro equality
  have entryEquality := congrArg
    (fun s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ↦ s 0 1) equality
  norm_num [shear, Matrix.SpecialLinearGroup.transvection_coe] at entryEquality
  exact (by decide : (1 : ZMod 5) ≠ 0) entryEquality

example : (specialLinearGroupMulEquivAlgHom ℤ (Fin 2) ℤ shear).ofConv
      (entry ℤ (Fin 2) 0 1) = 1 := by
  rw [specialLinearGroupMulEquivAlgHom_entry]
  norm_num [shear, Matrix.SpecialLinearGroup.transvection_coe]

end AlgebraicGroupsTest.SpecialLinear

#lint
