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

example : (TauCeti.SpecialLinear.definingHopfIdeal K (Fintype.card n)).toIdeal.IsHopfIdeal K :=
  inferInstance

example (i j : n) : polynomialEquiv K n
      ((Ideal.Quotient.mkₐ K (polynomialIdeal K n)) (MvPolynomial.X ((Fintype.equivFin n) i,
        (Fintype.equivFin n) j))) =
    (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) := by
  change polynomialQuotientToCoordinateRing K n
    ((Ideal.Quotient.mkₐ K (polynomialIdeal K n))
      (MvPolynomial.X ((Fintype.equivFin n) i, (Fintype.equivFin n) j))) = _
  rw [← AlgHom.comp_apply, polynomialQuotientToCoordinateRing_comp_quotient]
  simp only [polynomialToCoordinateRing, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    TauCeti.GeneralLinear.reindexedGenericMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, TauCeti.GeneralLinear.genericMatrix_apply]
  rfl

example : Matrix.det
    (fun i j ↦ (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) :
        Matrix n n (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) = 1 :=
by
  have h := RingHom.map_det
    (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom.toRingHom
    (TauCeti.GeneralLinear.reindexedGenericMatrix K n)
  change (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
    (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det = _ at h
  rw [generalLinearReindexedGenericMatrix_det,
    TauCeti.SpecialLinear.coordinateMap_determinantGroupLike] at h
  exact h.symm

example : CategoryTheory.IsPullback
    (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom.left
    ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).hom
    (generalLinearDeterminantSchemeHom K n).hom.hom.left
    η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X].left :=
  specialLinearDeterminantSquare_isPullback K n

example : CategoryTheory.IsPullback
    (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)) (0 : _ ⟶ Grp.trivial (Over (Spec (.of
      K))))
    (generalLinearDeterminantSchemeHom K n) (0 : Grp.trivial (Over (Spec (.of K))) ⟶ _) :=
  specialLinearDeterminantSquare_isPullback_group K n

variable (R : Type u) [CommRing R] [Algebra K R]

example (s : Matrix.SpecialLinearGroup n R) (i j : n) :
    ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n R).symm s).ofConv
      ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j)) = s i j :=
  TauCeti.SpecialLinear.reindexedPointsMulEquiv_symm_apply K n R s i j

example (s : Matrix.SpecialLinearGroup n R) :
    ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n R).symm.trans
      (TauCeti.SpecialLinear.groupSchemePointMulEquiv (R := K) (Fintype.card n) R)) s ≫
        (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom =
      ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm.trans
        (TauCeti.GeneralLinear.groupSchemePointMulEquiv (R := K) (Fintype.card n) R))
          (Matrix.SpecialLinearGroup.toGL s) :=
  TauCeti.SpecialLinear.reindexedSchemePoint_comp_groupSchemeι K n R s

example (H : Grp (Over (Spec (.of K))))
    (f : H ⟶ TauCeti.GeneralLinear.groupScheme K (Fintype.card n))
    (hf : f ≫ generalLinearDeterminantSchemeHom K n =
      CartesianMonoidalCategory.toUnit H ≫
        (0 : Grp.trivial (Over (Spec (.of K))) ⟶ _)) :
    ∃! lift : H ⟶ TauCeti.SpecialLinear.groupScheme K (Fintype.card n),
      lift ≫ TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n) = f :=
  specialLinearGroupKernel_universal K n H f hf

example : Matrix.SpecialLinearGroup (Fin 0) (ZMod 1) ≃*
      WithConv (TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 0 →ₐ[ℤ] ZMod 1) :=
  (TauCeti.SpecialLinear.reindexedPointsMulEquiv ℤ (Fin 0) (ZMod 1)).symm

example : Matrix.SpecialLinearGroup (Fin 0) ℤ ≃*
      WithConv (TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 0 →ₐ[ℤ] ℤ) :=
  (TauCeti.SpecialLinear.reindexedPointsMulEquiv ℤ (Fin 0) ℤ).symm

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

example : ((TauCeti.SpecialLinear.reindexedPointsMulEquiv ℤ (Fin 2) ℤ).symm shear).ofConv
      ((TauCeti.SpecialLinear.coordinateMap ℤ 2).hom
        (TauCeti.GeneralLinear.reindexedGenericMatrix ℤ (Fin 2) 0 1)) = 1 := by
  erw [TauCeti.SpecialLinear.reindexedPointsMulEquiv_symm_apply]
  norm_num [shear, Matrix.SpecialLinearGroup.transvection_coe]

end AlgebraicGroupsTest.SpecialLinear

#lint
