/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangular
public import GeneralLinearGroups.Elementary
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import checks for the upper-triangular group scheme -/

@[expose] public section

noncomputable section

namespace AlgebraicGroupsTest.UpperTriangularScheme

open CategoryTheory AlgebraicGeometry UpperTriangularCoordinateRing
open scoped CategoryTheory.MonObj DualNumber

variable (K : Type) [CommRing K]

private theorem general_from_natural (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularFromGL K n S (Matrix.UpperTriangularGroup.map v.toRingHom s) =
      v.comp (upperTriangularFromGL K n R s) :=
  upperTriangularFromGL_natural K n R v s

private theorem general_to_natural (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (f : CoordinateRing K n →ₐ[K] R) :
    upperTriangularToGL K n S (v.comp f) =
      Matrix.UpperTriangularGroup.map v.toRingHom (upperTriangularToGL K n R f) :=
  upperTriangularToGL_natural K n R v f

private theorem general_points_natural (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) :
    (upperTriangularGroupFunctor K n).map (CommAlgCat.ofHom v) ≫
      (upperTriangularGroupPointsIso K n).hom.app (CommAlgCat.of K S) =
    (upperTriangularGroupPointsIso K n).hom.app (CommAlgCat.of K R) ≫
      (upperTriangularGroupPointsFunctor K n).map (CommAlgCat.ofHom v) :=
  (upperTriangularGroupPointsIso K n).hom.naturality (CommAlgCat.ofHom v)

private theorem general_points_multiplicative (n : Type) [Fintype n] [LinearOrder n]
    (R : Type) [CommRing R] [Algebra K R]
    (s t : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R (s * t) =
      upperTriangularGroupMulEquivPoints K n R s *
        upperTriangularGroupMulEquivPoints K n R t :=
  (upperTriangularGroupMulEquivPoints K n R).map_mul s t

private theorem general_inclusion (n : Type) [Fintype n] [LinearOrder n]
    (R : Type) [CommRing R] [Algebra K R] (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R s ≫
      (upperTriangularInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R (Matrix.UpperTriangularGroup.inclusion s) :=
  upperTriangularInclusion_point K n R s

private theorem general_lower (n : Type) [Fintype n] [LinearOrder n]
    (i j : n) (h : j < i) :
    quotient K n (GeneralLinearCoordinateRing.matrix K n i j) = 0 :=
  quotient_lower K n i j h

private theorem general_universal (n : Type) [Fintype n] [LinearOrder n]
    (i j : n) :
    (universal K n).1 i j =
      quotient K n (GeneralLinearCoordinateRing.matrix K n i j) :=
  universal_apply K n i j

private theorem general_determinant_inverse (n : Type) [Fintype n] [LinearOrder n] :
    quotient K n (GeneralLinearCoordinateRing.detInverse K n) *
      (∏ i, quotient K n (GeneralLinearCoordinateRing.matrix K n i i)) = 1 :=
  universal_detInverse K n

private theorem fin0_point (R : Type) [CommRing R]
    (s : Matrix.UpperTriangularGroup (Fin 0) R) : s = 1 := by
  apply Matrix.UpperTriangularGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_representation (R : Type) [CommRing R] [Algebra K R]
    (s : Matrix.UpperTriangularGroup (Fin 0) R) :
    (upperTriangularGroupMulEquivPoints K (Fin 0) R).symm
      (upperTriangularGroupMulEquivPoints K (Fin 0) R s) = 1 := by
  simpa using fin0_point R s

private theorem fin1_diagonal (R : Type) [CommRing R]
    (s : Matrix.UpperTriangularGroup (Fin 1) R) :
    Matrix.UpperTriangularGroup.diagonalSection (Matrix.UpperTriangularGroup.diagonal s) =
      s := by
  apply Matrix.UpperTriangularGroup.ext
  intro row col
  fin_cases row
  fin_cases col
  exact Matrix.UpperTriangularGroup.diagonal_apply_diag s 0

private def fin2_shear (R : Type) [CommRing R] (a : R) :
    Matrix.UpperTriangularGroup (Fin 2) R :=
  ⟨Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a, by
    change (1 + Matrix.single (0 : Fin 2) 1 a : Matrix (Fin 2) (Fin 2) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add
      (Matrix.blockTriangular_single (by decide : (0 : Fin 2) ≤ 1) _)⟩

private theorem fin2_shear_entry (R : Type) [CommRing R] (a : R) :
    (fin2_shear R a).1 0 1 = a := by
  simp [fin2_shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private def fin2_diagonal (R : Type) [CommRing R] (first second : Rˣ) :
    Matrix.UpperTriangularGroup (Fin 2) R :=
  Matrix.UpperTriangularGroup.diagonalSection
    ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
      (Fin 2 → Rˣ)).symm (fun i => if i = 0 then first else second))

private theorem fin2_diagonal_first (R : Type) [CommRing R] (first second : Rˣ) :
    (fin2_diagonal R first second).1 0 0 = first := by
  change ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
    (Fin 2 → Rˣ)).symm (fun i => if i = 0 then first else second)).1 0 0 = first
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private theorem fin2_diagonal_second (R : Type) [CommRing R] (first second : Rˣ) :
    (fin2_diagonal R first second).1 1 1 = second := by
  change ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
    (Fin 2 → Rˣ)).symm (fun i => if i = 0 then first else second)).1 1 1 = second
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply]

private def fin2_element (R : Type) [CommRing R] (first second : Rˣ) (a : R) :
    Matrix.UpperTriangularGroup (Fin 2) R :=
  fin2_shear R a * fin2_diagonal R first second

private theorem fin2_element_upper (R : Type) [CommRing R]
    (first second : Rˣ) (a : R) :
    (fin2_element R first second a).1 0 1 = a * second := by
  change ((fin2_shear R a).1 * (fin2_diagonal R first second).1 :
    Matrix (Fin 2) (Fin 2) R) 0 1 = _
  have hzero : (fin2_diagonal R first second).1 0 1 = 0 := by
    change ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
      (Fin 2 → Rˣ)).symm (fun i => if i = 0 then first else second)).1 0 1 = 0
    exact (Matrix.DiagonalGroup.unitsEquiv.symm
      (fun i : Fin 2 => if i = 0 then first else second)).2 0 1 (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_two, hzero, mul_zero, zero_add,
    fin2_shear_entry, fin2_diagonal_second]

private theorem fin2_shear_point (R : Type) [CommRing R] [Algebra K R] (a : R) :
    (upperTriangularGroupMulEquivAlgHom K (Fin 2) R (fin2_shear R a)).ofConv
      (quotient K (Fin 2) (GeneralLinearCoordinateRing.matrix K (Fin 2) 0 1)) = a := by
  rw [upperTriangularGroupMulEquivAlgHom_entry, fin2_shear_entry]

private theorem fin2_element_point (R : Type) [CommRing R] [Algebra K R]
    (first second : Rˣ) (a : R) :
    (upperTriangularGroupMulEquivAlgHom K (Fin 2) R
      (fin2_element R first second a)).ofConv
      (quotient K (Fin 2) (GeneralLinearCoordinateRing.matrix K (Fin 2) 0 1)) =
        a * second := by
  rw [upperTriangularGroupMulEquivAlgHom_entry, fin2_element_upper]

private theorem fin2_detInverse (R : Type) [CommRing R] [Algebra K R] (a : R) :
    (upperTriangularGroupMulEquivAlgHom K (Fin 2) R (fin2_shear R a)).ofConv
      (quotient K (Fin 2) (GeneralLinearCoordinateRing.detInverse K (Fin 2))) =
        ↑(Matrix.GeneralLinearGroup.det (fin2_shear R a).1)⁻¹ :=
  upperTriangularGroupMulEquivAlgHom_detInverse K (Fin 2) R _

private theorem zero_ring_fin0 :
    Algebra.FiniteType (ZMod 1) (CoordinateRing (ZMod 1) (Fin 0)) := inferInstance

private theorem zero_ring_fin2 :
    Algebra.FiniteType (ZMod 1) (CoordinateRing (ZMod 1) (Fin 2)) := inferInstance

private theorem zero_ring_fin0_point (s : Matrix.UpperTriangularGroup (Fin 0) (ZMod 1)) :
    s = 1 := fin0_point _ s

private theorem zero_ring_fin2_point (s : Matrix.UpperTriangularGroup (Fin 2) (ZMod 1)) :
    s = 1 := by
  apply Matrix.UpperTriangularGroup.ext
  intro row col
  exact Subsingleton.elim _ _

private theorem zero_ring_fin0_inclusion
    (s : Matrix.UpperTriangularGroup (Fin 0) (ZMod 1)) :
    upperTriangularGroupMulEquivPoints (ZMod 1) (Fin 0) (ZMod 1) s ≫
      (upperTriangularInclusion (ZMod 1) (Fin 0)).hom.hom =
      generalLinearGroupMulEquivPoints (ZMod 1) (Fin 0) (ZMod 1) s.1 :=
  upperTriangularInclusion_point (ZMod 1) (Fin 0) (ZMod 1) s

private theorem zero_ring_fin2_inclusion
    (s : Matrix.UpperTriangularGroup (Fin 2) (ZMod 1)) :
    upperTriangularGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1) s ≫
      (upperTriangularInclusion (ZMod 1) (Fin 2)).hom.hom =
      generalLinearGroupMulEquivPoints (ZMod 1) (Fin 2) (ZMod 1) s.1 :=
  upperTriangularInclusion_point (ZMod 1) (Fin 2) (ZMod 1) s

private theorem zero_ring_fin0_detInverse :
    quotient (ZMod 1) (Fin 0)
      (GeneralLinearCoordinateRing.detInverse (ZMod 1) (Fin 0)) = 1 := by
  have h := universal_detInverse (ZMod 1) (Fin 0)
  simpa using h

private theorem epsilon_nonzero : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro h
  have hs := congrArg TrivSqZeroExt.snd h
  norm_num at hs

private theorem epsilon_square : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by simp

private theorem epsilon_upper_nonzero :
    (fin2_shear (DualNumber ℤ) DualNumber.eps).1 0 1 ≠ 0 := by
  rw [fin2_shear_entry]
  exact epsilon_nonzero

private theorem epsilon_upper_point :
    (upperTriangularGroupMulEquivAlgHom ℤ (Fin 2) (DualNumber ℤ)
      (fin2_shear (DualNumber ℤ) DualNumber.eps)).ofConv
      (quotient ℤ (Fin 2) (GeneralLinearCoordinateRing.matrix ℤ (Fin 2) 0 1)) =
        DualNumber.eps :=
  fin2_shear_point ℤ (DualNumber ℤ) DualNumber.eps

private theorem epsilon_element_upper :
    (fin2_element (DualNumber ℤ) 1 1 DualNumber.eps).1 0 1 = DualNumber.eps := by
  simpa using fin2_element_upper (DualNumber ℤ) 1 1 DualNumber.eps

private theorem reduction_noninjective :
    ¬ Function.Injective (Algebra.ofId ℤ (ZMod 1)) := by
  intro injective
  have equal : (0 : ℤ) = 1 := injective (Subsingleton.elim _ _)
  norm_num at equal

private theorem reduction_natural (s : Matrix.UpperTriangularGroup (Fin 2) ℤ) :
    upperTriangularFromGL ℤ (Fin 2) (ZMod 1)
      (Matrix.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s) =
      (Algebra.ofId ℤ (ZMod 1)).comp (upperTriangularFromGL ℤ (Fin 2) ℤ s) :=
  upperTriangularFromGL_natural ℤ (Fin 2) ℤ (Algebra.ofId ℤ (ZMod 1)) s

private theorem reduction_points_natural :
    (upperTriangularGroupFunctor ℤ (Fin 2)).map
      (CommAlgCat.ofHom (Algebra.ofId ℤ (ZMod 1))) ≫
        (upperTriangularGroupPointsIso ℤ (Fin 2)).hom.app (CommAlgCat.of ℤ (ZMod 1)) =
    (upperTriangularGroupPointsIso ℤ (Fin 2)).hom.app (CommAlgCat.of ℤ ℤ) ≫
      (upperTriangularGroupPointsFunctor ℤ (Fin 2)).map
        (CommAlgCat.ofHom (Algebra.ofId ℤ (ZMod 1))) :=
  general_points_natural ℤ (Fin 2) ℤ (ZMod 1) (Algebra.ofId ℤ (ZMod 1))

end AlgebraicGroupsTest.UpperTriangularScheme
