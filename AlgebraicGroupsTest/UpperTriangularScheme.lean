/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import GeneralLinearGroups.Elementary
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import checks for the upper-triangular group scheme -/

@[expose] public section

noncomputable section

namespace AlgebraicGroupsTest.UpperTriangularScheme

open CategoryTheory AlgebraicGeometry TauCeti.GeneralLinear.UpperTriangular
open scoped CategoryTheory.MonObj DualNumber

variable (K : Type) [CommRing K]

private theorem general_from_natural (n : ℕ)
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : TauCeti.upperTriangularGroup (Fin n) R) :
    ((pointsMulEquiv (R := K) (n := n) (A := S)).symm
      (TauCeti.UpperTriangularGroup.map v.toRingHom s)).ofConv =
      v.comp ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s).ofConv := by
  apply congrArg WithConv.ofConv
  apply (pointsMulEquiv (R := K) (n := n) (A := S)).injective
  rw [MulEquiv.apply_symm_apply]
  change _ = (pointsMulEquiv (R := K) (n := n) (A := S))
    (WithConv.toConv (v.comp ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s).ofConv))
  rw [pointsMulEquiv_mapValue K n, MulEquiv.apply_symm_apply]

private theorem general_to_natural (n : ℕ)
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (f : coordinateHopfAlgebra K n →ₐ[K] R) :
    pointsMulEquiv (R := K) (n := n) (A := S) (WithConv.toConv (v.comp f)) =
      TauCeti.UpperTriangularGroup.map v.toRingHom
        (pointsMulEquiv (R := K) (n := n) (A := R) (WithConv.toConv f)) :=
  pointsMulEquiv_mapValue K n v _

private theorem general_points_natural (n : ℕ)
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) :
    (TauCeti.HopfAlgebra.pointsFunctor (R := K) (H := coordinateHopfAlgebra K n)).map
        (CommAlgCat.ofHom v) ≫ (pointsNatIso (R := K) n).hom.app (CommAlgCat.of K S) =
      (pointsNatIso (R := K) n).hom.app (CommAlgCat.of K R) ≫
        (upperTriangularFunctor (R := K) n).map (CommAlgCat.ofHom v) :=
  (pointsNatIso (R := K) n).hom.naturality (CommAlgCat.ofHom v)

private theorem general_points_multiplicative (n : ℕ)
    (R : Type) [CommRing R] [Algebra K R]
    (s t : TauCeti.upperTriangularGroup (Fin n) R) :
    (pointsMulEquiv (R := K) (n := n) (A := R)).symm (s * t) =
      (pointsMulEquiv (R := K) (n := n) (A := R)).symm s *
        (pointsMulEquiv (R := K) (n := n) (A := R)).symm t :=
  (pointsMulEquiv (R := K) (n := n) (A := R)).symm.map_mul s t

private theorem general_inclusion (n : ℕ)
    (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.upperTriangularGroup (Fin n) R) :
    Spec.mapMulEquiv (R := K) (S := coordinateHopfAlgebra K n) (T := R)
        ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s) ≫
      (inclusion K n).hom.hom =
      TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) R
        (TauCeti.GeneralLinear.groupScheme_def K n)
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := K) n).symm s.1) := by
  have h := TauCeti.CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain R
    (TauCeti.GeneralLinear.groupScheme_def K n)
    (show groupScheme K n = (hopfSpec (.of K)).obj (.op (coordinateHopfAlgebra K n)) by rfl)
    (TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) R
        (TauCeti.GeneralLinear.groupScheme_def K n))
    (Spec.mapMulEquiv (R := K) (S := coordinateHopfAlgebra K n) (T := R))
    (fun f => TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) R
      (TauCeti.GeneralLinear.groupScheme_def K n)
      (TauCeti.GeneralLinear.groupScheme_X_left K n) f)
    (fun _ => by rfl) (coordinateMap K n)
    ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s)
  have hp : (CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap K n)).app
      (CommAlgCat.of K R) ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s) =
      (TauCeti.GeneralLinear.pointsMulEquiv (R := K) n).symm s.1 := by
    rw [coordinateMap_def]
    exact quotientPointsHom_pointsMulEquiv_symm K n s
  rw [hp] at h
  have hi : (hopfSpec (.of K)).map (coordinateMap K n).op ≫
      eqToHom (TauCeti.GeneralLinear.groupScheme_def K n).symm = inclusion K n := by
    rw [inclusion, TauCeti.GeneralLinear.weightParabolicInclusion_def,
      TauCeti.CommHopfAlgCat.quotientSpecι_def, coordinateMap_def]
  simp only [eqToHom_refl, Category.id_comp] at h
  rw [hi] at h
  exact h


private theorem point_entry (n : ℕ) (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.upperTriangularGroup (Fin n) R) (i j : Fin n) :
    ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s).ofConv
      ((coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i j)) =
      s.1 i j := by
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) R => g i j)
    (pointsMulEquiv_coe K n ((pointsMulEquiv (R := K) (n := n) (A := R)).symm s))
  erw [TauCeti.GeneralLinear.pointToGeneralLinear_apply,
    TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply] at h
  rw [coordinateMap_apply]
  simpa only [
    MulEquiv.apply_symm_apply, TauCeti.GeneralLinear.genericMatrix_apply,
    ] using h

private theorem general_lower (n : ℕ) (i j : Fin n) (hji : j < i) :
    (coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i j) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [definingHopfIdeal_toIdeal]
  apply Ideal.subset_span
  exact (mem_definingRelationSet_iff K n _).mpr ⟨i, j, hji, by
    rw [TauCeti.GeneralLinear.genericMatrix_apply]⟩

private theorem general_universal (n : ℕ) (i j : Fin n) :
    (pointsMulEquiv (R := K) (n := n) (A := coordinateHopfAlgebra K n)
      (WithConv.toConv (AlgHom.id K (coordinateHopfAlgebra K n)))).1 i j =
      (coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i j) := by
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (coordinateHopfAlgebra K n)
    => g i j) (pointsMulEquiv_coe K n (WithConv.toConv (AlgHom.id K
      (coordinateHopfAlgebra K n))))
  erw [TauCeti.GeneralLinear.pointToGeneralLinear_apply,
    TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply] at h
  rw [coordinateMap_apply]
  simpa only [
    TauCeti.GeneralLinear.genericMatrix_apply,
    WithConv.ofConv_toConv, AlgHom.id_apply] using h.symm

private theorem general_determinant_inverse (n : ℕ) :
    (coordinateMap K n).hom (Ring.inverse (TauCeti.GeneralLinear.genericMatrix K n).det) *
      (∏ i, (coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i i)) = 1 := by
  let q := (coordinateMap K n).hom.toAlgHom
  have hd : q (TauCeti.GeneralLinear.genericMatrix K n).det =
      ∏ i, q (TauCeti.GeneralLinear.genericMatrix K n i i) := by
    rw [AlgHom.map_det]
    apply Matrix.det_of_isUpperTriangular
    intro i j hji
    exact general_lower K n i j hji
  change q (Ring.inverse (TauCeti.GeneralLinear.genericMatrix K n).det) *
    (∏ i, q (TauCeti.GeneralLinear.genericMatrix K n i i)) = 1
  rw [(TauCeti.GeneralLinear.isUnit_det_genericMatrix K n).map_ringInverse q, ← hd]
  exact Ring.inverse_mul_cancel _ ((TauCeti.GeneralLinear.isUnit_det_genericMatrix K n).map q)

private theorem fin0_point (R : Type) [CommRing R]
    (s : TauCeti.upperTriangularGroup (Fin 0) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Fin.elim0 row

private theorem fin0_representation (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.upperTriangularGroup (Fin 0) R) :
    ((pointsMulEquiv (R := K) (n := 0) (A := R)).symm).symm
      ((pointsMulEquiv (R := K) (n := 0) (A := R)).symm s) = 1 := by
  simpa using fin0_point R s

private theorem fin1_diagonal (R : Type) [CommRing R]
    (s : TauCeti.upperTriangularGroup (Fin 1) R) :
    TauCeti.UpperTriangularGroup.diagonalHom (TauCeti.UpperTriangularGroup.diag s) = s := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row
  fin_cases col
  simp [TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_apply,
    TauCeti.UpperTriangularGroup.diag_apply_val]

private def fin2_shear (R : Type) [CommRing R] (a : R) :
    TauCeti.upperTriangularGroup (Fin 2) R :=
  ⟨Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a, by
    apply TauCeti.UpperTriangularGroup.mem_iff.mpr
    change (1 + Matrix.single (0 : Fin 2) 1 a : Matrix (Fin 2) (Fin 2) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add
      (Matrix.blockTriangular_single (by decide : (0 : Fin 2) ≤ 1) _)⟩

private theorem fin2_shear_entry (R : Type) [CommRing R] (a : R) :
    (fin2_shear R a).1 0 1 = a := by
  simp [fin2_shear, Matrix.GeneralLinearGroup.elementaryUnit_val, Matrix.add_apply]

private def fin2_diagonal (R : Type) [CommRing R] (first second : Rˣ) :
    TauCeti.upperTriangularGroup (Fin 2) R :=
  TauCeti.UpperTriangularGroup.diagonalHom (fun i => if i = 0 then first else second)

private theorem fin2_diagonal_first (R : Type) [CommRing R] (first second : Rˣ) :
    (fin2_diagonal R first second).1 0 0 = first := by
  simp [fin2_diagonal, TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_apply]

private theorem fin2_diagonal_second (R : Type) [CommRing R] (first second : Rˣ) :
    (fin2_diagonal R first second).1 1 1 = second := by
  simp [fin2_diagonal, TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_apply]

private def fin2_element (R : Type) [CommRing R] (first second : Rˣ) (a : R) :
    TauCeti.upperTriangularGroup (Fin 2) R :=
  fin2_shear R a * fin2_diagonal R first second

private theorem fin2_element_upper (R : Type) [CommRing R]
    (first second : Rˣ) (a : R) :
    (fin2_element R first second a).1 0 1 = a * second := by
  change ((fin2_shear R a).1 * (fin2_diagonal R first second).1 :
    Matrix (Fin 2) (Fin 2) R) 0 1 = _
  have hzero : (fin2_diagonal R first second).1 0 1 = 0 := by
    simp [fin2_diagonal, TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, hzero, mul_zero, zero_add,
    fin2_shear_entry, fin2_diagonal_second]

private theorem fin2_shear_point (R : Type) [CommRing R] [Algebra K R] (a : R) :
    ((pointsMulEquiv (R := K) (n := 2) (A := R)).symm (fin2_shear R a)).ofConv
      ((coordinateMap K 2).hom (TauCeti.GeneralLinear.genericMatrix K 2 0 1)) = a := by
  rw [point_entry, fin2_shear_entry]

private theorem fin2_element_point (R : Type) [CommRing R] [Algebra K R]
    (first second : Rˣ) (a : R) :
    ((pointsMulEquiv (R := K) (n := 2) (A := R)).symm
      (fin2_element R first second a)).ofConv
      ((coordinateMap K 2).hom (TauCeti.GeneralLinear.genericMatrix K 2 0 1)) =
        a * second := by
  rw [point_entry, fin2_element_upper]

private theorem fin2_detInverse (R : Type) [CommRing R] [Algebra K R] (a : R) :
    ((pointsMulEquiv (R := K) (n := 2) (A := R)).symm (fin2_shear R a)).ofConv
      ((coordinateMap K 2).hom (Ring.inverse (TauCeti.GeneralLinear.genericMatrix K 2).det)) =
        ↑(Matrix.GeneralLinearGroup.det (fin2_shear R a).1)⁻¹ := by
  let f := ((pointsMulEquiv (R := K) (n := 2) (A := R)).symm (fin2_shear R a)).ofConv
  have hmatrix : (TauCeti.GeneralLinear.genericMatrix K 2).map
      (f.comp (coordinateMap K 2).hom) = (fin2_shear R a).1 := by
    ext i j
    exact point_entry K 2 R (fin2_shear R a) i j
  change (f.comp (coordinateMap K 2).hom)
    (Ring.inverse (TauCeti.GeneralLinear.genericMatrix K 2).det) = _
  rw [(TauCeti.GeneralLinear.isUnit_det_genericMatrix K 2).map_ringInverse
    (f.comp (coordinateMap K 2).hom)]
  rw [AlgHom.map_det]
  change Ring.inverse ((TauCeti.GeneralLinear.genericMatrix K 2).map
    (f.comp (coordinateMap K 2).hom)).det = _
  rw [hmatrix]
  exact Ring.inverse_unit (Matrix.GeneralLinearGroup.det (fin2_shear R a).1)

private theorem zero_ring_fin0 :
    Algebra.FiniteType (ZMod 1) (coordinateHopfAlgebra (ZMod 1) 0) := inferInstance

private theorem zero_ring_fin2 :
    Algebra.FiniteType (ZMod 1) (coordinateHopfAlgebra (ZMod 1) 2) := inferInstance

private theorem zero_ring_fin0_point (s : TauCeti.upperTriangularGroup (Fin 0) (ZMod 1)) :
    s = 1 := fin0_point _ s

private theorem zero_ring_fin2_point (s : TauCeti.upperTriangularGroup (Fin 2) (ZMod 1)) :
    s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  exact Subsingleton.elim _ _

private theorem zero_ring_fin0_inclusion
    (s : TauCeti.upperTriangularGroup (Fin 0) (ZMod 1)) :
    Spec.mapMulEquiv (R := (ZMod 1)) (S := coordinateHopfAlgebra (ZMod 1) 0) (T := (ZMod 1))
        ((pointsMulEquiv (R := (ZMod 1)) (n := 0) (A := (ZMod 1))).symm s) ≫
      (inclusion (ZMod 1) 0).hom.hom =
      TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation
        (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 1) 0) (ZMod 1)
        (TauCeti.GeneralLinear.groupScheme_def (ZMod 1) 0)
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := (ZMod 1)) 0).symm s.1) :=
  general_inclusion (ZMod 1) 0 (ZMod 1) s

private theorem zero_ring_fin2_inclusion
    (s : TauCeti.upperTriangularGroup (Fin 2) (ZMod 1)) :
    Spec.mapMulEquiv (R := (ZMod 1)) (S := coordinateHopfAlgebra (ZMod 1) 2) (T := (ZMod 1))
        ((pointsMulEquiv (R := (ZMod 1)) (n := 2) (A := (ZMod 1))).symm s) ≫
      (inclusion (ZMod 1) 2).hom.hom =
      TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation
        (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 1) 2) (ZMod 1)
        (TauCeti.GeneralLinear.groupScheme_def (ZMod 1) 2)
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := (ZMod 1)) 2).symm s.1) :=
  general_inclusion (ZMod 1) 2 (ZMod 1) s

private theorem zero_ring_fin0_detInverse :
    (coordinateMap (ZMod 1) 0).hom
      (Ring.inverse (TauCeti.GeneralLinear.genericMatrix (ZMod 1) 0).det) = 1 := by
  rw [Matrix.det_isEmpty, Ring.inverse_one, map_one]

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
    ((pointsMulEquiv (R := ℤ) (n := 2) (A := DualNumber ℤ)).symm
      (fin2_shear (DualNumber ℤ) DualNumber.eps)).ofConv
      ((coordinateMap ℤ 2).hom (TauCeti.GeneralLinear.genericMatrix ℤ 2 0 1)) =
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

private theorem reduction_natural (s : TauCeti.upperTriangularGroup (Fin 2) ℤ) :
    ((pointsMulEquiv (R := ℤ) (n := 2) (A := ZMod 1)).symm
      (TauCeti.UpperTriangularGroup.map (Algebra.ofId ℤ (ZMod 1)).toRingHom s)).ofConv =
      (Algebra.ofId ℤ (ZMod 1)).comp
        ((pointsMulEquiv (R := ℤ) (n := 2) (A := ℤ)).symm s).ofConv :=
  general_from_natural ℤ 2 ℤ (ZMod 1) (Algebra.ofId ℤ (ZMod 1)) s

private theorem reduction_points_natural :
    (TauCeti.HopfAlgebra.pointsFunctor (R := ℤ) (H := coordinateHopfAlgebra ℤ 2)).map
        (CommAlgCat.ofHom (Algebra.ofId ℤ (ZMod 1))) ≫
      (pointsNatIso (R := ℤ) 2).hom.app (CommAlgCat.of ℤ (ZMod 1)) =
      (pointsNatIso (R := ℤ) 2).hom.app (CommAlgCat.of ℤ ℤ) ≫
        (upperTriangularFunctor (R := ℤ) 2).map
          (CommAlgCat.ofHom (Algebra.ofId ℤ (ZMod 1))) :=
  general_points_natural ℤ 2 ℤ (ZMod 1) (Algebra.ofId ℤ (ZMod 1))

end AlgebraicGroupsTest.UpperTriangularScheme
