/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Diagonal
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import clients of the native diagonal group scheme -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry DiagonalCoordinateRing
open scoped CategoryTheory.MonObj DualNumber

universe u

variable (K : Type) [CommRing K]

example (n : Type) [Fintype n] [DecidableEq n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.DiagonalGroup n R) :
    diagonalFromGL K n S (Matrix.DiagonalGroup.map v.toRingHom s) =
      v.comp (diagonalFromGL K n R s) :=
  diagonalFromGL_natural K n R v s

example (n : Type) [Fintype n] [DecidableEq n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (f : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    diagonalToGL K n S (v.comp f) =
      Matrix.DiagonalGroup.map v.toRingHom (diagonalToGL K n R f) :=
  diagonalToGL_natural K n R v f

example (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [Algebra K R] (s : Matrix.DiagonalGroup n R) :
    diagonalGroupMulEquivPoints K n R s ≫ (diagonalInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R s.1 :=
  diagonalInclusion_point K n R s

example (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [Algebra K R] (s : Matrix.DiagonalGroup n R)
    (i : n) :
    (diagonalGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (GeneralLinearCoordinateRing.matrix K n i i)) =
        ((Matrix.DiagonalGroup.unitsEquiv s i : Rˣ) : R) := by
  rw [diagonalGroupMulEquivAlgHom_entry, Matrix.DiagonalGroup.unitsEquiv_apply_val]

example (R : Type) [CommRing R] (s : Matrix.DiagonalGroup (Fin 0) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact Fin.elim0 i

example (R : Type) [CommRing R] (units : Fin 0 → Rˣ) : units = 1 := by
  funext index
  exact Fin.elim0 index

example (R : Type) [CommRing R] [Algebra K R] (unit : Rˣ) :
    (multiplicativeGroupMulEquivPoints K R).symm
      (multiplicativeGroupMulEquivPoints K R unit) =
    ((diagonalGroupUnitsEquivPoints K (Fin 1) R).symm
      (diagonalGroupUnitsEquivPoints K (Fin 1) R (fun _ => unit))) 0 := by
  simp

example (R : Type) [CommRing R] (first second : Rˣ) :
    ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
      (Fin 2 → Rˣ)).symm
      (fun index => if index = 0 then first else second)).1 0 0 = first := by
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply]

example (R : Type) [CommRing R] [Algebra K R] (first second : Rˣ) :
    diagonalGroupMulEquivPoints K (Fin 2) R
        ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
          (Fin 2 → Rˣ)).symm (fun index => if index = 0 then first else second)) ≫
      (diagonalInclusion K (Fin 2)).hom.hom =
    generalLinearGroupMulEquivPoints K (Fin 2) R
      ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
        (Fin 2 → Rˣ)).symm (fun index => if index = 0 then first else second)).1 :=
  diagonalInclusion_point K (Fin 2) R _

example (R : Type) [CommRing R] (first second : Rˣ) :
    ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) R ≃*
      (Fin 2 → Rˣ)).symm
      (fun index => if index = 0 then first else second)).1 1 1 = second := by
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply]

example : Algebra.FiniteType (ZMod 1)
    (DiagonalCoordinateRing.CoordinateRing (ZMod 1) (Fin 0)) := inferInstance

example : quotient (ZMod 1) (Fin 0)
    (GeneralLinearCoordinateRing.detInverse (ZMod 1) (Fin 0)) = 1 := by
  have h := universal_detInverse (ZMod 1) (Fin 0)
  simpa using h

private def dualNumberUnit : (DualNumber ℤ)ˣ :=
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

example : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro h
  have hs := congrArg TrivSqZeroExt.snd h
  norm_num at hs

example : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by simp

example :
    ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) (DualNumber ℤ) ≃*
      (Fin 2 → (DualNumber ℤ)ˣ)).symm
      (fun index => if index = 0 then dualNumberUnit else 1)).1 0 0 =
      1 + DualNumber.eps := by
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply, dualNumberUnit]

example :
    (diagonalGroupMulEquivAlgHom ℤ (Fin 2) (DualNumber ℤ)
      ((Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup (Fin 2) (DualNumber ℤ) ≃*
        (Fin 2 → (DualNumber ℤ)ˣ)).symm
        (fun index => if index = 0 then dualNumberUnit else 1))).ofConv
      (quotient ℤ (Fin 2) (GeneralLinearCoordinateRing.matrix ℤ (Fin 2) 0 0)) =
      1 + DualNumber.eps := by
  rw [diagonalGroupMulEquivAlgHom_entry]
  simp [Matrix.DiagonalGroup.unitsEquiv_symm_apply, dualNumberUnit]
