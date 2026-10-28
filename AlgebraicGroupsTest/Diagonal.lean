/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import clients of the native diagonal group scheme -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

universe u

variable (K : Type) [CommRing K]

example (n : Type) [Fintype n] [DecidableEq n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : n → Rˣ) :
    AlgHom.mapValue v ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R)).symm s) =
      (TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := S)).symm
        (fun i ↦ Units.map v.toMonoidHom (s i)) :=
  TauCeti.SplitTorus.mapValue_pointsMulEquiv_symm_apply v s

example (n : Type) [Fintype n] [DecidableEq n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S)
    (f : WithConv (MonoidAlgebra K (Multiplicative (n →₀ ℤ)) →ₐ[K] R)) (i : n) :
    TauCeti.SplitTorus.pointsMulEquiv (AlgHom.mapValue v f) i =
      Units.map v.toMonoidHom (TauCeti.SplitTorus.pointsMulEquiv f i) :=
  TauCeti.SplitTorus.pointsMulEquiv_mapValue v f i

example (n : ℕ) (R : Type) [CommRing R] [Algebra K R]
    (s : ULift (Fin n) → Rˣ) :
    TauCeti.GeneralLinear.schemePointsMulEquiv n R
      ((TauCeti.SplitTorus.schemePointsMulEquiv (R := K) (A := R)).symm s ≫
        (TauCeti.GeneralLinear.diagonalTorus (R := K) (N := n)).hom.hom) =
      TauCeti.diagGL (fun i ↦ s (ULift.up i)) := by
  rw [TauCeti.GeneralLinear.schemePointsMulEquiv_diagonalTorus,
    MulEquiv.apply_symm_apply]
  congr 1
  funext i
  exact TauCeti.GeneralLinear.diagonalTorusCoordinates_apply s i

example (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [Algebra K R] (s : n → Rˣ) (i : n) :
    ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R)).symm s).ofConv
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) = (s i : R) :=
  TauCeti.SplitTorus.pointsMulEquiv_symm_apply_single s i

example (R : Type) [CommRing R] (s : Matrix.GeneralLinearGroup (Fin 0) R) : s = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact Fin.elim0 i

example (R : Type) [CommRing R] (units : Fin 0 → Rˣ) : units = 1 := by
  funext index
  exact Fin.elim0 index

example (R : Type) [CommRing R] [Algebra K R] (unit : Rˣ) :
    TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := K) (A := R)
      ((TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := K) (A := R)).symm unit) =
      (TauCeti.SplitTorus.schemePointsMulEquiv (R := K) (A := R)
        ((TauCeti.SplitTorus.schemePointsMulEquiv (R := K) (A := R)).symm
          (fun _ : Fin 1 ↦ unit))) 0 := by
  simp

example (R : Type) [CommRing R] (first second : Rˣ) :
    TauCeti.diagGL (fun index : Fin 2 ↦ if index = 0 then first else second) 0 0 = first := by
  simp [TauCeti.diagGL_apply]

example (R : Type) [CommRing R] [Algebra K R] (first second : Rˣ) :
    TauCeti.GeneralLinear.schemePointsMulEquiv 2 R
      ((TauCeti.SplitTorus.schemePointsMulEquiv (R := K) (A := R)).symm
        (fun i : ULift (Fin 2) ↦ if i.down = 0 then first else second) ≫
        (TauCeti.GeneralLinear.diagonalTorus (R := K) (N := 2)).hom.hom) =
      TauCeti.diagGL (fun i : Fin 2 ↦ if i = 0 then first else second) := by
  rw [TauCeti.GeneralLinear.schemePointsMulEquiv_diagonalTorus,
    MulEquiv.apply_symm_apply]
  congr 1
  funext i
  exact TauCeti.GeneralLinear.diagonalTorusCoordinates_apply _ i

example (R : Type) [CommRing R] (first second : Rˣ) :
    TauCeti.diagGL (fun index : Fin 2 ↦ if index = 0 then first else second) 1 1 = second := by
  simp [TauCeti.diagGL_apply]

example : Algebra.FiniteType (ZMod 1)
    (MonoidAlgebra (ZMod 1) (Multiplicative (Fin 0 →₀ ℤ))) := inferInstance

example : (TauCeti.GeneralLinear.diagonalTorusCoordinateMap (R := ZMod 1) (N := 0)).hom
    (Ring.inverse (TauCeti.GeneralLinear.genericMatrix (ZMod 1) 0).det) = 1 :=
  Subsingleton.elim _ _

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
    TauCeti.diagGL (fun index : Fin 2 ↦ if index = 0 then dualNumberUnit else 1) 0 0 =
      1 + DualNumber.eps := by
  simp [TauCeti.diagGL_apply, dualNumberUnit]

example :
    ((TauCeti.SplitTorus.pointsMulEquiv (R := ℤ) (A := DualNumber ℤ)).symm
      (fun index : Fin 2 ↦ if index = 0 then dualNumberUnit else 1)).ofConv
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (0 : Fin 2) 1)) 1) =
      1 + DualNumber.eps := by
  rw [TauCeti.SplitTorus.pointsMulEquiv_symm_apply_single]
  simp [dualNumberUnit]
