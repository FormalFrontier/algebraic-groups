/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.DiagonalProduct
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary-import tests for the finite diagonal group-scheme product -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj DualNumber

universe u

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n] :
    TauCeti.SplitTorus.groupScheme K n ≅
      (∏ᶜ fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K n

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) :
    (diagonalGroupSchemeProductIso K n).hom ≫
      Limits.Pi.π (fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j =
        TauCeti.SplitTorus.characterGroupSchemeMap
          (R := K) (Finsupp.single j 1) :=
  diagonalGroupSchemeProductIso_hom_π K n j

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) :
    (diagonalGroupSchemeProductIso K n).inv ≫
      TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j 1) =
      Limits.Pi.π (fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j :=
  diagonalGroupSchemeProductIso_inv_projection K n j

example (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (j : n) (X : Over (Spec (.of K)))
    (hom : X ⟶ (TauCeti.SplitTorus.groupScheme K n).X) :
    multiplicativeGroupHomUnits K X
      (hom ≫ (TauCeti.SplitTorus.characterGroupSchemeMap
        (R := K) (Finsupp.single j 1)).hom.hom) =
      diagonalGroupHomUnits K n X hom j :=
  diagonalGroupProjection_globalUnit K n j X hom

example (K : Type) [CommRing K] :
    Limits.IsTerminal (TauCeti.SplitTorus.groupScheme K (Fin 0)) :=
  diagonalGroupSchemeFin0IsTerminal K

example (K : Type) [CommRing K] :
    TauCeti.SplitTorus.groupScheme K (Fin 0) ≅
      (∏ᶜ fun _ : Fin 0 ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 0)

example (K : Type) [CommRing K] :
    TauCeti.SplitTorus.groupScheme K (Fin 1) ≅
      (∏ᶜ fun _ : Fin 1 ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 1)

example (K : Type) [CommRing K] (j : Fin 1) :
    (diagonalGroupSchemeProductIso K (Fin 1)).hom ≫
      Limits.Pi.π (fun _ : Fin 1 ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j =
        TauCeti.SplitTorus.characterGroupSchemeMap
          (R := K) (Finsupp.single j 1) :=
  diagonalGroupSchemeProductIso_hom_π K (Fin 1) j

example (K : Type) [CommRing K] :
    TauCeti.SplitTorus.groupScheme K (Fin 2) ≅
      (∏ᶜ fun _ : Fin 2 ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  diagonalGroupSchemeProductIso K (Fin 2)

example (K : Type) [CommRing K] (j : Fin 2) :
    (diagonalGroupSchemeProductIso K (Fin 2)).inv ≫
      TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j 1) =
        Limits.Pi.π (fun _ : Fin 2 ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j :=
  diagonalGroupSchemeProductIso_inv_projection K (Fin 2) j

example : Limits.IsTerminal (TauCeti.SplitTorus.groupScheme (ZMod 1) (Fin 0)) :=
  diagonalGroupSchemeFin0IsTerminal (ZMod 1)

example (j : Fin 2) :
    MonoidAlgebra.mapDomainBialgHom (ZMod 1)
      (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv
        (Multiplicative (Fin 2 →₀ ℤ)) (Multiplicative.ofAdd (Finsupp.single j 1)))
      (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd 1)) 1) =
    MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single j 1)) 1 := by
  rw [MonoidAlgebra.mapDomainBialgHom_single,
    TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_apply, toAdd_ofAdd, zpow_one]

example (j : Fin 2) :
    (TauCeti.SplitTorus.schemePointsMulEquiv (R := ZMod 1) (A := ZMod 1)).symm
        (1 : Fin 2 → (ZMod 1)ˣ) ≫
      (TauCeti.SplitTorus.characterGroupSchemeMap (R := ZMod 1)
        (Finsupp.single j 1)).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := ZMod 1) (A := ZMod 1)).symm 1 := by
  apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
    (R := ZMod 1) (A := ZMod 1)).injective
  simp

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

private def dualNumberDiagonal : Fin 2 → (DualNumber ℤ)ˣ :=
  fun j ↦ if j = 0 then dualNumberUnit else 1

example : (DualNumber.eps : DualNumber ℤ) ≠ 0 := by
  intro assumption
  have hs := congrArg TrivSqZeroExt.snd assumption
  norm_num at hs

example : (DualNumber.eps : DualNumber ℤ) ^ 2 = 0 := by simp

example :
    (TauCeti.SplitTorus.schemePointsMulEquiv (R := ℤ) (A := DualNumber ℤ)).symm
        dualNumberDiagonal ≫
      (TauCeti.SplitTorus.characterGroupSchemeMap (R := ℤ)
        (Finsupp.single (0 : Fin 2) 1)).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := ℤ) (A := DualNumber ℤ)).symm dualNumberUnit := by
  apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
    (R := ℤ) (A := DualNumber ℤ)).injective
  simp [dualNumberDiagonal]

example :
    (TauCeti.SplitTorus.schemePointsMulEquiv (R := ℤ) (A := DualNumber ℤ)).symm
        dualNumberDiagonal ≫
      (TauCeti.SplitTorus.characterGroupSchemeMap (R := ℤ)
        (Finsupp.single (1 : Fin 2) 1)).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := ℤ) (A := DualNumber ℤ)).symm 1 := by
  apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
    (R := ℤ) (A := DualNumber ℤ)).injective
  simp [dualNumberDiagonal]
