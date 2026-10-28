/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStages
public import Mathlib.Data.ZMod.Basic

/-!
# Closed unitriangular stage clients

These clients evaluate the genuine Hopf quotients over arbitrary rings, inspect
the rank-three second stage, and exercise degenerate coefficient rings and ranks.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry UnitriangularStageCoordinateRing
open scoped CategoryTheory CategoryTheory.MonObj

variable (K : Type) [CommRing K]

example : ideal K 3 0 = ⊥ := ideal_zero K 3
example : ideal K 3 1 = ⊥ := ideal_one K 3

example (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := 3) (R := R) 2) :
    unitriangularStagePointMulEquiv K 3 2 R s ≫
        (unitriangularStageInclusion K 3 2).hom.hom =
      (TauCeti.UpperUnitriangular.schemePointsMulEquiv (R := K) (A := R) (Fin 3)).symm s.1 :=
  unitriangularStageInclusion_point K 3 2 R s

example (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := 3) (R := R) 3) :
    unitriangularStagePointMulEquiv K 3 3 R s ≫
        (unitriangularStageSuccessor K 3 2).hom.hom =
      unitriangularStagePointMulEquiv K 3 2 R
        (unitriangularStagePointSuccessor 3 2 R s) :=
  unitriangularStageSuccessor_point K 3 2 R s

example (R : Type) [CommRing R] [Algebra K R]
    (f : CoordinateRing K 3 2 →ₐ[K] R) :
    (((unitriangularStageToGL K 3 2 R f).1.1 : Matrix (Fin 3) (Fin 3) R) 0 1 = 0) ∧
    (((unitriangularStageToGL K 3 2 R f).1.1 : Matrix (Fin 3) (Fin 3) R) 1 2 = 0) := by
  constructor
  · have hz := (TauCeti.UpperUnitriangularGroup.mem_superdiagonalSubgroup_iff _
        (unitriangularStageToGL K 3 2 R f).1).mp
          (unitriangularStageToGL K 3 2 R f).2 0 1 (by decide)
    simpa [Matrix.sub_apply, Matrix.one_apply] using hz
  · have hz := (TauCeti.UpperUnitriangularGroup.mem_superdiagonalSubgroup_iff _
        (unitriangularStageToGL K 3 2 R f).1).mp
          (unitriangularStageToGL K 3 2 R f).2 1 2 (by decide)
    simpa [Matrix.sub_apply, Matrix.one_apply] using hz

example (R : Type) [CommRing R]
    (s t : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := 3) (R := R) 2) :
    (((s * t).1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) =
      ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) +
        ((t.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) := by
  have hs := (TauCeti.UpperUnitriangularGroup.mem_superdiagonalSubgroup_iff _ s.1).mp
    s.2 0 1 (by decide)
  have hs01 : (s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by
    simpa [Matrix.one_apply] using hs
  change ((s.1.1 : Matrix (Fin 3) (Fin 3) R) *
    (t.1.1 : Matrix (Fin 3) (Fin 3) R)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [hs01, add_comm]

example (R : Type) [CommRing R] (n r : ℕ) (hr : n ≤ r)
    (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := n) (R := R) r) : s = 1 := by
  apply Subtype.ext
  have hs := (TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup_antitone (n := n) (R := R)
    hr) s.2
  rw [TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup_eq_bot_of_le (by omega)] at hs
  exact hs

example : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := 0) (R := (ZMod 1)) 0 ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      unitriangularStageUnderlyingScheme ℤ 0 0) :=
  unitriangularStagePointMulEquiv ℤ 0 0 (ZMod 1)

example : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := 1) (R := (ZMod 1)) 4 ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      unitriangularStageUnderlyingScheme ℤ 1 4) :=
  unitriangularStagePointMulEquiv ℤ 1 4 (ZMod 1)
