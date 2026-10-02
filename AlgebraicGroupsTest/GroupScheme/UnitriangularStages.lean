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
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2) :
    unitriangularStagePointMulEquiv K 3 2 R s ≫
        (unitriangularStageInclusion K 3 2).hom.hom =
      unitriangularGroupMulEquivPoints K (Fin 3) R s.1 :=
  unitriangularStageInclusion_point K 3 2 R s

example (R : Type) [CommRing R] [Algebra K R]
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 3) :
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
  · have hz := (Matrix.UnitriangularGroup.mem_superdiagonalSubgroup 3 R
        (unitriangularStageToGL K 3 2 R f).1).mp
          (unitriangularStageToGL K 3 2 R f).2 0 1 (by decide)
    simpa [Matrix.sub_apply, Matrix.one_apply] using hz
  · have hz := (Matrix.UnitriangularGroup.mem_superdiagonalSubgroup 3 R
        (unitriangularStageToGL K 3 2 R f).1).mp
          (unitriangularStageToGL K 3 2 R f).2 1 2 (by decide)
    simpa [Matrix.sub_apply, Matrix.one_apply] using hz

example (R : Type) [CommRing R]
    (s t : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2) :
    (((s * t).1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) =
      ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) +
        ((t.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) := by
  have hs := (Matrix.UnitriangularGroup.mem_superdiagonalSubgroup 3 R s.1).mp
    s.2 0 1 (by decide)
  change (s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 1 -
    (1 : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 at hs
  have hs01 : (s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by
    simpa [Matrix.one_apply] using hs
  change ((s.1.1 : Matrix (Fin 3) (Fin 3) R) *
    (t.1.1 : Matrix (Fin 3) (Fin 3) R)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [hs01, s.1.2.2 0, t.1.2.2 2, add_comm]

example (R : Type) [CommRing R] (n r : ℕ) (hr : n ≤ r)
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) : s = 1 := by
  apply Subtype.ext
  have hs := (Matrix.UnitriangularGroup.superdiagonalSubgroup_antitone n R hr) s.2
  rw [Matrix.UnitriangularGroup.superdiagonalSubgroup_end] at hs
  exact hs

example : Matrix.UnitriangularGroup.superdiagonalSubgroup 0 (ZMod 1) 0 ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      unitriangularStageUnderlyingScheme ℤ 0 0) :=
  unitriangularStagePointMulEquiv ℤ 0 0 (ZMod 1)

example : Matrix.UnitriangularGroup.superdiagonalSubgroup 1 (ZMod 1) 4 ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of ℤ)) ⟶
      unitriangularStageUnderlyingScheme ℤ 1 4) :=
  unitriangularStagePointMulEquiv ℤ 1 4 (ZMod 1)
