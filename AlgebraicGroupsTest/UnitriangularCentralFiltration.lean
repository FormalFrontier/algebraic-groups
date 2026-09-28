/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

namespace AlgebraicGroupsTest.UnitriangularCentralFiltration

open scoped commutatorElement

variable (n : ℕ) (R : Type) [CommRing R]

private theorem first_stages :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R 0 = ⊤ ∧
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R 1 = ⊤ :=
  ⟨Matrix.UnitriangularGroup.superdiagonalSubgroup_zero n R,
    Matrix.UnitriangularGroup.superdiagonalSubgroup_one n R⟩

private theorem last_stage :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R n = ⊥ :=
  Matrix.UnitriangularGroup.superdiagonalSubgroup_end n R

private theorem normal_stages (r : ℕ) :
    (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r).Normal :=
  inferInstance

private theorem mixed_commutators (r s : ℕ) :
    ⁅Matrix.UnitriangularGroup.superdiagonalSubgroup n R r,
      Matrix.UnitriangularGroup.superdiagonalSubgroup n R s⁆ ≤
        Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + s) :=
  Matrix.UnitriangularGroup.superdiagonalSubgroup_commutator n R r s

private theorem coefficient_change {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) :
    (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r).map
        (Matrix.UnitriangularGroup.map f) ≤
      Matrix.UnitriangularGroup.superdiagonalSubgroup n S r :=
  Matrix.UnitriangularGroup.superdiagonalSubgroup_map n R f r

private theorem coefficient_change_point {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ)
    (g : Matrix.UnitriangularGroup (Fin n) R)
    (hg : g ∈ Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    Matrix.UnitriangularGroup.map f g ∈
      Matrix.UnitriangularGroup.superdiagonalSubgroup n S r :=
  Matrix.UnitriangularGroup.map_mem_superdiagonalSubgroup n R f hg

private theorem empty_class_zero (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 0) R) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 0 R)

private theorem singleton_class_zero (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 1) R) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 1 R)

private theorem two_class_le_one (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 2) R) ≤ 1 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 2 R

private theorem three_commutator_stage (R : Type) [CommRing R] :
    ⁅Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 1,
      Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 1⁆ ≤
        Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2 := by
  simpa using Matrix.UnitriangularGroup.superdiagonalSubgroup_commutator 3 R 1 1

private theorem three_class_le_two (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) R) ≤ 2 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 3 R

private theorem zero_ring_case :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 2) (ZMod 1)) ≤ 1 :=
  two_class_le_one (ZMod 1)

private theorem characteristic_two_case :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) (ZMod 2)) ≤ 2 :=
  three_class_le_two (ZMod 2)

private theorem nonreduced_case :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) (ZMod 4)) ≤ 2 :=
  three_class_le_two (ZMod 4)

private theorem nonreduced_to_characteristic_two
    (f : ZMod 4 →+* ZMod 2) (r : ℕ) :
    (Matrix.UnitriangularGroup.superdiagonalSubgroup 3 (ZMod 4) r).map
        (Matrix.UnitriangularGroup.map f) ≤
      Matrix.UnitriangularGroup.superdiagonalSubgroup 3 (ZMod 2) r :=
  coefficient_change 3 (ZMod 4) f r

end AlgebraicGroupsTest.UnitriangularCentralFiltration
