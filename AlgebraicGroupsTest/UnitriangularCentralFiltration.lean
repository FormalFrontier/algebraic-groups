/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
public import Mathlib.Data.ZMod.Basic

/-!
# Unitriangular central-filtration tests

These clients check commutator bounds and coefficient changes, including zero and nonreduced rings.
-/

public section

open TauCeti.UpperUnitriangularGroup


set_option warningAsError true

namespace AlgebraicGroupsTest.UnitriangularCentralFiltration

open scoped commutatorElement

variable (n : ℕ) (R : Type) [CommRing R]

private theorem first_stages :
    superdiagonalSubgroup (n := n) (R := R) 0 = ⊤ ∧
    superdiagonalSubgroup (n := n) (R := R) 1 = ⊤ :=
  ⟨superdiagonalSubgroup_zero n R,
    superdiagonalSubgroup_one (n := n) (R := R)⟩

private theorem last_stage :
    superdiagonalSubgroup (n := n) (R := R) n = ⊥ :=
  superdiagonalSubgroup_eq_bot_of_le (n := n) (R := R) le_rfl

private theorem normal_stages (r : ℕ) :
    (superdiagonalSubgroup (n := n) (R := R) r).Normal :=
  inferInstance

private theorem mixed_commutators (r s : ℕ) :
    ⁅superdiagonalSubgroup (n := n) (R := R) r,
      superdiagonalSubgroup (n := n) (R := R) s⁆ ≤
        superdiagonalSubgroup (n := n) (R := R) (r + s) :=
  commutator_superdiagonalSubgroup_le (n := n) (R := R) r s

private theorem coefficient_change {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) :
    (superdiagonalSubgroup (n := n) (R := R) r).map
        (map f) ≤
      superdiagonalSubgroup (n := n) (R := S) r :=
  superdiagonalSubgroup_map n R f r

private theorem coefficient_change_point {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ)
    (g : TauCeti.upperUnitriangularGroup (Fin n) R)
    (hg : g ∈ superdiagonalSubgroup (n := n) (R := R) r) :
    map f g ∈
      superdiagonalSubgroup (n := n) (R := S) r :=
  map_mem_superdiagonalSubgroup (n := n) (R := R) f hg

private theorem empty_class_zero (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 0) R) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using nilpotencyClass_le (m := Fin 0) (R := R))

private theorem singleton_class_zero (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 1) R) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using nilpotencyClass_le (m := Fin 1) (R := R))

private theorem two_class_le_one (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 2) R) ≤ 1 := by
  simpa using nilpotencyClass_le (m := Fin 2) (R := R)

private theorem three_commutator_stage (R : Type) [CommRing R] :
    ⁅superdiagonalSubgroup (n := 3) (R := R) 1,
      superdiagonalSubgroup (n := 3) (R := R) 1⁆ ≤
        superdiagonalSubgroup (n := 3) (R := R) 2 := by
  simpa using commutator_superdiagonalSubgroup_le (n := 3) (R := R) 1 1

private theorem three_class_le_two (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) R) ≤ 2 := by
  simpa using nilpotencyClass_le (m := Fin 3) (R := R)

private theorem zero_ring_case :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 2) (ZMod 1)) ≤ 1 :=
  two_class_le_one (ZMod 1)

private theorem characteristic_two_case :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 2)) ≤ 2 :=
  three_class_le_two (ZMod 2)

private theorem nonreduced_case :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 4)) ≤ 2 :=
  three_class_le_two (ZMod 4)

/-- A map from `ZMod 4` to `ZMod 2` preserves each superdiagonal stage in dimension three. -/
public theorem _root_.TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup_map_zmod_four_two
    (f : ZMod 4 →+* ZMod 2) (r : ℕ) :
    (superdiagonalSubgroup (n := 3) (R := (ZMod 4)) r).map
        (map f) ≤
      superdiagonalSubgroup (n := 3) (R := (ZMod 2)) r :=
  coefficient_change 3 (ZMod 4) f r

end AlgebraicGroupsTest.UnitriangularCentralFiltration
