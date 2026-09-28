/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularDerivedSeries

@[expose] public section

open scoped commutatorElement

namespace AlgebraicGroupsTest.UnitriangularDerivedSeries

open Matrix.UnitriangularGroup

private theorem symbolic_commutator (n : ℕ) (R : Type) [CommRing R]
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ⁅superdiagonalSubgroup n R r, superdiagonalSubgroup n R s⁆ =
      superdiagonalSubgroup n R (r + s) :=
  superdiagonalSubgroup_commutator_eq n R r s hr hs

private theorem unequal_stages (R : Type) [CommRing R] :
    ⁅superdiagonalSubgroup 4 R 1, superdiagonalSubgroup 4 R 2⁆ =
      superdiagonalSubgroup 4 R 3 := by
  simpa using superdiagonalSubgroup_commutator_eq 4 R 1 2 (by decide) (by decide)

private theorem symbolic_derived (n : ℕ) (R : Type) [CommRing R] (t : ℕ) :
    derivedSeries (Matrix.UnitriangularGroup (Fin n) R) t =
      superdiagonalSubgroup n R (2 ^ t) :=
  derivedSeries_eq_superdiagonalSubgroup n R t

private theorem symbolic_successor (n : ℕ) (R : Type) [CommRing R] (t : ℕ) :
    derivedSeries (Matrix.UnitriangularGroup (Fin n) R) (t + 1) =
      superdiagonalSubgroup n R (2 ^ (t + 1)) :=
  derivedSeries_eq_superdiagonalSubgroup n R (t + 1)

private theorem dimension_zero (R : Type) [CommRing R] :
    derivedSeries (Matrix.UnitriangularGroup (Fin 0) R) 0 = ⊥ := by
  rw [derivedSeries_eq_superdiagonalSubgroup]
  apply le_antisymm _ bot_le
  rw [← superdiagonalSubgroup_end 0 R]
  exact superdiagonalSubgroup_antitone 0 R (by decide : 0 ≤ 2 ^ 0)

private theorem dimension_one (R : Type) [CommRing R] :
    derivedSeries (Matrix.UnitriangularGroup (Fin 1) R) 0 = ⊥ := by
  rw [derivedSeries_eq_superdiagonalSubgroup, pow_zero]
  exact superdiagonalSubgroup_end 1 R

private theorem dimension_two (R : Type) [CommRing R] :
    derivedSeries (Matrix.UnitriangularGroup (Fin 2) R) 1 =
      superdiagonalSubgroup 2 R 2 := by
  simpa using derivedSeries_eq_superdiagonalSubgroup 2 R 1

private theorem dimension_three (R : Type) [CommRing R] :
    derivedSeries (Matrix.UnitriangularGroup (Fin 3) R) 1 =
      superdiagonalSubgroup 3 R 2 := by
  simpa using derivedSeries_eq_superdiagonalSubgroup 3 R 1

private theorem dimension_four_late (R : Type) [CommRing R] :
    derivedSeries (Matrix.UnitriangularGroup (Fin 4) R) 4 =
      superdiagonalSubgroup 4 R 16 := by
  simpa using derivedSeries_eq_superdiagonalSubgroup 4 R 4

private theorem characteristic_two :
    derivedSeries (Matrix.UnitriangularGroup (Fin 3) (ZMod 2)) 1 =
      superdiagonalSubgroup 3 (ZMod 2) 2 := by
  simpa using derivedSeries_eq_superdiagonalSubgroup 3 (ZMod 2) 1

private theorem nonreduced :
    ⁅superdiagonalSubgroup 4 (ZMod 4) 2, superdiagonalSubgroup 4 (ZMod 4) 1⁆ =
      superdiagonalSubgroup 4 (ZMod 4) 3 := by
  simpa using superdiagonalSubgroup_commutator_eq 4 (ZMod 4) 2 1
    (by decide) (by decide)

private theorem zero_ring :
    derivedSeries (Matrix.UnitriangularGroup (Fin 4) (ZMod 1)) 0 = ⊥ := by
  rw [derivedSeries_zero]
  apply le_antisymm _ bot_le
  intro g _
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact Subsingleton.elim _ _

private theorem symbolic_stage_stopping (n : ℕ) (R : Type)
    [CommRing R] [Nontrivial R] (d : ℕ) (hd : 1 ≤ d) :
    superdiagonalSubgroup n R d = ⊥ ↔ n ≤ d :=
  superdiagonalSubgroup_eq_bot_iff n R d hd

private theorem symbolic_derived_stopping (n : ℕ) (R : Type)
    [CommRing R] [Nontrivial R] (t : ℕ) :
    derivedSeries (Matrix.UnitriangularGroup (Fin n) R) t = ⊥ ↔ n ≤ 2 ^ t :=
  derivedSeries_eq_bot_iff n R t

private theorem two_stops_at_one :
    derivedSeries (Matrix.UnitriangularGroup (Fin 2) (ZMod 2)) 1 = ⊥ :=
  (derivedSeries_eq_bot_iff 2 (ZMod 2) 1).2 (by decide)

private theorem zero_index_counterexample :
    ⁅superdiagonalSubgroup 2 (ZMod 2) 0,
      superdiagonalSubgroup 2 (ZMod 2) 1⁆ ≠
        superdiagonalSubgroup 2 (ZMod 2) 1 := by
  intro heq
  have hcomm :
      ⁅superdiagonalSubgroup 2 (ZMod 2) 0,
        superdiagonalSubgroup 2 (ZMod 2) 1⁆ = ⊥ := by
    rw [superdiagonalSubgroup_zero, superdiagonalSubgroup_one]
    change derivedSeries (Matrix.UnitriangularGroup (Fin 2) (ZMod 2)) 1 = ⊥
    exact two_stops_at_one
  have hnot : superdiagonalSubgroup 2 (ZMod 2) 1 ≠ ⊥ := by
    intro hbot
    have hle := (superdiagonalSubgroup_eq_bot_iff 2 (ZMod 2) 1
      (by decide)).1 hbot
    omega
  exact hnot (heq.symm.trans hcomm)

set_option linter.style.haveILetI false in
private theorem four_stops_at_two :
    derivedSeries (Matrix.UnitriangularGroup (Fin 4) (ZMod 4)) 2 = ⊥ :=
  by
    letI : Fact (1 < 4) := ⟨by decide⟩
    exact (derivedSeries_eq_bot_iff 4 (ZMod 4) 2).2 (by decide)

private theorem four_not_at_one :
    derivedSeries (Matrix.UnitriangularGroup (Fin 4) (ZMod 2)) 1 ≠ ⊥ := by
  intro hbot
  have hle := (derivedSeries_eq_bot_iff 4 (ZMod 2) 1).1 hbot
  omega

end AlgebraicGroupsTest.UnitriangularDerivedSeries
