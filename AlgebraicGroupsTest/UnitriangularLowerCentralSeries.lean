/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries
import Mathlib.Data.ZMod.Basic

/-!
# Ordinary-import checks for the unitriangular lower central series
-/

public section

open TauCeti.UpperUnitriangularGroup


set_option warningAsError true

namespace AlgebraicGroupsTest.UnitriangularLowerCentralSeries

open TauCeti.UpperUnitriangularGroup

private theorem generic_series (n t : ℕ) (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin n) R)).lowerCentralSeries t =
      superdiagonalSubgroup (n := n) (R := R) (t + 1) :=
  lowerCentralSeries_eq_superdiagonalSubgroup (n := n) (R := R) t

private theorem generic_generation (n d : ℕ) (R : Type) [CommRing R]
    (hd : 1 ≤ d) (H : Subgroup (TauCeti.upperUnitriangularGroup (Fin n) R))
    (hroot : ∀ (i j : Fin n) (hij : i < j) (a : R),
      i.val + d ≤ j.val → elementary n R i j hij a ∈ H) :
    superdiagonalSubgroup (n := n) (R := R) d ≤ H :=
  superdiagonalSubgroup_le_of_elementary_mem n R d hd H hroot

private theorem empty_generation (R : Type) [CommRing R]
    (H : Subgroup (TauCeti.upperUnitriangularGroup (Fin 0) R)) :
    superdiagonalSubgroup (n := 0) (R := R) 1 ≤ H := by
  apply generic_generation 0 1 R (by decide) H
  intro i
  exact Fin.elim0 i

private theorem singleton_generation (R : Type) [CommRing R]
    (H : Subgroup (TauCeti.upperUnitriangularGroup (Fin 1) R)) :
    superdiagonalSubgroup (n := 1) (R := R) 1 ≤ H := by
  apply generic_generation 1 1 R (by decide) H
  intro i j hij
  omega

private theorem four_stage_generation (R : Type) [CommRing R] :
    superdiagonalSubgroup (n := 4) (R := R) 2 ≤ superdiagonalSubgroup (n := 4) (R := R) 2 := by
  apply generic_generation 4 2 R (by decide) _
  intro i j hij a hdist
  exact elementary_mem_superdiagonalSubgroup (n := 4) (R := R) i j hij a 2 hdist

private theorem four_late_generation (R : Type) [CommRing R]
    (H : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) R)) :
    superdiagonalSubgroup (n := 4) (R := R) 8 ≤ H := by
  apply generic_generation 4 8 R (by decide) H
  intro i j hij a hdist
  have := j.isLt
  omega

private theorem characteristic_two_generation :
    superdiagonalSubgroup (n := 4) (R := (ZMod 2)) 3 ≤
      superdiagonalSubgroup (n := 4) (R := (ZMod 2)) 3 := by
  apply generic_generation 4 3 (ZMod 2) (by decide) _
  intro i j hij a hdist
  exact elementary_mem_superdiagonalSubgroup (n := 4) (R := (ZMod 2)) i j hij a 3 hdist

private theorem nonreduced_generation :
    superdiagonalSubgroup (n := 4) (R := (ZMod 4)) 2 ≤
      superdiagonalSubgroup (n := 4) (R := (ZMod 4)) 2 := by
  have : Fact (1 < 4) := ⟨by decide⟩
  apply generic_generation 4 2 (ZMod 4) (by decide) _
  intro i j hij a hdist
  exact elementary_mem_superdiagonalSubgroup (n := 4) (R := (ZMod 4)) i j hij a 2 hdist

private theorem zero_ring_generation :
    superdiagonalSubgroup (n := 4) (R := (ZMod 1)) 3 ≤
      superdiagonalSubgroup (n := 4) (R := (ZMod 1)) 3 := by
  apply generic_generation 4 3 (ZMod 1) (by decide) _
  intro i j hij a hdist
  exact elementary_mem_superdiagonalSubgroup (n := 4) (R := (ZMod 1)) i j hij a 3 hdist

private theorem empty_dim (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 0) R)).lowerCentralSeries 0 =
      superdiagonalSubgroup (n := 0) (R := R) 1 := generic_series 0 0 R

private theorem singleton_dim (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 1) R)).lowerCentralSeries 7 =
      superdiagonalSubgroup (n := 1) (R := R) 8 := generic_series 1 7 R

private theorem three_first (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 3) R)).lowerCentralSeries 1 =
      superdiagonalSubgroup (n := 3) (R := R) 2 := generic_series 3 1 R

private theorem four_first (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) R)).lowerCentralSeries 1 =
      superdiagonalSubgroup (n := 4) (R := R) 2 := generic_series 4 1 R

private theorem four_large (R : Type) [CommRing R] :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) R)).lowerCentralSeries 9 =
      superdiagonalSubgroup (n := 4) (R := R) 10 := generic_series 4 9 R

/-- The root from zero to three lies in the second lower central subgroup in dimension four. -/
public theorem _root_.elementary_zero_three_mem_lowerCentralSeries_two
    (R : Type) [CommRing R] (a : R) :
    elementary 4 R (0 : Fin 4) (3 : Fin 4) (by decide) a ∈
      (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) R)).lowerCentralSeries 2 :=
  elementary_mem_lowerCentralSeries_of_distance 4 R 0 3 (by decide) a 2 (by decide)

private theorem root_at_stage (R : Type) [CommRing R] (a : R) :
    elementary 4 R (0 : Fin 4) (3 : Fin 4) (by decide) a ∈
      superdiagonalSubgroup (n := 4) (R := R) 3 :=
  elementary_mem_superdiagonalSubgroup (n := 4) (R := R) 0 3 (by decide) a 3 (by decide)

private theorem characteristic_two_three :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 2))).lowerCentralSeries 1 =
      superdiagonalSubgroup (n := 3) (R := (ZMod 2)) 2 := generic_series 3 1 (ZMod 2)

private theorem characteristic_two_four :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) (ZMod 2))).lowerCentralSeries 2 =
      superdiagonalSubgroup (n := 4) (R := (ZMod 2)) 3 := generic_series 4 2 (ZMod 2)

private theorem nonreduced_four :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 4) (ZMod 4))).lowerCentralSeries 1 =
      superdiagonalSubgroup (n := 4) (R := (ZMod 4)) 2 := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact generic_series 4 1 (ZMod 4)

private theorem zero_ring_empty :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 0) (ZMod 1))).lowerCentralSeries 4 =
      superdiagonalSubgroup (n := 0) (R := (ZMod 1)) 5 := generic_series 0 4 (ZMod 1)

private theorem zero_ring_singleton :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 1) (ZMod 1))).lowerCentralSeries 0 =
      superdiagonalSubgroup (n := 1) (R := (ZMod 1)) 1 := generic_series 1 0 (ZMod 1)

private theorem zero_ring_three :
    (⊤ : Subgroup (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 1))).lowerCentralSeries 1 =
      superdiagonalSubgroup (n := 3) (R := (ZMod 1)) 2 := generic_series 3 1 (ZMod 1)

end AlgebraicGroupsTest.UnitriangularLowerCentralSeries
