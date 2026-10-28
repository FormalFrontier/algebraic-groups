/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass
public import Mathlib.Data.ZMod.Basic

/-!
# Unitriangular commutator and nilpotency-class tests

These clients include the elementary commutator in dimension three, empty indices, and zero rings.
-/

public section

open TauCeti.UpperUnitriangularGroup


set_option warningAsError true

namespace AlgebraicGroupsTest.UnitriangularNilpotencyClass

open scoped commutatorElement

private theorem elementary_matrix (R : Type) [CommRing R] (a : R) :
    ((elementary 3 R (0 : Fin 3) (1 : Fin 3)
      (by decide) a).1 : Matrix (Fin 3) (Fin 3) R) =
        1 + Matrix.single 0 1 a :=
  elementary_coe 3 R 0 1 (by decide) a

private theorem elementary_gl (R : Type) [CommRing R] (a : R) :
    (elementary 3 R (0 : Fin 3) (1 : Fin 3)
      (by decide) a).1 =
        Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a :=
  TauCeti.UpperUnitriangularGroup.elementary_gl 3 R 0 1 (by decide) a

/-- The adjacent elementary roots in dimension three have commutator coefficient `a * b`. -/
public theorem _root_.TauCeti.UpperUnitriangularGroup.elementary_commutator_fin_three
    (R : Type) [CommRing R] (a b : R) :
    ⁅elementary 3 R (0 : Fin 3) 1 (by decide) a,
      elementary 3 R 1 2 (by decide) b⁆ =
        elementary 3 R 0 2 (by decide) (a * b) := by
  simpa using TauCeti.UpperUnitriangularGroup.elementary_commutator 3 R 0 1 2
    (by decide) (by decide) a b

private theorem empty_class (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 0) R) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using nilpotencyClass_le (m := Fin 0) (R := R))

private theorem singleton_class (R : Type) [CommRing R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 1) R) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using nilpotencyClass_le (m := Fin 1) (R := R))

private theorem two_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 2) R) = 1 := by
  simpa using nilpotencyClass_eq_of_nontrivial 2 R

private theorem three_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) R) = 2 := by
  simpa using nilpotencyClass_eq_of_nontrivial 3 R

private theorem four_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 4) R) = 3 := by
  simpa using nilpotencyClass_eq_of_nontrivial 4 R

private theorem characteristic_two_three :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 2)) = 2 :=
  three_class (ZMod 2)

private theorem characteristic_two_four :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 4) (ZMod 2)) = 3 :=
  four_class (ZMod 2)

private theorem nonreduced_four :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 4) (ZMod 4)) = 3 := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact four_class (ZMod 4)

private theorem zero_ring_three :
    Group.nilpotencyClass (TauCeti.upperUnitriangularGroup (Fin 3) (ZMod 1)) = 0 :=
  nilpotencyClass_eq_zero_of_subsingleton 3 (ZMod 1)

end AlgebraicGroupsTest.UnitriangularNilpotencyClass
