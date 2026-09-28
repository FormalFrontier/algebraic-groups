/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

namespace AlgebraicGroupsTest.UnitriangularNilpotencyClass

open scoped commutatorElement

private theorem elementary_matrix (R : Type) [CommRing R] (a : R) :
    ((Matrix.UnitriangularGroup.elementary 3 R (0 : Fin 3) (1 : Fin 3)
      (by decide) a).1 : Matrix (Fin 3) (Fin 3) R) =
        1 + Matrix.single 0 1 a :=
  Matrix.UnitriangularGroup.elementary_coe 3 R 0 1 (by decide) a

private theorem elementary_gl (R : Type) [CommRing R] (a : R) :
    (Matrix.UnitriangularGroup.elementary 3 R (0 : Fin 3) (1 : Fin 3)
      (by decide) a).1 =
        Matrix.GeneralLinearGroup.elementaryUnit 0 1 (by decide) a :=
  Matrix.UnitriangularGroup.elementary_gl 3 R 0 1 (by decide) a

private theorem elementary_commutator (R : Type) [CommRing R] (a b : R) :
    ⁅Matrix.UnitriangularGroup.elementary 3 R (0 : Fin 3) 1 (by decide) a,
      Matrix.UnitriangularGroup.elementary 3 R 1 2 (by decide) b⁆ =
        Matrix.UnitriangularGroup.elementary 3 R 0 2 (by decide) (a * b) := by
  simpa using Matrix.UnitriangularGroup.elementary_commutator 3 R 0 1 2
    (by decide) (by decide) a b

private theorem empty_class (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 0) R) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 0 R)

private theorem singleton_class (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 1) R) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 1 R)

private theorem two_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 2) R) = 1 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial 2 R

private theorem three_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) R) = 2 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial 3 R

private theorem four_class (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 4) R) = 3 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial 4 R

private theorem characteristic_two_three :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) (ZMod 2)) = 2 :=
  three_class (ZMod 2)

private theorem characteristic_two_four :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 4) (ZMod 2)) = 3 :=
  four_class (ZMod 2)

set_option linter.style.haveILetI false in
private theorem nonreduced_four :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 4) (ZMod 4)) = 3 := by
  letI : Fact (1 < 4) := ⟨by decide⟩
  exact four_class (ZMod 4)

private theorem zero_ring_three :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) (ZMod 1)) = 0 :=
  Matrix.UnitriangularGroup.nilpotencyClass_eq_zero_of_subsingleton 3 (ZMod 1)

end AlgebraicGroupsTest.UnitriangularNilpotencyClass
