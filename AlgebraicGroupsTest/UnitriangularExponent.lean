/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularExponent
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace AlgebraicGroupsTest.UnitriangularExponent

theorem generic_matrix_nilpotence {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
    (N : Matrix ι ι R) (hu : N.IsUpperTriangular) (hd : ∀ i, N i i = 0) :
    N ^ Fintype.card ι = 0 :=
  Matrix.pow_card_eq_zero_of_upperTriangular_diag_zero N hu hd

example (R : Type) [CommRing R] (hp : Nat.Prime p) (hchar : (p : R) = 0)
    (g : Matrix.UnitriangularGroup (Fin 0) R) : g ^ (p ^ 0) = 1 :=
  Matrix.UnitriangularGroup.pow_prime_pow_eq_one hp hchar (by omega) g

example (R : Type) [CommRing R] (hp : Nat.Prime p) (hchar : (p : R) = 0)
    (g : Matrix.UnitriangularGroup (Fin 1) R) : g ^ (p ^ 0) = 1 :=
  Matrix.UnitriangularGroup.pow_prime_pow_eq_one hp hchar (by simp) g

example (g : Matrix.UnitriangularGroup (Fin 4) (ZMod 2)) : g ^ (2 ^ 2) = 1 :=
  Matrix.UnitriangularGroup.pow_prime_pow_eq_one (by decide) (by decide) (by decide) g

example (g : Matrix.UnitriangularGroup (Fin 3) (ZMod 3)) : g ^ (3 ^ 1) = 1 :=
  Matrix.UnitriangularGroup.pow_prime_pow_eq_one (by decide) (by decide) (by decide) g

example : ∃ g : Matrix.UnitriangularGroup (Fin 3) (ZMod 2), g ^ 2 ≠ 1 :=
  Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt (by decide) (by decide)

example : ∃ g : Matrix.UnitriangularGroup (Fin 4) (ZMod 3), g ^ 3 ≠ 1 :=
  Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt (by decide) (by decide)

theorem generic_exponent_threshold (R : Type) [CommRing R] [Nontrivial R] {n p t : ℕ}
    (hp : Nat.Prime p) (hchar : (p : R) = 0) :
    (∀ g : Matrix.UnitriangularGroup (Fin n) R, g ^ (p ^ t) = 1) ↔ n ≤ p ^ t :=
  Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff hp hchar

example (R : Type) [CommRing R] [Nontrivial R] {n p t : ℕ}
    (hp : Nat.Prime p) (hchar : (p : R) = 0) :
    (Monoid.exponent (Matrix.UnitriangularGroup (Fin n) R) ∣ p ^ t) ↔ n ≤ p ^ t :=
  Matrix.UnitriangularGroup.exponent_dvd_prime_pow_iff hp hchar

example (g : Matrix.UnitriangularGroup (Fin 4) (ZMod 2)) : g ^ 0 = 1 := pow_zero g

example : (∀ g : Matrix.UnitriangularGroup (Fin 4) (ZMod 2), g ^ (2 ^ 2) = 1) :=
  (Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff (by decide) (by decide)).mpr
    (by decide)

example : ¬(∀ g : Matrix.UnitriangularGroup (Fin 3) (ZMod 2), g ^ (2 ^ 1) = 1) := by
  intro hall
  have hbad : 3 ≤ 2 ^ 1 :=
    (Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff (by decide) (by decide)).mp hall
  omega

example (g : Matrix.UnitriangularGroup (Fin 4) (ZMod 1)) : g ^ (2 ^ 2) = 1 :=
  Matrix.UnitriangularGroup.pow_prime_pow_eq_one (by decide) (by decide) (by decide) g

example : (DualNumber.eps : DualNumber (ZMod 2)) ^ 2 = 0 := by simp

example : (DualNumber.eps : DualNumber (ZMod 2)) ≠ 0 := by
  intro heq
  have h := congrArg TrivSqZeroExt.snd heq
  simp at h

example (g : Matrix.UnitriangularGroup (Fin 4) (DualNumber (ZMod 2))) :
    g ^ (2 ^ 2) = 1 := by
  have hchar : (2 : DualNumber (ZMod 2)) = 0 := by
    apply TrivSqZeroExt.ext
    · change (2 : ZMod 2) = 0
      decide
    · change (0 : ZMod 2) = 0
      rfl
  exact Matrix.UnitriangularGroup.pow_prime_pow_eq_one (by decide) hchar (by decide) g

example : ∃ g : Matrix.UnitriangularGroup (Fin 3) (DualNumber (ZMod 2)),
    g ^ 2 ≠ 1 :=
  Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt (by decide) (by decide)

end AlgebraicGroupsTest.UnitriangularExponent
