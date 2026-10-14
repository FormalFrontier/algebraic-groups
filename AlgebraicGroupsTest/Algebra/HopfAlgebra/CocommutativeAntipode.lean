/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Basic

/-!
# Cocommutative antipodes on noncommutative group algebras

The group algebra `ℕ[S₃]` has Mathlib's group-algebra Hopf structure and a
cocommutative coalgebra. Its antipode is involutive on arbitrary elements,
not just on group basis elements. The coefficient semiring has no additive
inverses. The basis elements of the transpositions `(0 1)` and `(1 2)` do not
commute, so algebra commutativity cannot supply this involutivity result.

The generic clients keep the scalar and algebra universes independent and
assume only a commutative scalar semiring, a possibly noncommutative algebra
semiring, a Hopf structure and cocommutativity. The group-algebra client over
`ZMod 1` also uses the cocommutative identity. The finite group is an example,
not a finiteness hypothesis of the generic result.

## References

* Mathlib, `RingTheory/HopfAlgebra/MonoidAlgebra` and
  `RingTheory/Coalgebra/MonoidAlgebra`, by Amelia Livingston: group-algebra
  Hopf and cocommutative coalgebra structures.
* `AlgebraicGroups.Algebra.HopfAlgebra.Antipode`: cocommutative antipode
  involutivity.
* `AlgebraicGroupsTest.Algebra.HopfAlgebra.Hom`: the two-transposition
  multiplication comparison for a group algebra.
-/

@[expose] public noncomputable section

namespace HopfAlgebraExamples

universe u v

section

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]

example : Function.Bijective (HopfAlgebra.antipode R (A := A)) :=
  (HopfAlgebra.antipode_involutive_of_isCocomm (R := R) (A := A)).bijective

example (a : A) : HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a :=
  HopfAlgebra.antipode_antipode_of_isCocomm (R := R) a

end

/-- The cocommutative identity recovers every element of the noncommutative group algebra
`ℕ[S₃]` after two antipodes. -/
theorem natPermutationGroupAlgebra_antipode_antipode
    (a : MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) :
    HopfAlgebra.antipode ℕ (HopfAlgebra.antipode ℕ a) = a :=
  HopfAlgebra.antipode_antipode_of_isCocomm (R := ℕ) a

/-- Every element of `ℕ[S₃]` is the antipode of another element. -/
theorem natPermutationGroupAlgebra_exists_antipode
    (a : MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) :
    ∃ b, HopfAlgebra.antipode ℕ b = a :=
  (HopfAlgebra.antipode_involutive_of_isCocomm
    (R := ℕ) (A := MonoidAlgebra ℕ (Equiv.Perm (Fin 3)))).surjective a

/-- The basis elements of `(0 1)` and `(1 2)` do not commute in `ℕ[S₃]`. -/
theorem natPermutationGroupAlgebra_transpositions_mul_ne :
    (MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1) 1 :
      MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) *
        MonoidAlgebra.single (Equiv.swap (1 : Fin 3) 2) 1 ≠
      MonoidAlgebra.single (Equiv.swap (1 : Fin 3) 2) 1 *
        MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1) 1 := by
  intro h
  simp only [MonoidAlgebra.single_mul_single, mul_one] at h
  have hg := MonoidAlgebra.single_left_injective (by decide : (1 : ℕ) ≠ 0) h
  have he := congrArg (fun g : Equiv.Perm (Fin 3) => g (0 : Fin 3)) hg
  have hn : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) (0 : Fin 3)) ≠
      ((Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) (0 : Fin 3)) := by decide
  exact hn he

/-- Cocommutative antipode involutivity also includes a group algebra over the zero ring. -/
theorem zeroRingPermutationGroupAlgebra_antipode_antipode
    (a : MonoidAlgebra (ZMod 1) (Equiv.Perm (Fin 3))) :
    HopfAlgebra.antipode (ZMod 1) (HopfAlgebra.antipode (ZMod 1) a) = a :=
  HopfAlgebra.antipode_antipode_of_isCocomm (R := ZMod 1) a

end HopfAlgebraExamples
