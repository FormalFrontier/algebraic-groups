/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Differences of group-like elements

For group-like elements `g` and `h` of a coalgebra, the difference `g - h` is
`(g, h)`-skew-primitive: its counit is zero and its comultiplication is
`g ⊗ₜ[R] (g - h) + (g - h) ⊗ₜ[R] h`.

The scalars form a commutative semiring and the carrier is an additive commutative
group; no multiplication on the carrier is required. The canonical group-like and
skew-primitive predicates require the full `Coalgebra R C` class. The calculation
uses only linearity and the endpoint equations, not coassociativity or counitality.

## Main declarations

* `IsGroupLikeElem.isSkewPrimitiveElem_sub`: the difference of group-like elements
  is skew-primitive with those ordered endpoints.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories* (2015),
  the reference for Mathlib's skew-primitive development.
* Mathlib's `Mathlib.RingTheory.Coalgebra.Primitive`, formalized by Robert Hawkins,
  and `Mathlib.RingTheory.Coalgebra.GroupLike`, formalized by Yaël Dillies and
  Michał Mrugała, for the canonical predicates and their field APIs.
-/

@[expose] public section

universe u v

open Coalgebra TensorProduct

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommGroup C] [Module R C] [Coalgebra R C] {g h : C}

/-- The difference of group-like elements `g` and `h` is `(g, h)`-skew-primitive. -/
theorem IsGroupLikeElem.isSkewPrimitiveElem_sub (hg : IsGroupLikeElem R g)
    (hh : IsGroupLikeElem R h) : Coalgebra.IsSkewPrimitiveElem R g h (g - h) where
  counit_eq_zero := by
    calc
      counit (R := R) (g - h) = counit (R := R) (h - h) := by
        simp only [sub_eq_add_neg, map_add, hg.counit_eq_one, hh.counit_eq_one]
      _ = 0 := by rw [sub_self, map_zero]
  comul_eq_tmul_add_tmul := by
    rw [map_sub, hg.comul_eq_tmul_self, hh.comul_eq_tmul_self, tmul_sub, sub_tmul,
      sub_add_sub_cancel]
