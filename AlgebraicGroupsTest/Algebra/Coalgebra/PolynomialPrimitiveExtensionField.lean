/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension.Polynomial.GroupLike
import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension.Polynomial.Module
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Field specializations of the polynomial primitive extension

For a field `K`, the scalar ring `K[X]` is a principal ideal domain. The
primitive-extension APIs recover the rational rank-one, nonflat example with
infinitely many group-like points. The parametrization applies to arbitrary
fields, not only `ℚ` or infinite fields: over `ZMod 2` there are exactly two points.
The module results hold more generally over commutative coefficient rings, and
the group-like equivalence only requires reducedness.
-/

open Polynomial TrivSqZeroExt

universe u

example (K : Type u) [Field K] : IsPrincipalIdealRing K[X] := inferInstance

example :
    Module.rank ℚ[X] (TrivSqZeroExt ℚ[X] (ℚ[X] ⧸ Ideal.span {(X ^ 2 : ℚ[X])})) = 1 :=
  polynomial_rank ℚ

example :
    ¬ Module.Flat ℚ[X] (TrivSqZeroExt ℚ[X] (ℚ[X] ⧸ Ideal.span {(X ^ 2 : ℚ[X])})) :=
  polynomial_not_flat ℚ

example :
    Infinite (GroupLike ℚ[X] (TrivSqZeroExt ℚ[X] (ℚ[X] ⧸ Ideal.span {(X ^ 2 : ℚ[X])}))) :=
  polynomialGroupLike_infinite ℚ

example (K : Type u) [Field K] [Fintype K] :
    Nat.card (GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) =
      Fintype.card K := by
  rw [polynomialGroupLike_natCard K, Nat.card_eq_fintype_card]

example :
    Nat.card (GroupLike (ZMod 2)[X]
      (TrivSqZeroExt (ZMod 2)[X] ((ZMod 2)[X] ⧸ Ideal.span {(X ^ 2 : (ZMod 2)[X])}))) = 2 := by
  rw [polynomialGroupLike_natCard (ZMod 2), Nat.card_zmod]
