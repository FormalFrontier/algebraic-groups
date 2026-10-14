/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroupsTest.Algebra.Coalgebra.CounitRange

/-!
# Scalar-action witnesses for existing coalgebras

The scalar coalgebra over `ℕ` separates the scalars two and five at seven,
both on the coalgebra and after applying the counit. This uses a commutative
semiring that is not a ring.

On the existing ideal coalgebra `(3)` over `ZMod 6`, the distinct scalars zero
and two act equally. Their products with every counit value are also equal.
The empty diagonal coalgebra over `ℕ` gives the zero-module boundary: zero and
one have the same action and the same products with all counit values.

## References

The ideal coalgebra and its identity action are reused from
`AlgebraicGroupsTest.Algebra.Coalgebra.CounitRange`. Mathlib supplies the scalar
and empty diagonal coalgebras and linearity of the counit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Coalgebra

namespace CoalgebraTest

/-- Two and five have different actions on seven in the natural-number scalar
coalgebra, and are still distinguished after applying its counit. -/
theorem natural_scalar_actions_separated :
    (2 : ℕ) • (7 : ℕ) ≠ (5 : ℕ) • 7 ∧
    (2 : ℕ) * counit (R := ℕ) (7 : ℕ) ≠ 5 * counit (R := ℕ) (7 : ℕ) := by
  constructor
  · decide
  · simpa only [CommSemiring.counit_apply] using (show (2 : ℕ) * 7 ≠ 5 * 7 by decide)

/-- The semiring scalar coalgebra has faithful scalar action on its counit image. -/
example : FaithfulSMul ℕ (LinearMap.range (counit (R := ℕ) (A := ℕ))) :=
  (Coalgebra.faithfulSMul_iff_counit_range ℕ ℕ).mp inferInstance

/-- The two and five scalar actions remain distinguishable on the counit image. -/
example : ¬∀ x : LinearMap.range (counit (R := ℕ) (A := ℕ)),
    (2 : ℕ) • x = (5 : ℕ) • x := by
  intro h
  exact natural_scalar_actions_separated.1
    ((Coalgebra.smul_eq_smul_iff_on_counit_range ℕ ℕ).mpr h 7)

section ThreeIdeal

attribute [local instance] spanThreeCoalgebra

/-- Zero and two are distinct scalars with the same action on the ideal
coalgebra `(3)` over `ZMod 6` and the same products with every counit value. -/
theorem span_three_distinct_scalars_equal_actions :
    (0 : ZMod 6) ≠ 2 ∧
    (∀ d : Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)),
      (0 : ZMod 6) • d = (2 : ZMod 6) • d) ∧
    (∀ d : Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)),
      (0 : ZMod 6) * counit (R := ZMod 6) d = 2 * counit (R := ZMod 6) d) := by
  have haction (d : Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) :
      (0 : ZMod 6) • d = (2 : ZMod 6) • d := by
    have hthree := span_three_identity_action_not_faithful.1 d
    have htwo : (2 : ZMod 6) = 3 - 1 := by decide
    rw [zero_smul, htwo, sub_smul, hthree, one_smul, sub_self]
  refine ⟨by decide, haction, ?_⟩
  intro d
  simpa only [map_smul, smul_eq_mul] using
    congrArg (counit (R := ZMod 6)) (haction d)

/-- The scalar action on the proper counit-image ideal of `(3)` is not faithful. -/
example : ¬FaithfulSMul (ZMod 6)
    (LinearMap.range (counit (R := ZMod 6)
      (A := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))))) := by
  exact fun h ↦ span_three_identity_action_not_faithful.2.2.2
    ((Coalgebra.faithfulSMul_iff_counit_range (ZMod 6)
      (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))).mpr h)

/-- Equality on the counit image recovers equality of the zero and two scalar actions. -/
example : ∀ d : Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)),
    (0 : ZMod 6) • d = (2 : ZMod 6) • d := by
  apply (Coalgebra.smul_eq_smul_iff_on_counit_range (ZMod 6)
    (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))).mpr
  intro x
  obtain ⟨d, rfl⟩ := (counit (R := ZMod 6)
    (A := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))).surjective_rangeRestrict x
  apply Subtype.ext
  simpa only [Submodule.coe_smul, smul_eq_mul, LinearMap.codRestrict_apply] using
    span_three_distinct_scalars_equal_actions.2.2 d

end ThreeIdeal

/-- On the empty natural-number diagonal coalgebra, zero and one are distinct
scalars but all their actions and products with counit values agree. -/
theorem empty_natural_distinct_scalars_equal_actions :
    (0 : ℕ) ≠ 1 ∧
    (∀ c : Fin 0 →₀ ℕ, (0 : ℕ) • c = (1 : ℕ) • c) ∧
    (∀ c : Fin 0 →₀ ℕ,
      (0 : ℕ) * counit (R := ℕ) c = 1 * counit (R := ℕ) c) := by
  have haction (c : Fin 0 →₀ ℕ) : (0 : ℕ) • c = (1 : ℕ) • c :=
    Subsingleton.elim _ _
  refine ⟨by decide, haction, ?_⟩
  intro c
  simpa only [map_smul, smul_eq_mul] using
    congrArg (counit (R := ℕ)) (haction c)

end CoalgebraTest
