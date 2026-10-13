/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.BaseChange
public import AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Clients of extension of the counit ideal

The infinite coalgebra `ℕ →₀ ℕ` is extended to the infinite commutative semiring
`MonoidAlgebra ℕ ℕ`; neither scalar type is a ring. Identity scalar extension
and the zero scalar semiring are included.

The proper nonzero ideal `(3)` in `ZMod 6` carries the existing idempotent-ideal
coalgebra with counit inclusion. Its generator has counit three, not one.
Extending scalars by the canonical projections to `ZMod 3` and `ZMod 2` gives
counit ideal zero and the unit ideal, respectively. The zero-ideal assertion is
only about the counit range; no tensor-product subsingleton assertion is made.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct
open Coalgebra

namespace CoalgebraTest

/-- Extending the infinite natural-number coalgebra to an infinite non-ring
commutative scalar semiring preserves its unit counit ideal. -/
theorem natural_monoidAlgebra_counit_range :
    (LinearMap.range (counit (R := MonoidAlgebra ℕ ℕ)
      (A := MonoidAlgebra ℕ ℕ ⊗[ℕ] (ℕ →₀ ℕ))) : Ideal (MonoidAlgebra ℕ ℕ)) = ⊤ := by
  rw [counit_range_baseChange, counit_range_eq_top_of_free, Ideal.map_top]

/-- A pure tensor in the infinite non-ring scalar-extension example has counit seven. -/
theorem natural_monoidAlgebra_counit_seven :
    counit (R := MonoidAlgebra ℕ ℕ)
      ((1 : MonoidAlgebra ℕ ℕ) ⊗ₜ[ℕ] (Finsupp.single 37 7 : ℕ →₀ ℕ)) = 7 := by
  simp [TensorProduct.counit_tmul, Algebra.smul_def]

/-- Scalar extension along the identity leaves the counit ideal unchanged. -/
theorem identity_counit_range (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    (LinearMap.range (counit (R := R) (A := R ⊗[R] C)) : Ideal R) =
      LinearMap.range (counit (R := R) (A := C)) := by
  simpa using counit_range_baseChange R R C

/-- Extension to the zero scalar semiring has zero counit ideal. -/
theorem zero_scalar_counit_range :
    (LinearMap.range (counit (R := ZMod 1)
      (A := ZMod 1 ⊗[ℕ] (ℕ →₀ ℕ))) : Ideal (ZMod 1)) = ⊥ := by
  rw [counit_range_baseChange]
  exact Subsingleton.elim _ _

section IdempotentIdeal

/-- Three is an idempotent scalar in `ZMod 6`. -/
theorem three_idempotent : IsIdempotentElem (3 : ZMod 6) := by
  change (3 : ZMod 6) * 3 = 3
  decide

noncomputable local instance :
    Coalgebra (ZMod 6) (Ideal.span ({3} : Set (ZMod 6))) := three_idempotent.coalgebraSpan

/-- The counit ideal of the idempotent principal ideal coalgebra on `(3)` is `(3)`. -/
theorem three_counit_range :
    (LinearMap.range (counit (R := ZMod 6)
      (A := Ideal.span ({3} : Set (ZMod 6)))) : Ideal (ZMod 6)) =
        Ideal.span ({3} : Set (ZMod 6)) := by
  rw [three_idempotent.coalgebraSpan_counit, Submodule.range_subtype]

/-- The generator of the proper ideal coalgebra has counit three. -/
theorem three_generator_counit :
    counit (R := ZMod 6) (Ideal.spanSingletonGenerator (3 : ZMod 6)) = 3 :=
  three_idempotent.coalgebraSpan_counit_apply _

/-- The initial counit ideal in `ZMod 6` is nonzero and proper. -/
theorem three_counit_range_proper :
    (LinearMap.range (counit (R := ZMod 6)
      (A := Ideal.span ({3} : Set (ZMod 6)))) : Ideal (ZMod 6)) ≠ ⊥ ∧
    (LinearMap.range (counit (R := ZMod 6)
      (A := Ideal.span ({3} : Set (ZMod 6)))) : Ideal (ZMod 6)) ≠ ⊤ := by
  rw [three_counit_range]
  constructor
  · rw [ne_eq, Ideal.span_singleton_eq_bot]
    decide
  · rw [ne_eq, Ideal.span_singleton_eq_top]
    exact (ZMod.isUnit_iff_coprime 3 6).not.mpr (by decide)

section ModThree

local instance : Algebra (ZMod 6) (ZMod 3) :=
  (ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)).toAlgebra

/-- The projection to `ZMod 3` kills the counit ideal of the coalgebra on `(3)`. -/
theorem three_baseChange_mod_three_counit_range :
    (LinearMap.range (counit (R := ZMod 3)
      (A := ZMod 3 ⊗[ZMod 6] Ideal.span ({3} : Set (ZMod 6)))) : Ideal (ZMod 3)) = ⊥ := by
  rw [counit_range_baseChange, three_counit_range, Ideal.map_span, Set.image_singleton]
  have h : algebraMap (ZMod 6) (ZMod 3) 3 = 0 := by
    rw [map_ofNat]
    decide
  rw [h]
  simp

end ModThree

section ModTwo

local instance : Algebra (ZMod 6) (ZMod 2) :=
  (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)).toAlgebra

/-- The projection to `ZMod 2` sends the counit ideal of the coalgebra on `(3)`
to the unit ideal. -/
theorem three_baseChange_mod_two_counit_range :
    (LinearMap.range (counit (R := ZMod 2)
      (A := ZMod 2 ⊗[ZMod 6] Ideal.span ({3} : Set (ZMod 6)))) : Ideal (ZMod 2)) = ⊤ := by
  rw [counit_range_baseChange, three_counit_range, Ideal.map_span, Set.image_singleton]
  have h : algebraMap (ZMod 6) (ZMod 2) 3 = 1 := by
    rw [map_ofNat]
    decide
  rw [h]
  simp

end ModTwo
end IdempotentIdeal

end CoalgebraTest
