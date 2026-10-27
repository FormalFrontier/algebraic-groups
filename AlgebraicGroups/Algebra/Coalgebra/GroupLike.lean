/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.Algebra.Group.Idempotent

/-!
# Group-like elements with unit counit

In a coalgebra over a commutative semiring, an element whose comultiplication is its tensor
square is group-like if its counit is a unit. The carrier is an additive commutative monoid
with a module structure; no multiplication on it is required. The scalar and carrier
universes are independent.

Milne's character-coordinate normalization starts with an invertible element of a Hopf
algebra. Here the unit condition is imposed only on its scalar counit. The counit law forces
that scalar to be idempotent, so Mathlib's unit-idempotent cancellation applies.

## References

* J. S. Milne, *Algebraic Groups* (2017), §4g, p. 93, unnumbered counit-normalization calculation.
* Mathlib's `Mathlib.RingTheory.Coalgebra.GroupLike`, by Yaël Dillies and Michał Mrugała,
  for the normalized group-like predicate; `Mathlib.RingTheory.Coalgebra.Basic`, by
  Ali Ramsey and Eric Wieser, for counitality; and `Mathlib.Algebra.Group.Idempotent`,
  by Christopher Hoskin, for `IsIdempotentElem.iff_eq_one_of_isUnit`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- An element with tensor-square comultiplication and unit counit is group-like.

This generalizes the counit-normalization calculation in J. S. Milne, *Algebraic Groups*
(2017), §4g, p. 93: the unit condition is on the scalar counit, and the coalgebra carrier
need not have multiplication. -/
theorem IsGroupLikeElem.of_isUnit_counit {a : C}
    (hε : IsUnit (Coalgebra.counit (R := R) a))
    (hΔ : Coalgebra.comul (R := R) a = a ⊗ₜ[R] a) :
    IsGroupLikeElem R a := by
  have hsmul : Coalgebra.counit (R := R) a • a = a := by
    have h := Coalgebra.rTensor_counit_comul (R := R) a
    rw [hΔ, LinearMap.rTensor_tmul] at h
    simpa only [TensorProduct.lid_tmul, one_smul] using
      congrArg (TensorProduct.lid R C) h
  have hidem : IsIdempotentElem (Coalgebra.counit (R := R) a) := by
    simpa only [IsIdempotentElem, LinearMap.map_smul, smul_eq_mul] using
      congrArg (Coalgebra.counit (R := R)) hsmul
  exact ⟨(IsIdempotentElem.iff_eq_one_of_isUnit hε).mp hidem, hΔ⟩
