/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Comultiplication of spans of group-like elements

The linear span of group-like elements is closed under comultiplication into the image of
its tensor square. The proof uses Mathlib's span universal property: the inverse image of
the tensor-square image under the linear comultiplication contains every generator, with
its tensor square as a witness.

This is an image-closure statement over a commutative semiring. It does not assert that
the tensor inclusion is injective or construct a coalgebra structure on the span.
-/

@[expose] public section

open TensorProduct

universe u v

namespace Coalgebra

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Comultiplication of an element in the span of group-like elements belongs to the image
of the tensor square of that span in the ambient tensor square. -/
theorem comul_mem_range_mapIncl_span_of_isGroupLikeElem
    {s : Set C} (hs : ∀ y ∈ s, IsGroupLikeElem R y)
    {x : C} (hx : x ∈ Submodule.span R s) :
    comul (R := R) x ∈ LinearMap.range
      (TensorProduct.mapIncl (Submodule.span R s) (Submodule.span R s)) := by
  have hspan : Submodule.span R s ≤
      (LinearMap.range (TensorProduct.mapIncl (Submodule.span R s) (Submodule.span R s))).comap
        (comul (R := R)) := by
    apply Submodule.span_le.mpr
    intro y hy
    change comul (R := R) y ∈ LinearMap.range
      (TensorProduct.mapIncl (Submodule.span R s) (Submodule.span R s))
    rw [(hs y hy).comul_eq_tmul_self]
    exact ⟨(⟨y, Submodule.subset_span hy⟩ : Submodule.span R s) ⊗ₜ[R]
      (⟨y, Submodule.subset_span hy⟩ : Submodule.span R s), rfl⟩
  exact hspan hx

end Coalgebra
