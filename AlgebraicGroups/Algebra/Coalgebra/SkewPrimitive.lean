/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Skew-primitive elements

For group-like elements `g` and `h` of a coalgebra, the difference `g - h` is
`(g, h)`-skew-primitive: its counit is zero and its comultiplication is
`g ⊗ₜ[R] (g - h) + (g - h) ⊗ₜ[R] h`.

The scalars form a commutative semiring. Transport between skew-primitive
submodules requires only additive commutative monoids; the difference result
requires an additive commutative group. No multiplication on a carrier is required.
The canonical group-like and
skew-primitive predicates require the full `Coalgebra R C` class. The calculation
uses only linearity and the endpoint equations, not coassociativity or counitality.

## Main declarations

* `Coalgebra.skewPrimitiveMap`: linear transport along coalgebra maps, with
  coercion, identity and composition formulas.

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

universe u v w x

open Coalgebra TensorProduct

noncomputable section

namespace Coalgebra

variable {R : Type u} {D : Type v} {E : Type w} {F : Type x}
variable [CommSemiring R]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable [AddCommMonoid F] [Module R F] [Coalgebra R F]

/-- A coalgebra map transports the existing skew-primitive submodules.
This is a restriction of its underlying linear map, including zero counit. -/
def skewPrimitiveMap (H : D →ₗc[R] E) (g h : D) :
    skewPrimitive R g h →ₗ[R] skewPrimitive R (H g) (H h) :=
  LinearMap.codRestrict _
    (H.toLinearMap.comp (skewPrimitive R g h).subtype)
    (fun a => a.property.map H)

@[simp] theorem skewPrimitiveMap_apply (H : D →ₗc[R] E) (g h : D)
    (a : skewPrimitive R g h) :
    (skewPrimitiveMap H g h a : E) = H (a : D) := rfl

@[simp] theorem skewPrimitiveMap_id (g h : D) :
    skewPrimitiveMap (CoalgHom.id R D) g h = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

/-- Restriction to skew primitives commutes with composition. -/
theorem skewPrimitiveMap_comp (H : D →ₗc[R] E) (K : E →ₗc[R] F) (g h : D) :
    skewPrimitiveMap (K.comp H) g h =
      (skewPrimitiveMap K (H g) (H h)).comp (skewPrimitiveMap H g h) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

end Coalgebra

end

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
