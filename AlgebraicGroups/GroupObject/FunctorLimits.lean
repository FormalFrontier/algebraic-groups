/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Limit preservation for functors on monoid objects

A lax monoidal functor preserving limits of shape `J` induces a functor on
internal monoids preserving these limits, provided the source category has
limits of shape `J`. No limit-existence assumption is needed on the target.

The proof uses Mathlib's creation of limits by `Mon.forget`, its general
reflection-of-limits argument, and the defining underlying composite.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

namespace Functor

/-- A lax monoidal functor preserving limits of shape `J` also preserves them
on monoid objects, when the source category has limits of this shape. -/
instance preservesLimitsOfShape_mapMon (F : C ⥤ D) [F.LaxMonoidal]
    (J : Type u₃) [Category.{v₃} J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J F.mapMon := by
  letI : PreservesLimitsOfShape J (F.mapMon ⋙ Mon.forget D) := by
    change PreservesLimitsOfShape J (Mon.forget C ⋙ F)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves F.mapMon (Mon.forget D)

end Functor

end CategoryTheory
