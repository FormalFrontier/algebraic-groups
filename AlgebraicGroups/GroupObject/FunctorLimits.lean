/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Functors on internal monoids and groups

Transporting internal group objects commutes with forgetting to internal monoid objects.

A lax monoidal functor preserving limits of shape `J` induces a functor on
internal monoids preserving these limits, provided the source category has
limits of shape `J`. No limit-existence assumption is needed on the target.

The proof uses Mathlib's creation of limits by `Mon.forget`, its general
reflection-of-limits argument, and the defining underlying composite.

A monoidal functor between cartesian monoidal categories likewise preserves
these limits on internal group objects. The source forgetful functor preserves
limits, and the fully faithful target forgetful functor reflects them.

It also preserves zero morphisms: it preserves terminal objects, so Mathlib's
zero objects on internal groups and its terminal-preservation instance
supply `Functor.PreservesZeroMorphisms` for the induced functor.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

namespace Functor

section Cartesian

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

/-- Transporting group objects commutes with forgetting to monoid objects. -/
@[simp]
lemma mapGrp_comp_forget₂Mon (F : C ⥤ D) [F.Monoidal] :
    F.mapGrp ⋙ Grp.forget₂Mon D = Grp.forget₂Mon C ⋙ F.mapMon := rfl

end Cartesian

section Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A lax monoidal functor preserving limits of shape `J` also preserves them
on monoid objects, when the source category has limits of this shape. -/
instance preservesLimitsOfShape_mapMon (F : C ⥤ D) [F.LaxMonoidal]
    (J : Type u₃) [Category.{v₃} J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J F.mapMon := by
  let : PreservesLimitsOfShape J (F.mapMon ⋙ Mon.forget D) := by
    change PreservesLimitsOfShape J (Mon.forget C ⋙ F)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves F.mapMon (Mon.forget D)

end Monoidal

section Cartesian

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

/-- A monoidal functor preserving limits of shape `J` preserves them on group objects. -/
instance preservesLimitsOfShape_mapGrp (F : C ⥤ D) [F.Monoidal]
    (J : Type u₃) [Category.{v₃} J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J F.mapGrp := by
  let : PreservesLimitsOfShape J (F.mapGrp ⋙ Grp.forget₂Mon D) := by
    rw [mapGrp_comp_forget₂Mon]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves F.mapGrp (Grp.forget₂Mon D)

end Cartesian

end Functor

end CategoryTheory
