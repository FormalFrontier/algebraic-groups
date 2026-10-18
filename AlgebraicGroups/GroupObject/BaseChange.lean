/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
The Mathlib notice above applies to the unit-projection calculation adapted
from its identity-point smoothness proof. Modifications by Formal Frontier Agents:
generalize the calculation to monoid objects in slice categories.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Units under base change in slice categories

The unit of the stock transported monoid object projects to the original unit
composed with the base morphism. The Cartesian monoidal structures and the
transported monoid structure are the ones defined by Mathlib using pullbacks.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C]

attribute [local instance] cartesianMonoidalCategory braidedCategory monObjMkPullbackSnd

/-- The unit of a base-changed monoid object projects to the original unit. -/
@[reassoc]
theorem unit_pullback_fst {S S' G : C} (f : G ⟶ S) (β : S' ⟶ S)
    [MonObj (Over.mk f)] :
    η[Over.mk (pullback.snd f β)].left ≫ pullback.fst f β =
      β ≫ η[Over.mk f].left := by
  rw [show η[Over.mk (pullback.snd f β)] =
    Functor.LaxMonoidal.ε (Over.pullback β) ≫
      (Over.pullback β).map η[Over.mk f] from monObjMkPullbackSnd_one]
  rw [Over.comp_left, Category.assoc, Over.ε_pullback_left]
  change inv (pullback.snd (𝟙 _) β) ≫
      pullback.lift (pullback.fst (𝟙 _) β ≫ η[Over.mk f].left)
        (pullback.snd (𝟙 _) β) _ ≫ pullback.fst f β =
      β ≫ η[Over.mk f].left
  rw [pullback.lift_fst]
  rw [show pullback.fst (𝟙 _) β = pullback.snd (𝟙 _) β ≫ β by
    simpa using (pullback.condition :
      pullback.fst (𝟙 _) β ≫ 𝟙 _ = pullback.snd (𝟙 _) β ≫ β)]
  simp

end CategoryTheory.Over
