/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Word
public import AlgebraicGroups.GroupObject.CommutatorWord
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutator words and free-group evaluation

The commutator word of a finite fan is the evaluation of the product of the corresponding
commutators in a free group. For a given limiting fan, the universal property of word evaluation
therefore characterizes the commutator-word morphism by its values on all tuples.

## Main results

* `CategoryTheory.GrpObj.commutatorWord_eq_freeGroup_lift` identifies commutator-word evaluation
  with `FreeGroup.lift`.
* `CategoryTheory.GrpObj.eq_commutatorWord_iff` characterizes the commutator-word morphism of a
  given limiting fan by evaluation on arbitrary test objects.

This AI-assisted formalization uses Mathlib's homomorphism APIs and the
commutator-word API of `AlgebraicGroups.GroupObject.CommutatorWord`.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrpObj

open Limits
open scoped CategoryTheory.MonObj commutatorElement

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G : C} [GrpObj G]

/-- The commutator word is the free-group evaluation of the product of the commutators of the
paired generators. -/
theorem commutatorWord_eq_freeGroup_lift {n : ℕ}
    (P : Fan (fun _ : Fin n × Fin 2 => G)) :
    commutatorWord P =
      FreeGroup.lift P.proj
        ((List.ofFn (fun i : Fin n =>
          ⁅FreeGroup.of (i, (0 : Fin 2)), FreeGroup.of (i, (1 : Fin 2))⁆)).prod) := by
  simp [commutatorWord_eq, map_list_prod, Function.comp_def]

/-- A morphism from a given limiting fan is its commutator word exactly when its value on every
tuple is the evaluation of the product of the commutators of the paired free generators. -/
theorem eq_commutatorWord_iff {n : ℕ}
    (P : Fan (fun _ : Fin n × Fin 2 => G)) (hP : IsLimit P) (m : P.pt ⟶ G) :
    m = commutatorWord P ↔
      ∀ (T : C) (a : Fin n × Fin 2 → (T ⟶ G)),
        Fan.IsLimit.lift hP a ≫ m =
          FreeGroup.lift a
            ((List.ofFn (fun i : Fin n =>
              ⁅FreeGroup.of (i, (0 : Fin 2)), FreeGroup.of (i, (1 : Fin 2))⁆)).prod) := by
  have hcomm : ∀ (T : C) (a : Fin n × Fin 2 → (T ⟶ G)),
      Fan.IsLimit.lift hP a ≫ commutatorWord P =
        FreeGroup.lift a
          ((List.ofFn (fun i : Fin n =>
            ⁅FreeGroup.of (i, (0 : Fin 2)), FreeGroup.of (i, (1 : Fin 2))⁆)).prod) := by
    intro T a
    rw [commutatorWord_eq_freeGroup_lift]
    exact lift_comp_freeGroup_lift P hP _ a
  constructor
  · rintro rfl
    exact hcomm
  · intro hm
    obtain ⟨_, _, huniq⟩ := existsUnique_word_morphism P hP
      ((List.ofFn (fun i : Fin n =>
        ⁅FreeGroup.of (i, (0 : Fin 2)), FreeGroup.of (i, (1 : Fin 2))⁆)).prod)
    exact (huniq m hm).trans (huniq (commutatorWord P) hcomm).symm

end CategoryTheory.GrpObj
