/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Unit-counit normalization in a group algebra

Over an arbitrary field `k`, the group algebra on `Multiplicative ℤ` has Mathlib's full
Hopf algebra and inherited coalgebra structures. The basis element at integer weight `1`
is a unit with tensor-square comultiplication and unit counit, distinct from zero and the
algebra unit at weight `0`. Its normalization uses the coalgebra criterion with those same
counit-unit and comultiplication inputs.

Zero satisfies the tensor-square equation in the same coalgebra, but its counit is not a
unit and it is not group-like.

## References

Mathlib's `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, by Amelia Livingston, supplies
its full group-algebra Hopf structure. The group-like basis elements and their units use
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra` and `Mathlib.RingTheory.HopfAlgebra.GroupLike`,
by Amelia Livingston, Yaël Dillies and Michał Mrugała.
-/

@[expose] public section

universe u

open scoped TensorProduct

private abbrev GroupAlgebra (k : Type u) [Field k] :=
  MonoidAlgebra k (Multiplicative ℤ)

private noncomputable abbrev generator (k : Type u) [Field k] : GroupAlgebra k :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k)

private theorem generator_inputs (k : Type u) [Field k] :
    IsUnit (Coalgebra.counit (R := k) (generator k)) ∧
      Coalgebra.comul (R := k) (generator k) = generator k ⊗ₜ[k] generator k ∧
      IsUnit (generator k) ∧ generator k ≠ 0 ∧ generator k ≠ 1 := by
  have ht : IsGroupLikeElem k (generator k) :=
    MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k)
      (Multiplicative.ofAdd (1 : ℤ))
  refine ⟨?_, ht.comul_eq_tmul_self, ht.isUnit, ?_, ?_⟩
  · rw [ht.counit_eq_one]
    exact isUnit_one
  · intro h
    have hc := congrArg
      (fun x : GroupAlgebra k => x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
    exact (one_ne_zero : (1 : k) ≠ 0) (by
      simpa only [generator, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc)
  · intro h
    have hi : Multiplicative.ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ) :=
      fun h => (one_ne_zero : (1 : ℤ) ≠ 0) (ofAdd_eq_one.mp h)
    have hc := congrArg
      (fun x : GroupAlgebra k => x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
    exact (one_ne_zero : (1 : k) ≠ 0) (by
      simpa only [generator, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hi] using hc)

private theorem generator_isGroupLikeElem (k : Type u) [Field k] :
    IsGroupLikeElem k (generator k) := by
  exact IsGroupLikeElem.of_isUnit_counit
    (generator_inputs k).1 (generator_inputs k).2.1

private theorem zero_boundary (k : Type u) [Field k] :
    Coalgebra.comul (R := k) (0 : GroupAlgebra k) =
        (0 : GroupAlgebra k) ⊗ₜ[k] (0 : GroupAlgebra k) ∧
      ¬ IsUnit (Coalgebra.counit (R := k) (0 : GroupAlgebra k)) ∧
      ¬ IsGroupLikeElem k (0 : GroupAlgebra k) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_zero, TensorProduct.zero_tmul]
  · simpa only [map_zero] using (not_isUnit_zero : ¬ IsUnit (0 : k))
  · intro h
    exact h.ne_zero rfl
