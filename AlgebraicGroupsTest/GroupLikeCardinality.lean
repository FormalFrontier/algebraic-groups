/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCardinality

import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Group-like cardinality in diagonal coalgebras

The diagonal coalgebra on `Fin 2 →₀ ℤ` instantiates the cardinal bound, the three
finite-rank consequences, and the module-finite instance and consequences. Its two
basis vectors are group-like, so the natural-number bound is sharp. The coefficient
ring is not a field.

The zero coalgebra `Empty →₀ ℤ` has no group-like elements; no nontriviality assumption
on the coalgebra is needed. In contrast, `ℕ →₀ ℤ` has infinitely many group-like
basis vectors, rank at least `ℵ₀`, and is not module-finite. Both its `Nat.card` of
group-likes and its `finrank` are zero. Those natural numbers alone do not express
finiteness, and the finite-rank consequences do not apply to this example.

Over the non-domain `ℤ × ℤ`, the diagonal coalgebra on `Fin 2 →₀ (ℤ × ℤ)` is finite
free, torsion-free for regular scalars, and has rank two. Orthogonal idempotents give
an injective family of four group-like elements, disproving the cardinal bound when
the domain hypothesis is removed. This example uses only a cardinal lower bound,
not finiteness or a natural-number cardinal bound for all group-like elements.

## References

* Mathlib's group-like carrier and linear independence API in
  `Mathlib.RingTheory.Coalgebra.GroupLike`, by Yaël Dillies and Michał Mrugała.
* Mathlib's diagonal Finsupp coalgebra in `Mathlib.RingTheory.Coalgebra.Basic`,
  by Ali Ramsey and Eric Wieser.
* Mathlib's Finsupp basis and free-module APIs in
  `Mathlib.LinearAlgebra.Finsupp.VectorSpace` and
  `Mathlib.LinearAlgebra.FreeModule.Basic`, by Johannes Hölzl and Riccardo Brasca,
  and its rank API in `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`,
  by Kim Morrison.
-/

@[expose] public section

universe v

open scoped Cardinal TensorProduct

namespace GroupLike

noncomputable section

/-- A basis vector of the diagonal integer coalgebra, bundled as group-like. -/
private def singleGroupLike (ι : Type v) (i : ι) : GroupLike ℤ (ι →₀ ℤ) where
  val := Finsupp.single i 1
  isGroupLikeElem_val := by
    constructor <;> simp

private theorem singleGroupLike_injective (ι : Type v) :
    Function.Injective (singleGroupLike ι) := by
  intro i j h
  exact (Finsupp.linearIndependent_single_one ℤ ι).injective
    (congrArg (val : GroupLike ℤ (ι →₀ ℤ) → ι →₀ ℤ) h)

/-! ## Finite diagonal coalgebra over the integers -/

example : ¬ IsField ℤ := by
  intro h
  obtain ⟨z, hz⟩ := h.mul_inv_cancel (by decide : (2 : ℤ) ≠ 0)
  exact (by decide : ¬ ((2 : ℤ) = 1 ∨ (2 : ℤ) = -1))
    (Int.eq_one_or_neg_one_of_mul_eq_one hz)

example : Module.IsTorsionFree ℤ (Fin 2 →₀ ℤ) := inferInstance

example : Module.Finite ℤ (Fin 2 →₀ ℤ) :=
  Module.Finite.of_basis (Finsupp.basisSingleOne : Module.Basis (Fin 2) ℤ (Fin 2 →₀ ℤ))

example : Module.rank ℤ (Fin 2 →₀ ℤ) = 2 := by
  simp

private theorem rank_fin_two_finsupp_int_lt_aleph0 :
    Module.rank ℤ (Fin 2 →₀ ℤ) < ℵ₀ := by
  simp

example : Cardinal.mk (GroupLike ℤ (Fin 2 →₀ ℤ)) ≤ 2 := by
  simpa using GroupLike.cardinalMk_le_rank ℤ (Fin 2 →₀ ℤ)

example : Finite (GroupLike ℤ (Fin 2 →₀ ℤ)) :=
  GroupLike.finite_of_rank_lt_aleph0 ℤ (Fin 2 →₀ ℤ) rank_fin_two_finsupp_int_lt_aleph0

example : Nat.card (GroupLike ℤ (Fin 2 →₀ ℤ)) ≤ 2 := by
  simpa using GroupLike.nat_card_le_finrank_of_rank_lt_aleph0 ℤ (Fin 2 →₀ ℤ)
    rank_fin_two_finsupp_int_lt_aleph0

example : Set.Finite {c : Fin 2 →₀ ℤ | IsGroupLikeElem ℤ c} :=
  GroupLike.setFinite_of_rank_lt_aleph0 ℤ (Fin 2 →₀ ℤ) rank_fin_two_finsupp_int_lt_aleph0

-- The module-finite specialization supplies the canonical `GroupLike.instFinite` instance.
example : Finite (GroupLike ℤ (Fin 2 →₀ ℤ)) := inferInstance

example : Nat.card (GroupLike ℤ (Fin 2 →₀ ℤ)) ≤ 2 := by
  simpa using GroupLike.nat_card_le_finrank ℤ (Fin 2 →₀ ℤ)

example : Set.Finite {c : Fin 2 →₀ ℤ | IsGroupLikeElem ℤ c} :=
  GroupLike.setFinite ℤ (Fin 2 →₀ ℤ)

/-- The diagonal rank-two integer coalgebra has exactly two group-like elements.
The cardinality API gives the upper bound, and the two basis vectors give the lower bound. -/
theorem nat_card_fin_two_finsupp_int : Nat.card (GroupLike ℤ (Fin 2 →₀ ℤ)) = 2 := by
  apply Nat.le_antisymm
  · simpa using GroupLike.nat_card_le_finrank ℤ (Fin 2 →₀ ℤ)
  · simpa using Nat.card_le_card_of_injective
      (singleGroupLike (Fin 2)) (singleGroupLike_injective (Fin 2))

/-! ## Zero coalgebra -/

example : Module.rank ℤ (Empty →₀ ℤ) = 0 := by
  simp

example : IsEmpty (GroupLike ℤ (Empty →₀ ℤ)) := by
  refine ⟨fun g ↦ ?_⟩
  apply g.isGroupLikeElem_val.ne_zero
  ext i
  exact Empty.elim i

-- The same cardinality theorem applies without a `Nontrivial` coalgebra instance.
example : Cardinal.mk (GroupLike ℤ (Empty →₀ ℤ)) = 0 := by
  apply le_antisymm
  · simpa using GroupLike.cardinalMk_le_rank ℤ (Empty →₀ ℤ)
  · exact zero_le

/-! ## Infinite diagonal coalgebra -/

private theorem infinite_groupLike_nat_finsupp_int : Infinite (GroupLike ℤ (ℕ →₀ ℤ)) :=
  Infinite.of_injective (singleGroupLike ℕ) (singleGroupLike_injective ℕ)

example : ∃ f : ℕ → GroupLike ℤ (ℕ →₀ ℤ), Function.Injective f :=
  ⟨singleGroupLike ℕ, singleGroupLike_injective ℕ⟩

example : Infinite (GroupLike ℤ (ℕ →₀ ℤ)) := infinite_groupLike_nat_finsupp_int

example : ℵ₀ ≤ Module.rank ℤ (ℕ →₀ ℤ) :=
  (Finsupp.linearIndependent_single_one ℤ ℕ).aleph0_le_rank

example : ¬ Module.Finite ℤ (ℕ →₀ ℤ) := by
  intro h
  let := h
  have hnat : Finite ℕ := (Finsupp.linearIndependent_single_one ℤ ℕ).finite
  exact hnat.false

example : Nat.card (GroupLike ℤ (ℕ →₀ ℤ)) = 0 := by
  let := infinite_groupLike_nat_finsupp_int
  exact Nat.card_eq_zero_of_infinite

example : Module.finrank ℤ (ℕ →₀ ℤ) = 0 := by
  simpa using Module.finrank_eq_nat_card_basis
    (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ))

-- Only the unrestricted cardinal bound is applied to this infinite-rank example.
example : Cardinal.mk (GroupLike ℤ (ℕ →₀ ℤ)) ≤ Module.rank ℤ (ℕ →₀ ℤ) :=
  GroupLike.cardinalMk_le_rank ℤ (ℕ →₀ ℤ)

end

end GroupLike

namespace Coalgebra

noncomputable section

/-! ## Domain boundary -/

private abbrev ProductRing := ℤ × ℤ

private abbrev BinaryDiagonal := Fin 2 →₀ ProductRing

private def firstIdempotent : ProductRing := (1, 0)

private def secondIdempotent : ProductRing := (0, 1)

private lemma first_add_second : firstIdempotent + secondIdempotent = 1 := by
  apply Prod.ext <;> simp [firstIdempotent, secondIdempotent]

private lemma first_mul_first : firstIdempotent * firstIdempotent = firstIdempotent := by
  apply Prod.ext <;> simp [firstIdempotent]

private lemma second_mul_second : secondIdempotent * secondIdempotent = secondIdempotent := by
  apply Prod.ext <;> simp [secondIdempotent]

private lemma first_mul_second : firstIdempotent * secondIdempotent = 0 := by
  apply Prod.ext <;> simp [firstIdempotent, secondIdempotent]

private lemma second_mul_first : secondIdempotent * firstIdempotent = 0 := by
  rw [mul_comm, first_mul_second]

private lemma first_ne_zero : firstIdempotent ≠ 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  simp [firstIdempotent] at hfst

private lemma second_ne_zero : secondIdempotent ≠ 0 := by
  intro h
  have hsnd := congrArg Prod.snd h
  simp [secondIdempotent] at hsnd

private lemma productRing_not_isDomain : ¬ IsDomain ProductRing := by
  intro h
  let := h
  exact (mul_eq_zero.mp first_mul_second).elim first_ne_zero second_ne_zero

private def mixedVector (p : Fin 2 × Fin 2) : BinaryDiagonal :=
  firstIdempotent • Finsupp.single p.1 1 + secondIdempotent • Finsupp.single p.2 1

private lemma mixedVector_counit (p : Fin 2 × Fin 2) :
    Coalgebra.counit (R := ProductRing) (mixedVector p) = 1 := by
  simp [mixedVector, first_add_second]

private lemma comul_single_one (i : Fin 2) :
    Coalgebra.comul (R := ProductRing) (Finsupp.single i (1 : ProductRing) : BinaryDiagonal) =
      (Finsupp.single i 1 : BinaryDiagonal) ⊗ₜ[ProductRing] Finsupp.single i 1 := by
  simp

private lemma mixedVector_comul (p : Fin 2 × Fin 2) :
    Coalgebra.comul (R := ProductRing) (mixedVector p) =
      mixedVector p ⊗ₜ[ProductRing] mixedVector p := by
  simp only [mixedVector, map_add, map_smul, comul_single_one]
  symm
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul_smul, first_mul_first, first_mul_second,
    second_mul_first, second_mul_second, zero_smul, add_zero, zero_add]

private def mixedGroupLike (p : Fin 2 × Fin 2) : GroupLike ProductRing BinaryDiagonal where
  val := mixedVector p
  isGroupLikeElem_val := ⟨mixedVector_counit p, mixedVector_comul p⟩

private lemma mixedVector_fst (p : Fin 2 × Fin 2) (k : Fin 2) :
    (mixedVector p k).1 = if p.1 = k then (1 : ℤ) else 0 := by
  classical
  by_cases hi : p.1 = k <;> by_cases hj : p.2 = k <;>
    simp [mixedVector, firstIdempotent, secondIdempotent, smul_eq_mul, hi, hj]

private lemma mixedVector_snd (p : Fin 2 × Fin 2) (k : Fin 2) :
    (mixedVector p k).2 = if p.2 = k then (1 : ℤ) else 0 := by
  classical
  by_cases hi : p.1 = k <;> by_cases hj : p.2 = k <;>
    simp [mixedVector, firstIdempotent, secondIdempotent, smul_eq_mul, hi, hj]

private lemma mixedVector_injective : Function.Injective mixedVector := by
  intro p q h
  apply Prod.ext
  · by_contra hp
    have hqp : q.1 ≠ p.1 := Ne.symm hp
    have hfst := congrArg (fun c : BinaryDiagonal => (c p.1).1) h
    simp [mixedVector_fst, hqp] at hfst
  · by_contra hp
    have hqp : q.2 ≠ p.2 := Ne.symm hp
    have hsnd := congrArg (fun c : BinaryDiagonal => (c p.2).2) h
    simp [mixedVector_snd, hqp] at hsnd

private lemma mixedGroupLike_injective : Function.Injective mixedGroupLike := by
  intro p q h
  apply mixedVector_injective
  exact congrArg (fun g : GroupLike ProductRing BinaryDiagonal => g.val) h

private lemma groupLike_cardinal_lower_bound :
    (4 : Cardinal) ≤ Cardinal.mk (GroupLike ProductRing BinaryDiagonal) := by
  simpa [Cardinal.mk_fintype] using
    Cardinal.mk_le_of_injective mixedGroupLike_injective

private lemma binaryDiagonal_rank : Module.rank ProductRing BinaryDiagonal = 2 := by
  simp

private lemma groupLike_cardinal_not_le_rank :
    ¬ Cardinal.mk (GroupLike ProductRing BinaryDiagonal) ≤
      Module.rank ProductRing BinaryDiagonal := by
  intro h
  rw [binaryDiagonal_rank] at h
  have hfour : (4 : Cardinal) ≤ 2 := groupLike_cardinal_lower_bound.trans h
  exact (by decide : ¬ (4 : ℕ) ≤ 2) (Nat.cast_le.mp hfour)

/-- Over the non-domain `ℤ × ℤ`, the finite free diagonal coalgebra is torsion-free
for regular scalars and has rank two, but admits four injectively indexed group-like elements.
Thus the domain hypothesis in the group-like cardinal bound cannot be dropped. -/
theorem diagonal_productRing_groupLike_rank_boundary :
    ¬ IsDomain (ℤ × ℤ) ∧
      Module.Free (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)) ∧
      Module.Finite (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)) ∧
      Module.IsTorsionFree (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)) ∧
      Module.rank (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)) = 2 ∧
      (∃ f : Fin 2 × Fin 2 → GroupLike (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)),
        Function.Injective f) ∧
      (4 : Cardinal) ≤ Cardinal.mk (GroupLike (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ))) ∧
      ¬ Cardinal.mk (GroupLike (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ))) ≤
        Module.rank (ℤ × ℤ) (Fin 2 →₀ (ℤ × ℤ)) :=
  ⟨productRing_not_isDomain, inferInstance, inferInstance, inferInstance,
    binaryDiagonal_rank, ⟨mixedGroupLike, mixedGroupLike_injective⟩,
    groupLike_cardinal_lower_bound, groupLike_cardinal_not_le_rank⟩

end

end Coalgebra
