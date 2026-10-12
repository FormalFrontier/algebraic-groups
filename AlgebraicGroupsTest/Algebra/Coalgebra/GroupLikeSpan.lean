/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite group-like spans in an integer-indexed monoid algebra

These examples use Mathlib's coalgebra and group-like basis elements of
`AddMonoidAlgebra R ℤ`. The specified span of the basis elements at 3 and 7 contains
both elements, is finitely generated as a module, and is closed under comultiplication
into the image of its tensor square. Singleton and empty spans cover the boundaries.
The natural-number scalar example also applies where additive inverses are unavailable.
-/

open Coalgebra

universe u

section CommSemiring

variable {R : Type u} [CommSemiring R]

-- The specified two-generator span, rather than an unspecified larger submodule.
/-- The span of the basis elements at `3` and `7` contains both generators, is finitely
generated, and is closed under comultiplication into the image of its tensor square. -/
public theorem span_pair_single_one_fg_comul_mem_range_mapIncl :
    let D := Submodule.span R
      ({AddMonoidAlgebra.single (3 : ℤ) (1 : R), AddMonoidAlgebra.single (7 : ℤ) (1 : R)} :
        Set (AddMonoidAlgebra R ℤ))
    AddMonoidAlgebra.single (3 : ℤ) (1 : R) ∈ D ∧
      AddMonoidAlgebra.single (7 : ℤ) (1 : R) ∈ D ∧ D.FG ∧
      ∀ x ∈ D, comul (R := R) x ∈ LinearMap.range (TensorProduct.mapIncl D D) := by
  dsimp only
  refine ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
    Submodule.fg_span ((Set.finite_singleton _).insert _), ?_⟩
  intro x hx
  apply comul_mem_range_mapIncl_span_of_isGroupLikeElem ?_ hx
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl <;> exact AddMonoidAlgebra.isGroupLikeElem_single_one _

-- Singleton spans use the same closure lemma and the existing finite-generation API.
private theorem span_singleton_single_one_fg_comul_mem_range_mapIncl (g : ℤ) :
    let D := Submodule.span R ({AddMonoidAlgebra.single g (1 : R)} : Set (AddMonoidAlgebra R ℤ))
    D.FG ∧ ∀ x ∈ D, comul (R := R) x ∈ LinearMap.range (TensorProduct.mapIncl D D) := by
  dsimp only
  refine ⟨Submodule.fg_span_singleton _, ?_⟩
  intro x hx
  apply comul_mem_range_mapIncl_span_of_isGroupLikeElem ?_ hx
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact AddMonoidAlgebra.isGroupLikeElem_single_one _

-- The empty span is covered without assuming a nonempty generator set.
private theorem span_empty_fg_comul_mem_range_mapIncl :
    let D := Submodule.span R (∅ : Set (AddMonoidAlgebra R ℤ))
    D.FG ∧ ∀ x ∈ D, comul (R := R) x ∈ LinearMap.range (TensorProduct.mapIncl D D) := by
  dsimp only
  refine ⟨Submodule.fg_span Set.finite_empty, ?_⟩
  intro x hx
  exact comul_mem_range_mapIncl_span_of_isGroupLikeElem (by simp) hx

end CommSemiring

-- A concrete non-generator element over a semiring with no additive inverses.
private theorem comul_nat_linear_combination_mem_range_mapIncl_span_pair_single_one :
    let D := Submodule.span ℕ
      ({AddMonoidAlgebra.single (3 : ℤ) (1 : ℕ), AddMonoidAlgebra.single (7 : ℤ) (1 : ℕ)} :
        Set (AddMonoidAlgebra ℕ ℤ))
    comul (R := ℕ)
        (2 • AddMonoidAlgebra.single (3 : ℤ) (1 : ℕ) +
          5 • AddMonoidAlgebra.single (7 : ℤ) (1 : ℕ)) ∈
      LinearMap.range (TensorProduct.mapIncl D D) := by
  dsimp only
  apply comul_mem_range_mapIncl_span_of_isGroupLikeElem
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> exact AddMonoidAlgebra.isGroupLikeElem_single_one _
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ 2 (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ 5 (Submodule.subset_span (by simp)))
