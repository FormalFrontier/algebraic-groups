/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero

set_option warningAsError true

namespace MvPolynomial

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem checks_unique_common_zero {σ : Type v} [Fintype σ]
    {ι : Type w} [Fintype ι]
    (f : ι → MvPolynomial σ K) (a : σ → K)
    (h : ∀ x : σ → K, (∀ i, eval x (f i) = 0) ↔ x = a) :
    Fintype.card σ ≤ Fintype.card ι :=
  card_le_card_of_unique_common_zero f a h

private theorem checks_empty_variables (a : Empty → K) :
    Fintype.card Empty ≤ Fintype.card Empty := by
  apply card_le_card_of_unique_common_zero
    (fun i : Empty => (isEmptyElim i : MvPolynomial Empty K)) a
  intro x
  constructor
  · intro _
    funext i
    exact isEmptyElim i
  · intro _ i
    exact isEmptyElim i

private theorem checks_sharp_coordinate_family (K : Type u) [Field K] [IsAlgClosed K] :
    Fintype.card (Fin 2) ≤ Fintype.card (Fin 2) := by
  apply card_le_card_of_unique_common_zero
    (fun i : Fin 2 => (X i : MvPolynomial (Fin 2) K)) (0 : Fin 2 → K)
  intro x
  constructor
  · intro hx
    funext i
    simpa using hx i
  · rintro rfl i
    simp

private theorem checks_second_common_zero {σ : Type v} [Fintype σ]
    {ι : Type w} [Fintype ι]
    (f : ι → MvPolynomial σ K) (a : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ)
    (ha : ∀ i, eval a (f i) = 0) :
    ∃ x : σ → K, x ≠ a ∧ ∀ i, eval x (f i) = 0 :=
  exists_common_zero_ne f a hcard ha

private theorem checks_no_equations_second_zero (f : Empty → MvPolynomial (Fin 1) K) :
    ∃ x : Fin 1 → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  apply exists_common_zero_ne f (0 : Fin 1 → K)
  · decide
  · intro i
    exact isEmptyElim i

private theorem checks_duplicate_equations (p : MvPolynomial (Fin 3) K)
    (a : Fin 3 → K) (ha : eval a p = 0) :
    ∃ x : Fin 3 → K, x ≠ a ∧
      ∀ i : Fin 2, eval x ((fun _ : Fin 2 => p) i) = 0 := by
  apply exists_common_zero_ne (fun _ : Fin 2 => p) a
  · decide
  · intro _
    exact ha

private theorem checks_no_equations_homogeneous (f : Empty → MvPolynomial (Fin 1) K) :
    ∃ x : Fin 1 → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  apply exists_nonzero_common_zero_of_isHomogeneous f (fun i : Empty => isEmptyElim i)
  · decide
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

private theorem checks_mixed_degrees (f : Bool → MvPolynomial (Fin 3) K)
    (hfalse : (f false).IsHomogeneous 1) (htrue : (f true).IsHomogeneous 2) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  apply exists_nonzero_common_zero_of_isHomogeneous f
    (fun i : Bool => if i then 2 else 1)
  · decide
  · intro i
    cases i <;> decide
  · intro i
    cases i with
    | false => simpa using hfalse
    | true => simpa using htrue

private theorem checks_zero_equation (p : MvPolynomial (Fin 3) K)
    (hp : p.IsHomogeneous 1) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧
      ∀ i : Fin 2, eval x (if i = 0 then p else 0) = 0 := by
  apply exists_nonzero_common_zero_of_isHomogeneous
    (fun i : Fin 2 => if i = 0 then p else 0) (fun _ => 1)
  · decide
  · intro _
    decide
  · intro i
    split_ifs with h
    · exact hp
    · exact isHomogeneous_zero (σ := Fin 3) (R := K) 1

end MvPolynomial
