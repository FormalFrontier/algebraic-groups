/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoefficients
import AlgebraicGroups.LinearAlgebra.Coalgebra.GroupLikeCoordinates
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Prod

/-!
# Group-like coordinates over semirings

The diagonal coalgebra on `MonoidAlgebra (ℕ × ℕ) ℕ` has a group-like element
with two nonzero coefficients, so it is not a scaled basis vector. This uses a
commutative semiring rather than a ring and an infinite ambient index type.

The vector `3δ₀` over `ZMod 6` satisfies the comultiplication equation but not
counit normalization. Over `ZMod 2`, the vector `δ₀ + δ₁ + δ₂` has normalized,
idempotent coefficients but fails off-diagonal orthogonality. Its comultiplication
has three diagonal ones, whereas its self-tensor has nine ones on the support
square. Only outside that square do both tensors vanish.
The zero ring and the empty index over `ℕ` give the two degenerate boundaries.

## References

These examples use Mathlib's `MonoidAlgebra` coefficient and basis APIs, its
transported coalgebra, its stock group-like basis vectors, and the tensor-product
basis representation. The coordinate criteria are those of
`AlgebraicGroups.LinearAlgebra.Coalgebra.GroupLikeCoordinates` and
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoefficients`.
-/

open scoped TensorProduct

noncomputable section

private def splitVector : MonoidAlgebra (ℕ × ℕ) ℕ :=
  MonoidAlgebra.single 1 (1, 0) + MonoidAlgebra.single 0 (0, 1)

private theorem splitVector_coeff (i : ℕ) :
    splitVector.coeff i =
      if i = 1 then (1, 0) else if i = 0 then (0, 1) else 0 := by
  by_cases h₁ : i = 1 <;> by_cases h₀ : i = 0 <;>
    simp_all [splitVector, eq_comm]

private theorem splitVector_support : splitVector.coeff.support = {1, 0} := by
  ext i
  by_cases h₁ : i = 1 <;> by_cases h₀ : i = 0 <;>
    simp_all [Finsupp.mem_support_iff, splitVector_coeff, Prod.ext_iff]

private theorem splitVector_nonzero_and_ne_single : splitVector ≠ 0 ∧
    ∀ (i : ℕ) (r : ℕ × ℕ), splitVector ≠ MonoidAlgebra.single i r := by
  constructor
  · intro h
    have hc := congrArg (fun z : MonoidAlgebra (ℕ × ℕ) ℕ ↦ z.coeff 1) h
    simp [splitVector_coeff, Prod.ext_iff] at hc
  · intro i r h
    have hi : i = 1 := by
      by_contra hi
      have hc := congrArg (fun z : MonoidAlgebra (ℕ × ℕ) ℕ ↦ z.coeff 1) h
      simp [splitVector_coeff, hi, Prod.ext_iff] at hc
    subst i
    have hc := congrArg (fun z : MonoidAlgebra (ℕ × ℕ) ℕ ↦ z.coeff 0) h
    simp [splitVector_coeff, Prod.ext_iff] at hc

private theorem splitVector_conditions :
    Pairwise (fun i j ↦ splitVector.coeff i * splitVector.coeff j = 0) ∧
      splitVector.coeff.sum (fun _ r ↦ r) = 1 := by
  constructor
  · intro i j hij
    by_cases hi₁ : i = 1 <;> by_cases hi₀ : i = 0 <;>
      by_cases hj₁ : j = 1 <;> by_cases hj₀ : j = 0 <;>
      simp_all [splitVector_coeff, Prod.ext_iff]
  · simp only [splitVector, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single]
    rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    simp [Prod.ext_iff]

private theorem splitBasis_groupLike (i : ℕ) :
    IsGroupLikeElem (ℕ × ℕ) ((MonoidAlgebra.basis ℕ (ℕ × ℕ)) i) := by
  simpa only [MonoidAlgebra.basis_apply] using
    (MonoidAlgebra.isGroupLikeElem_single_one (R := ℕ × ℕ) (A := ℕ × ℕ) i)

-- The counit is computed from the coefficients, without assuming the vector is group-like.
private theorem splitVector_counit_eq_one : Coalgebra.counit (R := ℕ × ℕ) splitVector = 1 := by
  rw [(MonoidAlgebra.basis ℕ (ℕ × ℕ)).counit_eq_sum_repr
    (fun i ↦ (splitBasis_groupLike i).counit_eq_one), MonoidAlgebra.basis_repr]
  exact splitVector_conditions.2

-- These are all coordinates of the two tensors, including outside the support square.
private theorem splitVector_tensor_coordinates (i j : ℕ) :
    let b := MonoidAlgebra.basis ℕ (ℕ × ℕ)
    (b.tensorProduct b).repr (Coalgebra.comul (R := ℕ × ℕ) splitVector) (i, j) =
        (if i = 1 ∧ j = 1 then (1, 0) else if i = 0 ∧ j = 0 then (0, 1) else 0) ∧
      (b.tensorProduct b).repr (splitVector ⊗ₜ[ℕ × ℕ] splitVector) (i, j) =
        (if i = 1 ∧ j = 1 then (1, 0) else if i = 0 ∧ j = 0 then (0, 1) else 0) := by
  dsimp only
  rw [(MonoidAlgebra.basis ℕ (ℕ × ℕ)).tensorProduct_repr_comul_apply
    (fun k ↦ (splitBasis_groupLike k).comul_eq_tmul_self),
    Module.Basis.tensorProduct_repr_tmul_apply]
  by_cases hi₁ : i = 1 <;> by_cases hi₀ : i = 0 <;>
    by_cases hj₁ : j = 1 <;> by_cases hj₀ : j = 0 <;>
    simp_all [MonoidAlgebra.basis_repr, MonoidAlgebra.basis_apply,
      splitVector_coeff, Finsupp.single_apply, smul_eq_mul, Prod.ext_iff, eq_comm]

private theorem splitVector_groupLike : IsGroupLikeElem (ℕ × ℕ) splitVector :=
  (MonoidAlgebra.isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one splitVector).2
    splitVector_conditions

-- The abstract basis criterion has the same nonmonomial semiring example.
private theorem splitVector_isGroupLikeElem_of_basis : IsGroupLikeElem (ℕ × ℕ) splitVector := by
  apply (Module.Basis.isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one
    (MonoidAlgebra.basis ℕ (ℕ × ℕ)) splitBasis_groupLike splitVector).2
  simpa only [MonoidAlgebra.basis_repr] using splitVector_conditions

private theorem splitVector_coeff_isIdempotentElem
    (i : ℕ) : IsIdempotentElem (splitVector.coeff i) := by
  simpa only [MonoidAlgebra.basis_repr] using
    (IsGroupLikeElem.isIdempotentElem_repr (MonoidAlgebra.basis ℕ (ℕ × ℕ))
      splitBasis_groupLike splitVector_groupLike i)

private def unnormalizedVector : MonoidAlgebra (ZMod 6) ℕ :=
  MonoidAlgebra.single 0 3

private theorem unnormalizedVector_coeff (i : ℕ) :
    unnormalizedVector.coeff i = if i = 0 then 3 else 0 := by
  simp [unnormalizedVector, Finsupp.single_apply, eq_comm]

private theorem unnormalizedVector_support : unnormalizedVector.coeff.support = {0} := by
  simpa only [unnormalizedVector, MonoidAlgebra.coeff_single] using
    (Finsupp.support_single (0 : ℕ) (by decide : (3 : ZMod 6) ≠ 0))

private theorem unnormalizedVector_orthogonal :
    OrthogonalIdempotents
      (fun i ↦ (MonoidAlgebra.basis ℕ (ZMod 6)).repr unnormalizedVector i) := by
  constructor
  · intro i
    simp only [MonoidAlgebra.basis_repr, unnormalizedVector_coeff]
    by_cases hi : i = 0
    · simpa only [ite_eq_left hi, IsIdempotentElem] using
        (show (3 : ZMod 6) * 3 = 3 by decide)
    · simpa only [ite_eq_right hi] using (IsIdempotentElem.zero : IsIdempotentElem (0 : ZMod 6))
  · intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp_all [MonoidAlgebra.basis_repr, unnormalizedVector_coeff]

private theorem unnormalizedVector_comul :
    Coalgebra.comul (R := ZMod 6) unnormalizedVector =
      unnormalizedVector ⊗ₜ[ZMod 6] unnormalizedVector := by
  apply (Module.Basis.comul_eq_tmul_self_iff_orthogonalIdempotents_repr
    (MonoidAlgebra.basis ℕ (ZMod 6))
    (fun i ↦ by
      simpa only [MonoidAlgebra.basis_apply] using
        (MonoidAlgebra.isGroupLikeElem_single_one
          (R := ZMod 6) (A := ZMod 6) i).comul_eq_tmul_self)
    unnormalizedVector).2
  exact unnormalizedVector_orthogonal

private theorem unnormalizedVector_tensor_coordinates (i j : ℕ) :
    let b := MonoidAlgebra.basis ℕ (ZMod 6)
    (b.tensorProduct b).repr (Coalgebra.comul (R := ZMod 6) unnormalizedVector) (i, j) =
        (if i = 0 ∧ j = 0 then 3 else 0) ∧
      (b.tensorProduct b).repr (unnormalizedVector ⊗ₜ[ZMod 6] unnormalizedVector) (i, j) =
        (if i = 0 ∧ j = 0 then 3 else 0) := by
  dsimp only
  rw [unnormalizedVector_comul, Module.Basis.tensorProduct_repr_tmul_apply]
  have h₃ : (3 : ZMod 6) * 3 = 3 := by decide
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp_all [MonoidAlgebra.basis_repr, unnormalizedVector_coeff, smul_eq_mul]

private theorem unnormalizedVector_counit_and_not_groupLike
    : Coalgebra.counit (R := ZMod 6) unnormalizedVector = 3 ∧
    Coalgebra.counit (R := ZMod 6) unnormalizedVector ≠ 1 ∧
      ¬ IsGroupLikeElem (ZMod 6) unnormalizedVector := by
  have hc : Coalgebra.counit (R := ZMod 6) unnormalizedVector = 3 := by
    simp [unnormalizedVector]
  have hn : Coalgebra.counit (R := ZMod 6) unnormalizedVector ≠ 1 := by
    rw [hc]
    decide
  exact ⟨hc, hn, fun h ↦ hn h.counit_eq_one⟩

private def oddVector : MonoidAlgebra (ZMod 2) ℕ :=
  MonoidAlgebra.single 0 1 + MonoidAlgebra.single 1 1 + MonoidAlgebra.single 2 1

private theorem oddVector_coeff (i : ℕ) :
    oddVector.coeff i = if i ∈ ({0, 1, 2} : Finset ℕ) then 1 else 0 := by
  by_cases h₀ : i = 0 <;> by_cases h₁ : i = 1 <;> by_cases h₂ : i = 2 <;>
    simp_all [oddVector, eq_comm]

private theorem oddVector_support : oddVector.coeff.support = {0, 1, 2} := by
  ext i
  by_cases hi : i ∈ ({0, 1, 2} : Finset ℕ) <;>
    simp [Finsupp.mem_support_iff, oddVector_coeff, hi]

private theorem oddVector_counit_and_coeff_isIdempotentElem
    : Coalgebra.counit (R := ZMod 2) oddVector = 3 ∧ (3 : ZMod 2) = 1 ∧
    ∀ i, IsIdempotentElem (oddVector.coeff i) := by
  refine ⟨?_, by decide, ?_⟩
  · simp only [oddVector, map_add, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
    decide
  · intro i
    by_cases hi : i ∈ ({0, 1, 2} : Finset ℕ) <;>
      simp [oddVector_coeff, hi]

-- All three diagonals are (1,1); all six ordered off-diagonals are (0,1).
-- Outside the support square both entries are zero.
private theorem oddVector_tensor_coordinates (i j : ℕ) :
    let b := MonoidAlgebra.basis ℕ (ZMod 2)
    (b.tensorProduct b).repr (Coalgebra.comul (R := ZMod 2) oddVector) (i, j) =
        (if i = j ∧ i ∈ ({0, 1, 2} : Finset ℕ) then 1 else 0) ∧
      (b.tensorProduct b).repr (oddVector ⊗ₜ[ZMod 2] oddVector) (i, j) =
        (if i ∈ ({0, 1, 2} : Finset ℕ) ∧ j ∈ ({0, 1, 2} : Finset ℕ) then 1 else 0) := by
  dsimp only
  rw [(MonoidAlgebra.basis ℕ (ZMod 2)).tensorProduct_repr_comul_apply
    (fun k ↦ by
      simpa only [MonoidAlgebra.basis_apply] using
        (MonoidAlgebra.isGroupLikeElem_single_one
          (R := ZMod 2) (A := ZMod 2) k).comul_eq_tmul_self),
    Module.Basis.tensorProduct_repr_tmul_apply]
  by_cases hij : i = j <;>
    by_cases hi : i ∈ ({0, 1, 2} : Finset ℕ) <;>
    by_cases hj : j ∈ ({0, 1, 2} : Finset ℕ) <;>
    simp_all [MonoidAlgebra.basis_repr, MonoidAlgebra.basis_apply, oddVector_coeff,
      smul_eq_mul]

private theorem oddVector_not_comul :
    Coalgebra.comul (R := ZMod 2) oddVector ≠ oddVector ⊗ₜ[ZMod 2] oddVector := by
  intro h
  have hc := congrArg (fun z ↦
    ((MonoidAlgebra.basis ℕ (ZMod 2)).tensorProduct
      (MonoidAlgebra.basis ℕ (ZMod 2))).repr z (0, 1)) h
  have hd := oddVector_tensor_coordinates 0 1
  have h₀ : ((MonoidAlgebra.basis ℕ (ZMod 2)).tensorProduct
      (MonoidAlgebra.basis ℕ (ZMod 2))).repr
      (Coalgebra.comul (R := ZMod 2) oddVector) (0, 1) = 0 := by simpa using hd.1
  have h₁ : ((MonoidAlgebra.basis ℕ (ZMod 2)).tensorProduct
      (MonoidAlgebra.basis ℕ (ZMod 2))).repr
      (oddVector ⊗ₜ[ZMod 2] oddVector) (0, 1) = 1 := by simpa using hd.2
  exact zero_ne_one (h₀.symm.trans (hc.trans h₁))

private theorem oddVector_not_groupLike : ¬ IsGroupLikeElem (ZMod 2) oddVector :=
  fun h ↦ oddVector_not_comul h.comul_eq_tmul_self

-- The domain bridge excludes the same three-point vector; no extra field model is needed.
private theorem oddVector_not_mem_range_single_one
    : oddVector ∉ Set.range (MonoidAlgebra.single · (1 : ZMod 2)) := by
  apply (MonoidAlgebra.pairwise_mul_eq_zero_sum_eq_one_iff_mem_range_single_one oddVector).not.mp
  rintro ⟨hp, _⟩
  have h : oddVector.coeff 0 * oddVector.coeff 1 = 0 := hp (by decide : (0 : ℕ) ≠ 1)
  simp [oddVector_coeff] at h

private theorem zmodOne_zero_groupLike :
    (0 : MonoidAlgebra (ZMod 1) ℕ).coeff.support = ∅ ∧
      (0 : MonoidAlgebra (ZMod 1) ℕ).coeff.sum (fun _ r ↦ r) = 1 ∧
      Coalgebra.counit (R := ZMod 1) (0 : MonoidAlgebra (ZMod 1) ℕ) = 1 ∧
      Coalgebra.comul (R := ZMod 1) (0 : MonoidAlgebra (ZMod 1) ℕ) =
        (0 : MonoidAlgebra (ZMod 1) ℕ) ⊗ₜ[ZMod 1] 0 ∧
      IsGroupLikeElem (ZMod 1) (0 : MonoidAlgebra (ZMod 1) ℕ) := by
  have h₀₁ : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
  have hc : Coalgebra.counit (R := ZMod 1) (0 : MonoidAlgebra (ZMod 1) ℕ) = 1 := by
    simpa only [map_zero] using h₀₁
  have hd : Coalgebra.comul (R := ZMod 1) (0 : MonoidAlgebra (ZMod 1) ℕ) =
      (0 : MonoidAlgebra (ZMod 1) ℕ) ⊗ₜ[ZMod 1] 0 := by simp
  exact ⟨by simp, by simpa using h₀₁, hc, hd, ⟨hc, hd⟩⟩

private theorem emptyIndex_zero_and_not_groupLike (x : MonoidAlgebra ℕ Empty) :
    x = 0 ∧ x.coeff.support = ∅ ∧ x.coeff.sum (fun _ r ↦ r) = 0 ∧
      (∀ i : Empty, IsGroupLikeElem ℕ ((MonoidAlgebra.basis Empty ℕ) i)) ∧
      Coalgebra.counit (R := ℕ) x ≠ 1 ∧ ¬ IsGroupLikeElem ℕ x := by
  have hx : x = 0 := by
    apply MonoidAlgebra.coeff_injective
    ext i
    exact Empty.elim i
  subst x
  have hc : Coalgebra.counit (R := ℕ) (0 : MonoidAlgebra ℕ Empty) ≠ 1 := by simp
  exact ⟨rfl, by simp, by simp, (fun i ↦ Empty.elim i), hc,
    fun h ↦ hc h.counit_eq_one⟩
