/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension.Polynomial.GroupLike
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Boundary rings for the polynomial primitive extension

Over `ZMod 4`, the constant class of `2` gives a group-like point outside the
family parametrized by linear terms. The zero ring and the reduced ring
`ℤ × ℤ` illustrate the broader scope of the construction and classification.
The polynomial ring `ℤ[X]` is not a principal ideal ring.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace TrivSqZeroExt

/-- The constant square-zero class of `2` gives a group-like point over `ZMod 4`. -/
def polynomialConstantTwoGroupLike :
    GroupLike (Polynomial (ZMod 4))
      (TrivSqZeroExt (Polynomial (ZMod 4))
        (Polynomial (ZMod 4) ⧸ Ideal.span {(X : Polynomial (ZMod 4)) ^ 2})) where
  val := 1 + inr (Ideal.Quotient.mk
    (Ideal.span {(X : Polynomial (ZMod 4)) ^ 2}) (C (2 : ZMod 4)))
  isGroupLikeElem_val := by
    have hsq : (C (2 : ZMod 4)) ^ 2 = (0 : Polynomial (ZMod 4)) := by
      have h : (2 : ZMod 4) ^ 2 = 0 := by decide
      rw [← map_pow, h, map_zero]
    have hmem : (C (2 : ZMod 4)) ^ 2 ∈
        (Ideal.span {(X : Polynomial (ZMod 4)) ^ 2} : Ideal (Polynomial (ZMod 4))) := by
      rw [hsq]
      exact Ideal.zero_mem _
    simpa only [inl_one] using
      (isGroupLikeElem_quotient_mk_iff
        (Ideal.span {(X : Polynomial (ZMod 4)) ^ 2}) (C (2 : ZMod 4))).mpr hmem

/-- The underlying element of the constant group-like point. -/
@[simp] theorem polynomialConstantTwoGroupLike_val :
    polynomialConstantTwoGroupLike.val =
      1 + inr (Ideal.Quotient.mk
        (Ideal.span {(X : Polynomial (ZMod 4)) ^ 2}) (C (2 : ZMod 4))) := rfl

/-- The constant coordinate of the extra point is `2`. -/
@[simp] theorem polynomialConstantTwoGroupLike_coeffZero :
    quotientXsqCoeffZero (ZMod 4) polynomialConstantTwoGroupLike.val.snd = 2 := by
  simp [polynomialConstantTwoGroupLike_val]

/-- The constant square-zero point is not in the family of linear points. -/
theorem polynomialConstantTwoGroupLike_not_mem_range :
    polynomialConstantTwoGroupLike ∉ Set.range (polynomialGroupLike (ZMod 4)) := by
  rintro ⟨k, hk⟩
  have hcoord := congrArg
    (fun x : GroupLike (Polynomial (ZMod 4))
      (TrivSqZeroExt (Polynomial (ZMod 4))
        (Polynomial (ZMod 4) ⧸ Ideal.span {(X : Polynomial (ZMod 4)) ^ 2})) =>
          quotientXsqCoeffZero (ZMod 4) x.val.snd) hk
  have h : (2 : ZMod 4) = 0 := by
    simpa only [polynomialConstantTwoGroupLike_coeffZero,
      polynomialGroupLike_coeffZero] using hcoord.symm
  exact (by decide : (2 : ZMod 4) ≠ 0) h

example : polynomialGroupLike (ZMod 1) 0 = ⟨1, isGroupLikeElem_inl_one⟩ :=
  polynomialGroupLike_zero (ZMod 1)

example (x : GroupLike (Polynomial (ZMod 1))
    (TrivSqZeroExt (Polynomial (ZMod 1))
      (Polynomial (ZMod 1) ⧸ Ideal.span {(X : Polynomial (ZMod 1)) ^ 2}))) :
    (polynomialGroupLikeEquiv (ZMod 1)).symm 0 = x := by
  have h : polynomialGroupLikeEquiv (ZMod 1) x = 0 := Subsingleton.elim _ _
  rw [← h]
  exact (polynomialGroupLikeEquiv (ZMod 1)).symm_apply_apply x

example :
    ((1, 0) : ℤ × ℤ) ≠ 0 ∧ ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      ((1, 0) : ℤ × ℤ) * ((0, 1) : ℤ × ℤ) = 0 := by
  decide

example (x : GroupLike (Polynomial (ℤ × ℤ))
    (TrivSqZeroExt (Polynomial (ℤ × ℤ))
      (Polynomial (ℤ × ℤ) ⧸ Ideal.span {(X : Polynomial (ℤ × ℤ)) ^ 2}))) :
    (polynomialGroupLikeEquiv (ℤ × ℤ)).symm
      (polynomialGroupLikeEquiv (ℤ × ℤ) x) = x :=
  (polynomialGroupLikeEquiv (ℤ × ℤ)).symm_apply_apply x

example : ¬ IsPrincipalIdealRing (Polynomial ℤ) := by
  intro h
  let := h
  exact Int.not_isField (Ideal.IsField.of_isPrincipalIdealRing_polynomial (R := ℤ))

end TrivSqZeroExt
