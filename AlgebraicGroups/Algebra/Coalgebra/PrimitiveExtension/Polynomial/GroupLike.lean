/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension
public import AlgebraicGroups.Algebra.Polynomial.QuotientXsq
import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Group-like elements of the polynomial primitive extension

For a commutative ring `K`, put `R = K[X]`, `T = R/(X²)` and let
`C = TrivSqZeroExt R T` carry the primitive coalgebra structure. For each
`k : K`, the point `1 + inr([Polynomial.C k * X])` is `R`-group-like.
Reading its linear coefficient recovers `k`, giving an injective family.
This yields infinitely many points under `Infinite K`.

Under `IsReduced K`, every point belongs to this family, so the parameter
map is an equivalence `GroupLike R C ≃ K`. No infinitude assumption is
needed for classification; in particular, finite fields are included.

## References

*Finite generation and group-like elements*, §3, constructs the rational
primitive coalgebra `ℚ[X] ⊕ ℚ[X]/(X²)` and parametrizes all its group-like
elements by `ℚ`. The commutative-ring family and reduced-ring classification
in this module extend the coordinate argument of that rational case.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u

namespace TrivSqZeroExt

variable (K : Type u) [CommRing K]

/-- The group-like point with linear coefficient `k`. -/
def polynomialGroupLike (k : K) :
    GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])})) where
  val := 1 + inr (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C k * X))
  isGroupLikeElem_val := by
    have hmem : (C k * X) ^ 2 ∈ (Ideal.span {(X ^ 2 : K[X])} : Ideal K[X]) := by
      apply Ideal.mem_span_singleton.mpr
      exact ⟨(C k) ^ 2, by simp only [mul_pow, mul_comm]⟩
    simpa only [inl_one] using
      (isGroupLikeElem_quotient_mk_iff (Ideal.span {(X ^ 2 : K[X])}) (C k * X)).mpr hmem

/-- The linear coefficient of a group-like element. -/
def polynomialGroupLikeParameter
    (x : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) : K :=
  Polynomial.quotientXsqCoeffOne K x.val.snd

/-- The parameter is the linear coefficient of the quotient coordinate. -/
theorem polynomialGroupLikeParameter_eq_coeffOne
    (x : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) :
    polynomialGroupLikeParameter K x = Polynomial.quotientXsqCoeffOne K x.val.snd := rfl

/-- The underlying element of the point with parameter `k`. -/
theorem polynomialGroupLike_val (k : K) :
    (polynomialGroupLike K k).val =
      1 + inr (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C k * X)) := rfl

/-- The scalar coordinate of a constructed group-like point is one. -/
@[simp] theorem polynomialGroupLike_val_fst (k : K) :
    (polynomialGroupLike K k).val.fst = 1 := by
  simp only [polynomialGroupLike_val, fst_add, fst_one, fst_inr, add_zero]

/-- The quotient coordinate of a constructed group-like point is `kX`. -/
theorem polynomialGroupLike_val_snd (k : K) :
    (polynomialGroupLike K k).val.snd =
      Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C k * X) := by
  simp only [polynomialGroupLike_val, snd_add, snd_one, snd_inr, zero_add]

/-- The quotient coordinate of a constructed point has zero constant coefficient. -/
@[simp] theorem polynomialGroupLike_coeffZero (k : K) :
    Polynomial.quotientXsqCoeffZero K (polynomialGroupLike K k).val.snd = 0 := by
  rw [polynomialGroupLike_val_snd, Polynomial.quotientXsqCoeffZero_mk]
  simp

/-- The quotient coordinate of a constructed point has linear coefficient `k`. -/
@[simp] theorem polynomialGroupLike_coeffOne (k : K) :
    Polynomial.quotientXsqCoeffOne K (polynomialGroupLike K k).val.snd = k := by
  rw [polynomialGroupLike_val_snd, Polynomial.quotientXsqCoeffOne_mk]
  simp

/-- Taking the parameter is a left inverse to the construction. -/
@[simp] theorem polynomialGroupLikeParameter_apply (k : K) :
    polynomialGroupLikeParameter K (polynomialGroupLike K k) = k := by
  exact polynomialGroupLike_coeffOne K k

/-- Different parameters give different group-like elements over any commutative ring. -/
theorem polynomialGroupLike_injective : Function.Injective (polynomialGroupLike K) :=
  Function.LeftInverse.injective (polynomialGroupLikeParameter_apply K)

/-- Parameter zero gives the distinguished group-like point. -/
@[simp] theorem polynomialGroupLike_zero :
    polynomialGroupLike K 0 = ⟨1, isGroupLikeElem_inl_one⟩ := by
  apply GroupLike.val_injective
  simp [polynomialGroupLike_val]

/-- An infinite coefficient ring gives infinitely many group-like elements. -/
theorem polynomialGroupLike_infinite [Infinite K] :
    Infinite (GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) :=
  Infinite.of_injective (polynomialGroupLike K) (polynomialGroupLike_injective K)

section Reduced

variable [IsReduced K]

/-- Over a reduced ring, the quotient coordinate of any group-like point has
zero constant coefficient. -/
@[simp] theorem polynomialGroupLike_coeffZero_eq_zero
    (x : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) :
    Polynomial.quotientXsqCoeffZero K x.val.snd = 0 := by
  have hf : x.val.fst = 1 := ((isGroupLikeElem_iff x.val).mp x.isGroupLikeElem_val).1
  let p : K[X] := C (Polynomial.quotientXsqCoeffZero K x.val.snd) +
    C (Polynomial.quotientXsqCoeffOne K x.val.snd) * X
  have hp : (inl 1 + inr (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p) :
      TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])})) = x.val := by
    apply TrivSqZeroExt.ext
    · simpa only [fst_add, fst_inl, fst_inr, add_zero] using hf.symm
    · simpa only [p, snd_add, snd_inl, snd_inr, zero_add] using
        Polynomial.quotientXsq_mk_coeffs K x.val.snd
  have hg : IsGroupLikeElem K[X]
      (inl 1 + inr (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p) :
        TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])})) := by
    rw [hp]
    exact x.isGroupLikeElem_val
  have hm := (isGroupLikeElem_quotient_mk_iff (Ideal.span {(X ^ 2 : K[X])}) p).mp hg
  have hq : Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])} : Ideal K[X]) (p ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hc := congrArg (Polynomial.quotientXsqCoeffZero K) hq
  rw [Polynomial.quotientXsqCoeffZero_mk, map_zero (Polynomial.quotientXsqCoeffZero K)] at hc
  have ha : (Polynomial.quotientXsqCoeffZero K x.val.snd) ^ 2 = 0 := by
    simpa [p, pow_two, Polynomial.mul_coeff_zero] using hc
  exact (show IsNilpotent (Polynomial.quotientXsqCoeffZero K x.val.snd) from ⟨2, ha⟩).eq_zero

/-- Over a reduced ring, construction from the linear coefficient is a right inverse. -/
@[simp] theorem polynomialGroupLike_parameter
    (x : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) :
    polynomialGroupLike K (polynomialGroupLikeParameter K x) = x := by
  apply GroupLike.val_injective
  apply TrivSqZeroExt.ext
  · rw [polynomialGroupLike_val_fst]
    exact ((isGroupLikeElem_iff x.val).mp x.isGroupLikeElem_val).1.symm
  · rw [polynomialGroupLike_val_snd]
    simpa [polynomialGroupLikeParameter] using
      Polynomial.quotientXsq_mk_coeffs K x.val.snd

/-- Over a reduced ring, every group-like point is obtained from a parameter. -/
theorem polynomialGroupLike_surjective : Function.Surjective (polynomialGroupLike K) :=
  fun x => ⟨polynomialGroupLikeParameter K x, polynomialGroupLike_parameter K x⟩

/-- Group-like points of the polynomial primitive extension over a reduced ring
are parametrized by the coefficient ring. -/
def polynomialGroupLikeEquiv :
    GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])})) ≃ K where
  toFun := polynomialGroupLikeParameter K
  invFun := polynomialGroupLike K
  left_inv := polynomialGroupLike_parameter K
  right_inv := polynomialGroupLikeParameter_apply K

/-- The equivalence reads the linear coefficient. -/
@[simp] theorem polynomialGroupLikeEquiv_apply
    (x : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) :
    polynomialGroupLikeEquiv K x = polynomialGroupLikeParameter K x := rfl

/-- The inverse equivalence constructs the point with the specified parameter. -/
@[simp] theorem polynomialGroupLikeEquiv_symm_apply (k : K) :
    (polynomialGroupLikeEquiv K).symm k = polynomialGroupLike K k := rfl

/-- Over a reduced ring, the linear coefficient distinguishes group-like points. -/
theorem polynomialGroupLikeParameter_injective :
    Function.Injective (polynomialGroupLikeParameter K) :=
  (polynomialGroupLikeEquiv K).injective

/-- Group-like points over a reduced ring are equal when their parameters agree. -/
@[ext] theorem polynomialGroupLike_ext
    {x y : GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))}
    (h : polynomialGroupLikeParameter K x = polynomialGroupLikeParameter K y) : x = y :=
  polynomialGroupLikeParameter_injective K h

/-- Group-like points have the same natural cardinality as the reduced coefficient ring.
As usual, `Nat.card` is zero for infinite types. -/
theorem polynomialGroupLike_natCard :
    Nat.card (GroupLike K[X] (TrivSqZeroExt K[X] (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}))) =
      Nat.card K :=
  Nat.card_congr (polynomialGroupLikeEquiv K)

end Reduced

end TrivSqZeroExt
