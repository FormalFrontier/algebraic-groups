/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.Data.ZMod.Basic

/-!
# Group-like evaluation on positive weights over `ZMod 6`

In the monoid algebra on `Multiplicative ℕ` over `ZMod 6`, the normalized
basis point of weight `1` is group-like. Mathlib's `liftGroupLikeBialgHom`
evaluates the monoid algebra on the group-like elements at their values.
The induced `BialgHom.groupLikeMap` sends the basis point indexed by the
weight-`1` point to that point, and its square to the basis point of weight `2`.
Coefficient calculations separate the weight-`1` point from its square and
from the constant point.

The coalgebra transport and its scalar-source correspondence are evaluated
at the scalar `5`: both transport followed by scalar multiplication and
postcomposition of the scalar-source morphism give the basis vector with
coefficient `5` at weight `1`.

## Implementation notes

The scalar ring has zero divisors, and the weight monoid is the multiplicative
tag of the additive monoid `ℕ`. All algebra, bialgebra, coalgebra, and monoid
instances are Mathlib's; the computations use only bialgebra and coalgebra
transport.

## References

The monoid-algebra bialgebra, its normalized basis points, and its evaluation
morphism are provided by Amelia Livingston, Yaël Dillies, and Michał Mrugała
in Mathlib's `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`. The computations
use `MonoidAlgebra.lift_single`, `smul_single`, and `single_mul_single`, together
with the group-like transport and scalar-source correspondence in
`AlgebraicGroups.Algebra.Bialgebra.GroupLike` and
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom`.
-/

@[expose] public section

noncomputable section

namespace MonoidAlgebra.PositiveWeights

local notation "R₆" => ZMod 6
local notation "Gₙ" => Multiplicative ℕ
local notation "A₆" => MonoidAlgebra R₆ Gₙ

/-- The normalized basis point of weight `1` over `ZMod 6`. -/
def weightOne : GroupLike R₆ A₆ where
  val := single (Multiplicative.ofAdd 1) 1
  isGroupLikeElem_val := isGroupLikeElem_single_one _

/-- The underlying value of the normalized weight-`1` point. -/
@[simp]
theorem weightOne_val : weightOne.val = single (Multiplicative.ofAdd 1) 1 := rfl

/-- The normalized basis point indexed by `weightOne` in the evaluation source. -/
def evaluationPoint : GroupLike R₆ (MonoidAlgebra R₆ (GroupLike R₆ A₆)) where
  val := single weightOne 1
  isGroupLikeElem_val := isGroupLikeElem_single_one _

/-- The evaluation-source point has coefficient `1` at `weightOne`. -/
@[simp]
theorem evaluationPoint_val : evaluationPoint.val = single weightOne 1 := rfl

private theorem evaluation_single_weightOne (r : R₆) :
    liftGroupLikeBialgHom (R := R₆) (A := A₆) (single weightOne r) =
      single (Multiplicative.ofAdd 1) r := by
  simp [liftGroupLikeBialgHom, weightOne_val, smul_eq_mul]

/-- The induced monoid map evaluates the source point to the weight-`1` basis vector. -/
theorem groupLikeMap_evaluationPoint_val :
    ((liftGroupLikeBialgHom (R := R₆) (A := A₆)).groupLikeMap evaluationPoint).val =
      single (Multiplicative.ofAdd 1) 1 := by
  rw [BialgHom.groupLikeMap_val, evaluationPoint_val]
  exact evaluation_single_weightOne 1

/-- The induced monoid map sends the source point to `weightOne`. -/
@[simp]
theorem groupLikeMap_evaluationPoint :
    (liftGroupLikeBialgHom (R := R₆) (A := A₆)).groupLikeMap evaluationPoint =
      weightOne := by
  apply GroupLike.val_injective
  rw [groupLikeMap_evaluationPoint_val, weightOne_val]

/-- Squaring the weight-`1` point gives the normalized basis vector of weight `2`. -/
theorem weightOne_mul_weightOne_val :
    (weightOne * weightOne).val = single (Multiplicative.ofAdd 2) 1 := by
  simp only [GroupLike.val_mul, weightOne_val, single_mul_single, mul_one]
  rfl

/-- The induced monoid map sends the square of the source point to weight `2`. -/
theorem groupLikeMap_evaluationPoint_mul_val :
    ((liftGroupLikeBialgHom (R := R₆) (A := A₆)).groupLikeMap
      (evaluationPoint * evaluationPoint)).val = single (Multiplicative.ofAdd 2) 1 := by
  rw [map_mul]
  simp only [GroupLike.val_mul, BialgHom.groupLikeMap_val, evaluationPoint_val,
    evaluation_single_weightOne, single_mul_single, mul_one]
  rfl

/-- The weight-`1` point differs from its weight-`2` square, as seen at weight `1`. -/
theorem weightOne_ne_mul_self : weightOne ≠ weightOne * weightOne := by
  intro h
  have hc := congrArg
    (fun g : GroupLike R₆ A₆ => g.val.coeff (Multiplicative.ofAdd 1)) h
  rw [weightOne_val, weightOne_mul_weightOne_val] at hc
  have h21 : (Multiplicative.ofAdd 2 : Gₙ) ≠ Multiplicative.ofAdd 1 := by decide
  exact (by decide : (1 : R₆) ≠ 0) (by simpa [h21] using hc)

/-- The weight-`1` point differs from the constant point, as seen at weight `1`. -/
theorem weightOne_ne_one : weightOne ≠ 1 := by
  intro h
  have hc := congrArg
    (fun g : GroupLike R₆ A₆ => g.val.coeff (Multiplicative.ofAdd 1)) h
  rw [weightOne_val, GroupLike.val_one, one_def] at hc
  have h01 : (1 : Gₙ) ≠ Multiplicative.ofAdd 1 := by decide
  exact (by decide : (1 : R₆) ≠ 0) (by simpa [h01] using hc)

/-- The fixed scalar ring has the nonzero zero divisors `2` and `3`. -/
theorem zmod_six_zero_divisors :
    (2 : R₆) ≠ 0 ∧ (3 : R₆) ≠ 0 ∧ (2 : R₆) * 3 = 0 := by
  decide

/-- The scalar-source morphism of the evaluation point puts coefficient `5` at `weightOne`. -/
theorem coalgHomEquiv_evaluationPoint_five :
    GroupLike.coalgHomEquiv evaluationPoint (5 : R₆) = single weightOne 5 := by
  rw [GroupLike.coalgHomEquiv_apply, evaluationPoint_val]
  simp only [smul_single, smul_eq_mul, mul_one]

/-- Naturality for evaluation gives coefficient `5` at weight `1` on both routes. -/
theorem coalgHomEquiv_map_evaluationPoint_five :
    GroupLike.coalgHomEquiv
        (GroupLike.map (liftGroupLikeBialgHom (R := R₆) (A := A₆)).toCoalgHom
          evaluationPoint) (5 : R₆) = single (Multiplicative.ofAdd 1) 5 ∧
      ((liftGroupLikeBialgHom (R := R₆) (A := A₆)).toCoalgHom.comp
        (GroupLike.coalgHomEquiv evaluationPoint)) (5 : R₆) =
          single (Multiplicative.ofAdd 1) 5 := by
  have hpost :
      ((liftGroupLikeBialgHom (R := R₆) (A := A₆)).toCoalgHom.comp
        (GroupLike.coalgHomEquiv evaluationPoint)) (5 : R₆) =
          single (Multiplicative.ofAdd 1) 5 := by
    rw [CoalgHom.comp_apply, coalgHomEquiv_evaluationPoint_five,
      BialgHom.toCoalgHom_apply]
    exact evaluation_single_weightOne 5
  refine ⟨?_, hpost⟩
  rw [GroupLike.coalgHomEquiv_map]
  exact hpost

end MonoidAlgebra.PositiveWeights
