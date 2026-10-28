/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Two weights and a zero scalar comodule

The basis vectors at zero and one in `MonoidAlgebra ℕ ℕ` are distinct group-like
weights. They give two specified right comodules on `ℕ` through
`Coalgebra.RightComodule.ofTensor`. The algebra identity is the basis vector at
one; the basis vector at zero is neither zero nor the algebra identity.

`TwoWeight.weightedCoaction` is the linear map on `ℕ × ℕ` sending `(x, y)` to
`(x, 0) ⊗ₜ basisZero + (0, y) ⊗ₜ basisOne`. Tensorized coordinate projections
and the left unitor recover its two distinct weights.

## Implementation notes

The weighted map is a sum of compositions of existing linear maps. It does not
define a comodule on `ℕ × ℕ`. The bottom-submodule example instead has scalar
coalgebra `ℕ`, with its canonical subtype module structure.

## References

The specified comodule construction is from
`AlgebraicGroups.Algebra.Coalgebra.RightComodule`. The monoid-algebra coalgebra
and its single-element formulas are Mathlib's formalization by Amelia Livingston;
the group-like predicate is due to Yaël Dillies and Michał Mrugała. Tensor products,
linear-map coordinates and unitors use the existing Mathlib developments.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Coalgebra.RightComodule.TwoWeight

/-- The basis vector indexed by zero, with coefficient one. -/
def basisZero : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single 0 1

/-- The basis vector indexed by one, with coefficient one. -/
def basisOne : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single 1 1

private theorem single_groupLike (i : ℕ) :
    IsGroupLikeElem ℕ (MonoidAlgebra.single i (1 : ℕ)) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [MonoidAlgebra.comul_single]

/-- The basis vector indexed by zero is group-like. -/
theorem basisZero_groupLike : IsGroupLikeElem ℕ basisZero := single_groupLike 0

/-- The basis vector indexed by one is group-like. -/
theorem basisOne_groupLike : IsGroupLikeElem ℕ basisOne := single_groupLike 1

/-- Evaluating the coefficient at zero distinguishes the two weights. -/
theorem basisZero_ne_basisOne : basisZero ≠ basisOne := by
  intro h
  have hcoeff := congrArg (fun a : MonoidAlgebra ℕ ℕ => a.coeff 0) h
  simp [basisZero, basisOne, MonoidAlgebra.coeff_single] at hcoeff

/-- The first weight is not the additive zero. -/
theorem basisZero_ne_zero : basisZero ≠ 0 := basisZero_groupLike.ne_zero

/-- The second weight is not the additive zero. -/
theorem basisOne_ne_zero : basisOne ≠ 0 := basisOne_groupLike.ne_zero

/-- The second weight, not the first, is the monoid-algebra identity. -/
@[simp] theorem basisOne_eq_one : basisOne = 1 := rfl

/-- The basis vector at zero is not the monoid-algebra identity. -/
theorem basisZero_ne_one : basisZero ≠ 1 := by
  simpa only [basisOne_eq_one] using basisZero_ne_basisOne

/-- The specified comodule on `ℕ` with the basis-zero weight. -/
def basisZeroComodule : RightComodule ℕ (MonoidAlgebra ℕ ℕ) ℕ :=
  ofTensor basisZero basisZero_groupLike.comul_eq_tmul_self
    (fun n => by rw [basisZero_groupLike.counit_eq_one, one_smul])

/-- The specified comodule on `ℕ` with the basis-one weight. -/
def basisOneComodule : RightComodule ℕ (MonoidAlgebra ℕ ℕ) ℕ :=
  ofTensor basisOne basisOne_groupLike.comul_eq_tmul_self
    (fun n => by rw [basisOne_groupLike.counit_eq_one, one_smul])

/-- The first specified input has the basis-zero coaction. -/
@[simp] theorem basisZeroComodule_coaction (n : ℕ) :
    basisZeroComodule.coaction n = n ⊗ₜ[ℕ] basisZero := rfl

/-- The second specified input has the basis-one coaction. -/
@[simp] theorem basisOneComodule_coaction (n : ℕ) :
    basisOneComodule.coaction n = n ⊗ₜ[ℕ] basisOne := rfl

/-- The two specified input comodules are distinct, as witnessed by the left unitor. -/
theorem basisZeroComodule_ne_basisOneComodule : basisZeroComodule ≠ basisOneComodule := by
  intro h
  apply basisZero_ne_basisOne
  have ht := congrArg (fun X : RightComodule ℕ (MonoidAlgebra ℕ ℕ) ℕ =>
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ) (X.coaction 1)) h
  simpa using ht

/-- The independent two-weight linear map, formed by sums and compositions of
coordinate maps with `TensorProduct.mk`. -/
def weightedCoaction : (ℕ × ℕ) →ₗ[ℕ] (ℕ × ℕ) ⊗[ℕ] MonoidAlgebra ℕ ℕ :=
  (TensorProduct.mk ℕ (ℕ × ℕ) (MonoidAlgebra ℕ ℕ)).flip basisZero ∘ₗ
      (LinearMap.inl ℕ ℕ ℕ ∘ₗ LinearMap.fst ℕ ℕ ℕ) +
    (TensorProduct.mk ℕ (ℕ × ℕ) (MonoidAlgebra ℕ ℕ)).flip basisOne ∘ₗ
      (LinearMap.inr ℕ ℕ ℕ ∘ₗ LinearMap.snd ℕ ℕ ℕ)

/-- The element formula for the independent two-weight linear map. -/
@[simp] theorem weightedCoaction_apply (x y : ℕ) :
    weightedCoaction (x, y) =
      (x, 0) ⊗ₜ[ℕ] basisZero + (0, y) ⊗ₜ[ℕ] basisOne := rfl

/-- The first coordinate vector has the basis-zero weight. -/
@[simp] theorem weightedCoaction_one_zero :
    weightedCoaction (1, 0) = (1, 0) ⊗ₜ[ℕ] basisZero := by
  simp only [weightedCoaction_apply, ← Prod.zero_eq_mk, TensorProduct.zero_tmul, add_zero]

/-- The second coordinate vector has the basis-one weight. -/
@[simp] theorem weightedCoaction_zero_one :
    weightedCoaction (0, 1) = (0, 1) ⊗ₜ[ℕ] basisOne := by
  simp only [weightedCoaction_apply, ← Prod.zero_eq_mk, TensorProduct.zero_tmul, zero_add]

/-- Tensorized first projection reads off the basis-zero coordinate. -/
@[simp] theorem fst_weightedCoaction (x y : ℕ) :
    (LinearMap.fst ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ) (weightedCoaction (x, y)) =
      x ⊗ₜ[ℕ] basisZero := by
  simp [LinearMap.rTensor_tmul]

/-- Tensorized second projection reads off the basis-one coordinate. -/
@[simp] theorem snd_weightedCoaction (x y : ℕ) :
    (LinearMap.snd ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ) (weightedCoaction (x, y)) =
      y ⊗ₜ[ℕ] basisOne := by
  simp [LinearMap.rTensor_tmul]

/-- First projection followed by the left unitor recovers the first weight. -/
@[simp] theorem lid_fst_weightedCoaction_one_zero :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
      ((LinearMap.fst ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ)
        (weightedCoaction (1, 0))) = basisZero := by simp

/-- Second projection followed by the left unitor recovers the second weight. -/
@[simp] theorem lid_snd_weightedCoaction_zero_one :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
      ((LinearMap.snd ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ)
        (weightedCoaction (0, 1))) = basisOne := by simp

/-- The two recovered weights differ; no injectivity of tensoring is assumed. -/
theorem projected_weights_ne :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        ((LinearMap.fst ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ)
          (weightedCoaction (1, 0))) ≠
      TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        ((LinearMap.snd ℕ ℕ ℕ).rTensor (MonoidAlgebra ℕ ℕ)
          (weightedCoaction (0, 1))) := by
  simpa only [lid_fst_weightedCoaction_one_zero, lid_snd_weightedCoaction_zero_one]
    using basisZero_ne_basisOne

end Coalgebra.RightComodule.TwoWeight

namespace Coalgebra.RightComodule

/-- The scalar right comodule on the bottom submodule of `ℕ`. -/
def zeroBoundary : RightComodule ℕ ℕ (⊥ : Submodule ℕ ℕ) :=
  scalar ℕ (⊥ : Submodule ℕ ℕ)

/-- The bottom submodule has only its zero vector. -/
theorem zeroBoundary_eq_zero (u : (⊥ : Submodule ℕ ℕ)) : u = 0 := by
  apply Subtype.ext
  exact (Submodule.mem_bot ℕ).mp u.property

/-- Every vector in the zero boundary has zero coaction. -/
@[simp] theorem zeroBoundary_coaction (u : (⊥ : Submodule ℕ ℕ)) :
    zeroBoundary.coaction u = 0 := by
  rw [zeroBoundary_eq_zero u, map_zero]

end Coalgebra.RightComodule
