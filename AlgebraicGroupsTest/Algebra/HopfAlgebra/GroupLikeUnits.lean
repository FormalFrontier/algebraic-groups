/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Data.ZMod.Basic

/-!
# Nonmonomial group-like units and counit normalization

The group algebra of `Multiplicative ℤ` over `ZMod 2 × ZMod 2` has a group-like
point with two nonzero coefficients. The complementary idempotents `(1, 0)` and
`(0, 1)` kill the cross terms in the tensor product over the product ring. Its
antipode is a distinct, explicitly computed inverse, and its image under
`GroupLike.toUnits` is not a scalar multiple of any single group basis element.
All structures are the canonical self-base and group-algebra structures.

In the group algebra over `ZMod 6`, the constant scalar `5` is a self-inverse
unit whose antipode agrees with its inverse. Its counit is nevertheless `5`,
not `1`, so this unit is outside the image of `GroupLike.toUnits`.

## References

* Mathlib, `RingTheory/Coalgebra/MonoidAlgebra` and
  `RingTheory/HopfAlgebra/MonoidAlgebra`, by Amelia Livingston: the canonical
  coalgebra and Hopf algebra structures and their formulas on single terms.
* Mathlib, `RingTheory/Coalgebra/GroupLike`,
  `RingTheory/Bialgebra/GroupLike`, and `RingTheory/HopfAlgebra/GroupLike`, by
  Yaël Dillies and Michał Mrugała: normalized group-like elements, their group
  structure, antipode cancellation, and the homomorphism to units.
* Mathlib, `Data/ZMod/Basic`, by Chris Hughes: the residue coefficient rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MonoidAlgebra
namespace ProductIdempotents

local notation "R₂" => ZMod 2 × ZMod 2
local notation "G₂" => Multiplicative ℤ
local notation "A₂" => MonoidAlgebra R₂ G₂
local notation "e₀" => ((1, 0) : R₂)
local notation "e₁" => ((0, 1) : R₂)
local notation "g" => Multiplicative.ofAdd (1 : ℤ)

private theorem left_ne_zero : e₀ ≠ 0 := by simp
private theorem right_ne_zero : e₁ ≠ 0 := by simp
private theorem left_mul_left : e₀ * e₀ = e₀ := by ext <;> simp
private theorem left_mul_right : e₀ * e₁ = 0 := by ext <;> simp
private theorem right_mul_left : e₁ * e₀ = 0 := by ext <;> simp
private theorem right_mul_right : e₁ * e₁ = e₁ := by ext <;> simp
private theorem left_add_right : e₀ + e₁ = 1 := by ext <;> simp

private theorem generator_ne_one : g ≠ (1 : G₂) := by decide
private theorem inverse_generator_ne_one : g⁻¹ ≠ (1 : G₂) := by decide
private theorem generator_ne_inverse : g ≠ g⁻¹ := by decide

/-- The two coefficients are nonzero zero divisors in the product ring. -/
theorem coefficient_zero_divisors : e₀ ≠ 0 ∧ e₁ ≠ 0 ∧ e₀ * e₁ = 0 :=
  ⟨left_ne_zero, right_ne_zero, left_mul_right⟩

/-- A two-support combination with complementary idempotent coefficients. -/
def mixed : A₂ := single g e₀ + single 1 e₁

/-- The combination obtained by inverting the two supports of `mixed`. -/
def mixedInverse : A₂ := single g⁻¹ e₀ + single 1 e₁

/-- The coefficient at integer weight `1` is the first nonzero idempotent. -/
@[simp] theorem mixed_coeff_generator : mixed.coeff g = e₀ := by
  simp [mixed]

/-- The coefficient at the identity is the second nonzero idempotent. -/
@[simp] theorem mixed_coeff_one : mixed.coeff 1 = e₁ := by
  simp [mixed]

/-- The support of `mixed` does not contain integer weight `-1`. -/
@[simp] theorem mixed_coeff_inverse_generator : mixed.coeff g⁻¹ = 0 := by
  simp [mixed, generator_ne_inverse]

/-- The coefficient of `mixedInverse` at integer weight `-1` is `(1, 0)`. -/
@[simp] theorem mixedInverse_coeff_inverse_generator : mixedInverse.coeff g⁻¹ = e₀ := by
  simp [mixedInverse]

/-- The coefficient of `mixedInverse` at the identity is `(0, 1)`. -/
@[simp] theorem mixedInverse_coeff_one : mixedInverse.coeff 1 = e₁ := by
  simp [mixedInverse]

/-- The support of `mixedInverse` does not contain integer weight `1`. -/
@[simp] theorem mixedInverse_coeff_generator : mixedInverse.coeff g = 0 := by
  simp [mixedInverse, generator_ne_inverse]

private theorem single_eq_smul (k : G₂) (r : R₂) :
    (single k r : A₂) = r • single k (1 : R₂) := by
  simp [smul_eq_mul]

private theorem single_tmul_single (k l : G₂) (r s : R₂) :
    (single k r : A₂) ⊗ₜ[R₂] single l s =
      (r * s) • ((single k 1 : A₂) ⊗ₜ[R₂] single l 1) := by
  rw [single_eq_smul k r, single_eq_smul l s, TensorProduct.smul_tmul_smul]

private theorem comul_single_scalar (k : G₂) (r : R₂) :
    Coalgebra.comul (R := R₂) (single k r : A₂) =
      r • ((single k 1 : A₂) ⊗ₜ[R₂] single k 1) := by
  simp only [MonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, lsingle_apply]
  rw [single_eq_smul k r, TensorProduct.tmul_smul]

/-- The sum of the two coefficients is the counit normalization `1`. -/
@[simp] theorem mixed_counit : Coalgebra.counit (R := R₂) mixed = 1 := by
  simp only [mixed, map_add, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  exact left_add_right

/-- Tensor balancing over the product ring makes both cross terms vanish. -/
@[simp] theorem mixed_comul : Coalgebra.comul (R := R₂) mixed = mixed ⊗ₜ[R₂] mixed := by
  calc
    Coalgebra.comul (R := R₂) mixed =
        e₀ • ((single g 1 : A₂) ⊗ₜ[R₂] single g 1) +
          e₁ • ((single 1 1 : A₂) ⊗ₜ[R₂] single 1 1) := by
      rw [mixed, map_add, comul_single_scalar, comul_single_scalar]
    _ = mixed ⊗ₜ[R₂] mixed := by
      symm
      simp only [mixed, TensorProduct.add_tmul, TensorProduct.tmul_add]
      rw [single_tmul_single g g e₀ e₀, single_tmul_single g 1 e₀ e₁,
        single_tmul_single 1 g e₁ e₀, single_tmul_single 1 1 e₁ e₁]
      simp only [left_mul_left, left_mul_right, right_mul_left, right_mul_right,
        zero_smul, add_zero, zero_add]

/-- The two-support combination is normalized and group-like. -/
theorem mixed_isGroupLike : IsGroupLikeElem R₂ mixed where
  counit_eq_one := mixed_counit
  comul_eq_tmul_self := mixed_comul

/-- The antipode inverts supports and leaves the product-ring coefficients fixed. -/
@[simp] theorem mixed_antipode : HopfAlgebra.antipode R₂ mixed = mixedInverse := by
  simp [mixed, mixedInverse]

/-- Antipode cancellation gives the right inverse, despite the zero divisors. -/
@[simp] theorem mixed_mul_inverse : mixed * mixedInverse = 1 := by
  simpa only [mixed_antipode] using mixed_isGroupLike.mul_antipode_cancel

/-- Antipode cancellation also gives the left inverse. -/
@[simp] theorem inverse_mul_mixed : mixedInverse * mixed = 1 := by
  simpa only [mixed_antipode] using mixed_isGroupLike.antipode_mul_cancel

/-- Squaring the combination doubles its nonconstant integer weight. -/
theorem mixed_mul_self : mixed * mixed = single (g ^ 2) e₀ + single 1 e₁ := by
  simp only [mixed, add_mul, mul_add, single_mul_single, left_mul_left,
    left_mul_right, right_mul_left, right_mul_right, single_zero, add_zero,
    zero_add, mul_one, one_mul, pow_two]

/-- The explicitly computed inverse is also normalized and group-like. -/
theorem mixedInverse_isGroupLike : IsGroupLikeElem R₂ mixedInverse := by
  rw [← mixed_antipode]
  exact mixed_isGroupLike.antipode

/-- Applying the antipode to the inverse recovers the two-support combination. -/
@[simp] theorem mixedInverse_antipode : HopfAlgebra.antipode R₂ mixedInverse = mixed := by
  rw [← mixed_antipode]
  exact mixed_isGroupLike.antipode_antipode

/-- Integer weights `1` and `-1` distinguish the combination from its inverse. -/
theorem mixed_ne_inverse : mixed ≠ mixedInverse := by
  intro h
  have hc := congrArg (fun z : A₂ => z.coeff g) h
  exact left_ne_zero (by simpa only [mixed_coeff_generator, mixedInverse_coeff_generator] using hc)

/-- Two distinct nonzero coefficients exclude every scalar multiple of a single basis element. -/
theorem mixed_ne_single (k : G₂) (c : R₂) : mixed ≠ single k c := by
  intro h
  by_cases hk : k = g
  · subst k
    have hc := congrArg (fun z : A₂ => z.coeff 1) h
    exact right_ne_zero (by
      simpa only [mixed_coeff_one, coeff_single,
        Finsupp.single_eq_of_ne (Ne.symm generator_ne_one)] using hc)
  · have hc := congrArg (fun z : A₂ => z.coeff g) h
    exact left_ne_zero (by
      simpa only [mixed_coeff_generator, coeff_single,
        Finsupp.single_eq_of_ne (Ne.symm hk)] using hc)

/-- The combination is not the zero element. -/
theorem mixed_ne_zero : mixed ≠ 0 := by
  simpa only [single_zero] using mixed_ne_single (1 : G₂) (0 : R₂)

/-- The combination is not the constant group-like point. -/
theorem mixed_ne_one : mixed ≠ 1 := by
  simpa only [one_def] using mixed_ne_single (1 : G₂) (1 : R₂)

/-- The normalized two-support point in the canonical group of group-like elements. -/
def mixedGroupLike : GroupLike R₂ A₂ where
  val := mixed
  isGroupLikeElem_val := mixed_isGroupLike

/-- The bundled point has the prescribed two-support value. -/
@[simp] theorem mixedGroupLike_val : (mixedGroupLike : A₂) = mixed := rfl

/-- Inversion of the bundled point has the computed antipode value. -/
@[simp] theorem mixedGroupLike_inv_val :
    ((mixedGroupLike⁻¹ : GroupLike R₂ A₂) : A₂) = mixedInverse := by
  rw [GroupLike.val_inv, mixedGroupLike_val, mixed_antipode]

/-- The homomorphism to units preserves the prescribed two-support value. -/
@[simp] theorem mixedGroupLike_toUnits_val :
    ((GroupLike.toUnits R₂ mixedGroupLike : A₂ˣ) : A₂) = mixed := rfl

/-- The inverse unit has the distinct, explicitly computed antipode value. -/
@[simp] theorem mixedGroupLike_toUnits_inv_val :
    (((GroupLike.toUnits R₂ mixedGroupLike)⁻¹ : A₂ˣ) : A₂) = mixedInverse := by
  change HopfAlgebra.antipode R₂ mixed = mixedInverse
  exact mixed_antipode

/-- Mapping the inverse group-like point to units also gives `mixedInverse`. -/
@[simp] theorem mixedGroupLike_inv_toUnits_val :
    ((GroupLike.toUnits R₂ (mixedGroupLike⁻¹) : A₂ˣ) : A₂) = mixedInverse := by
  change ((mixedGroupLike⁻¹ : GroupLike R₂ A₂) : A₂) = mixedInverse
  exact mixedGroupLike_inv_val

/-- Multiplication of the point and its inverse has value `1`. -/
theorem mixedGroupLike_mul_inv_val :
    ((mixedGroupLike * mixedGroupLike⁻¹ : GroupLike R₂ A₂) : A₂) = 1 := by
  rw [GroupLike.val_mul, mixedGroupLike_val, mixedGroupLike_inv_val, mixed_mul_inverse]

/-- The unit attached to the square has the doubled-weight two-support value. -/
theorem mixedGroupLike_toUnits_mul_self_val :
    ((GroupLike.toUnits R₂ (mixedGroupLike * mixedGroupLike) : A₂ˣ) : A₂) =
      single (g ^ 2) e₀ + single 1 e₁ := by
  simp only [map_mul, Units.val_mul, mixedGroupLike_toUnits_val, mixed_mul_self]

/-- The unit product evaluates to the computed product of the two combinations. -/
theorem mixedGroupLike_toUnits_mul_inv_val :
    (((GroupLike.toUnits R₂ mixedGroupLike) * (GroupLike.toUnits R₂ mixedGroupLike)⁻¹ : A₂ˣ) : A₂) =
      1 := by
  rw [Units.val_mul, mixedGroupLike_toUnits_val, mixedGroupLike_toUnits_inv_val,
    mixed_mul_inverse]

/-- The unit supplied by group-likeness has a genuinely nonmonomial value. -/
theorem mixedGroupLike_toUnits_ne_single (k : G₂) (c : R₂) :
    ((GroupLike.toUnits R₂ mixedGroupLike : A₂ˣ) : A₂) ≠ single k c := by
  rw [mixedGroupLike_toUnits_val]
  exact mixed_ne_single k c

/-- The two-support combination is a unit by the group-like antipode identities. -/
theorem mixed_isUnit : IsUnit mixed := mixed_isGroupLike.isUnit

end ProductIdempotents

namespace ResidueSix

local notation "R₆" => ZMod 6
local notation "G₆" => Multiplicative ℤ
local notation "A₆" => MonoidAlgebra R₆ G₆

private theorem five_mul_five : (5 : R₆) * 5 = 1 := by decide
private theorem five_ne_one : (5 : R₆) ≠ 1 := by decide

/-- The constant scalar `5` in the group algebra over `ZMod 6`. -/
def scalarFive : A₆ := single 1 (5 : R₆)

/-- The constant scalar `5` is its own multiplicative inverse. -/
@[simp] theorem scalarFive_mul_self : scalarFive * scalarFive = 1 := by
  simp only [scalarFive, single_mul_single, one_mul, five_mul_five, ← one_def]

/-- The counit retains the scalar coefficient, rather than normalizing it. -/
@[simp] theorem scalarFive_counit : Coalgebra.counit (R := R₆) scalarFive = 5 := by
  simp [scalarFive]

/-- The scalar unit fails the counit normalization for group-like elements. -/
theorem scalarFive_counit_ne_one : Coalgebra.counit (R := R₆) scalarFive ≠ 1 := by
  rw [scalarFive_counit]
  exact five_ne_one

/-- The antipode fixes the constant scalar `5`. -/
@[simp] theorem scalarFive_antipode : HopfAlgebra.antipode R₆ scalarFive = scalarFive := by
  simp [scalarFive]

/-- An invertible scalar need not be normalized and group-like. -/
theorem scalarFive_not_isGroupLike : ¬ IsGroupLikeElem R₆ scalarFive := by
  intro h
  exact scalarFive_counit_ne_one h.counit_eq_one

/-- The scalar `5` bundled as a unit using its computed square. -/
def scalarFiveUnit : A₆ˣ where
  val := scalarFive
  inv := scalarFive
  val_inv := scalarFive_mul_self
  inv_val := scalarFive_mul_self

/-- The scalar unit has value `single 1 5`. -/
@[simp] theorem scalarFiveUnit_val : (scalarFiveUnit : A₆) = scalarFive := rfl

/-- The inverse scalar unit again has value `single 1 5`. -/
@[simp] theorem scalarFiveUnit_inv_val : ((scalarFiveUnit⁻¹ : A₆ˣ) : A₆) = scalarFive := rfl

/-- The constant scalar `5` is a unit without being group-like. -/
theorem scalarFive_isUnit : IsUnit scalarFive := scalarFiveUnit.isUnit

/-- Agreement of an antipode with a unit inverse does not imply group-likeness. -/
theorem scalarFiveUnit_antipode_eq_inv :
    HopfAlgebra.antipode R₆ (scalarFiveUnit : A₆) = ((scalarFiveUnit⁻¹ : A₆ˣ) : A₆) := by
  rw [scalarFiveUnit_val, scalarFiveUnit_inv_val, scalarFive_antipode]

/-- The scalar unit is outside the image of the group-like-to-unit homomorphism. -/
theorem scalarFiveUnit_not_mem_range :
    scalarFiveUnit ∉ Set.range (GroupLike.toUnits R₆ (A := A₆)) := by
  rintro ⟨q, hq⟩
  have hval := congrArg (fun u : A₆ˣ => (u : A₆)) hq
  change (q : A₆) = scalarFive at hval
  have hc := q.isGroupLikeElem_val.counit_eq_one
  rw [hval, scalarFive_counit] at hc
  exact five_ne_one hc

end ResidueSix
end MonoidAlgebra
