/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Data.ZMod.Basic

/-!
# Antipodes on integer group algebras and general linear coordinates

The infinite commutative group algebra `ℕ[ℤ]` tests antipode involutivity
over scalars without additive inverses. Arbitrary finite sums have their
group supports inverted, and applying the antipode again recovers the sum.
The basis element at integer weight `1` is sent to weight `-1`, which is a
different element. The zero-ring scalar boundary uses the same group-algebra
Hopf instance.

The determinant-localized coordinate ring of `GL₂` over `ℚ` supplies another
commutative Hopf algebra. The client applies the identity to every matrix
coordinate without a cocommutativity assumption.

## References

* Mathlib, `RingTheory/HopfAlgebra/MonoidAlgebra`, by Amelia Livingston:
  the group-algebra Hopf instance and antipode on basis elements.
* `AlgebraicGroups.Algebra.HopfAlgebra.Antipode` and
  `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing`: antipode involutivity
  and determinant-localized general linear coordinates.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace HopfAlgebra

/-- In `ℕ[ℤ]`, the antipode inverts every support in an arbitrary finite sum. -/
theorem natIntegerGroupAlgebra_antipode_sum {ι : Type*} (s : Finset ι)
    (g : ι → Multiplicative ℤ) (c : ι → ℕ) :
    antipode ℕ (∑ i ∈ s, MonoidAlgebra.single (g i) (c i)) =
      ∑ i ∈ s, MonoidAlgebra.single ((g i)⁻¹) (c i) := by
  simp

/-- Applying the antipode twice recovers arbitrary finite sums in `ℕ[ℤ]`. -/
theorem natIntegerGroupAlgebra_antipode_antipode_sum {ι : Type*} (s : Finset ι)
    (g : ι → Multiplicative ℤ) (c : ι → ℕ) :
    antipode ℕ (antipode ℕ (∑ i ∈ s, MonoidAlgebra.single (g i) (c i))) =
      ∑ i ∈ s, MonoidAlgebra.single (g i) (c i) := by
  simp only [antipode_antipode]

/-- Every element of the infinite group algebra `ℕ[ℤ]` is the antipode of an element. -/
theorem natIntegerGroupAlgebra_antipode_surjective :
    Function.Surjective (antipode ℕ (A := MonoidAlgebra ℕ (Multiplicative ℤ))) :=
  antipode_involutive.surjective

/-- The antipode sends the basis element at weight `1` to the basis element at weight `-1`. -/
theorem natIntegerGroupAlgebra_antipode_weight_one :
    antipode ℕ (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℕ)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) (1 : ℕ) := by
  simp

/-- The antipode on `ℕ[ℤ]` is not the identity, as seen at integer weight `1`. -/
theorem natIntegerGroupAlgebra_antipode_weight_one_ne :
    antipode ℕ (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℕ)) ≠
      MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℕ) := by
  rw [natIntegerGroupAlgebra_antipode_weight_one]
  intro h
  have hsupport := (MonoidAlgebra.single_left_inj (by decide : (1 : ℕ) ≠ 0)).1 h
  exact (by decide : Multiplicative.ofAdd (-1 : ℤ) ≠ Multiplicative.ofAdd (1 : ℤ)) hsupport

/-- The same involution identity includes a group algebra over the zero ring. -/
theorem zeroRingIntegerGroupAlgebra_antipode_antipode
    (f : MonoidAlgebra (ZMod 1) (Multiplicative ℤ)) :
    antipode (ZMod 1) (antipode (ZMod 1) f) = f := by
  simp only [antipode_antipode]

/-- Double antipodes recover every matrix coordinate of `GL₂` over `ℚ`. -/
theorem generalLinearTwo_antipode_antipode_matrix (i j : Fin 2) :
    antipode ℚ (antipode ℚ (GeneralLinearCoordinateRing.matrix ℚ (Fin 2) i j)) =
      GeneralLinearCoordinateRing.matrix ℚ (Fin 2) i j := by
  simp only [antipode_antipode]

end HopfAlgebra
