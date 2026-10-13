/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication
public import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Primitive
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Using antipode reversal of comultiplication

The group algebra over `ℕ` tests arbitrary sums over genuine semiring scalars,
with an independently sized index group. In particular the symmetric group
on three letters gives a noncommutative algebra. The determinant localization
for `GL₂` supplies the complementary noncocommutative example: its commutative
multiplication does not remove the tensor flip. Evaluation at two rational
shear matrices distinguishes the ordered coproduct from its flip, and also
distinguishes antipode reversal from the formula without a flip. Its nonzero
upper-right coordinate is skew-primitive, and its antipode has the reversed
antipode endpoints.

The square of the antipode has an unflipped comultiplication formula. A weighted
sum in the symmetric-group algebra tests this formula without a commutative
multiplication hypothesis. In the coordinate ring of `GL₂`, commutative antipode
involutivity then recovers the ordered entry coproduct, which is still distinct
from its flip.

## References

* Amelia Livingston, Mathlib, `RingTheory/HopfAlgebra/MonoidAlgebra`:
  the canonical Hopf structure on group algebras.
* Robert Hawkins, Mathlib, `RingTheory/HopfAlgebra/Primitive`:
  antipode stability of primitive elements over rings.
* Johannes Hölzl, Yury Kudryashov and Kim Morrison, Mathlib,
  `Algebra/MonoidAlgebra/Defs`: basis-term multiplication and injectivity.
* Mathlib, `Algebra/Group/End` and `Logic/Equiv/Basic`: permutation
  multiplication and transposition evaluation.
* `AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication`: the tensor identity.
* `AlgebraicGroups.Algebra.HopfAlgebra.Antipode`: commutative antipode involutivity.
* `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing`: general linear coordinates.
-/

set_option warningAsError true

@[expose] public noncomputable section

universe u v

open TensorProduct
open scoped BigOperators TensorProduct

namespace HopfAlgebra

-- Specializing skew-antipode reversal to unit endpoints preserves the primitive
-- predicate over semirings; this does not assert the ring formula `S(a) = -a`.
example {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
    {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    Bialgebra.IsPrimitiveElem R (HopfAlgebra.antipode R a) := by
  have hskew : Coalgebra.IsSkewPrimitiveElem R (1 : A) (1 : A) a := ha
  simpa only [antipode_one] using (Coalgebra.IsSkewPrimitiveElem.antipode hskew)

-- At unit endpoints over a ring, skew-primitivity agrees with Mathlib's
-- existing primitive-antipode result.
example {R : Type u} {A : Type v} [CommSemiring R] [Ring A] [HopfAlgebra R A]
    {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    Coalgebra.IsSkewPrimitiveElem R (antipode R (1 : A)) (antipode R (1 : A))
      (antipode R a) := by
  simpa only [antipode_one] using (Bialgebra.IsPrimitiveElem.antipode ha)

/-- Antipode reversal distributes over arbitrary finite sums in a group algebra
 over the natural-number semiring, for a group in any universe. -/
theorem natGroupAlgebra_comul_antipode_sum {G : Type u} [Group G]
    {I : Type v} (s : Finset I) (f : I → MonoidAlgebra ℕ G) :
    Coalgebra.comul (R := ℕ) (antipode ℕ (∑ i ∈ s, f i)) =
      ∑ i ∈ s, map (antipode ℕ) (antipode ℕ)
        (TensorProduct.comm ℕ (MonoidAlgebra ℕ G) (MonoidAlgebra ℕ G)
          (Coalgebra.comul (R := ℕ) (f i))) := by
  rw [comul_antipode]
  simp only [map_sum]

/-- A two-term sum in the noncommutative symmetric-group algebra over `ℕ`
uses the identity on arbitrary elements, not just group-like basis terms. -/
theorem natPermutationGroupAlgebra_comul_antipode
    (x y : MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) :
    Coalgebra.comul (R := ℕ) (antipode ℕ (2 • x + 3 • y)) =
      2 • map (antipode ℕ) (antipode ℕ)
        (TensorProduct.comm ℕ _ _ (Coalgebra.comul (R := ℕ) x)) +
      3 • map (antipode ℕ) (antipode ℕ)
        (TensorProduct.comm ℕ _ _ (Coalgebra.comul (R := ℕ) y)) := by
  rw [comul_antipode]
  simp only [map_add, map_nsmul]

/-- Comultiplication of the antipode square distributes over a weighted sum
in the symmetric-group algebra over `ℕ`, with no tensor flip. -/
theorem natPermutationGroupAlgebra_comul_antipode_antipode
    (x y : MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) :
    Coalgebra.comul (R := ℕ) (antipode ℕ (antipode ℕ (2 • x + 3 • y))) =
      2 • map ((antipode ℕ).comp (antipode ℕ)) ((antipode ℕ).comp (antipode ℕ))
        (Coalgebra.comul (R := ℕ) x) +
      3 • map ((antipode ℕ).comp (antipode ℕ)) ((antipode ℕ).comp (antipode ℕ))
        (Coalgebra.comul (R := ℕ) y) := by
  have h := LinearMap.congr_fun
    (comul_comp_antipode_comp_antipode (R := ℕ)
      (A := MonoidAlgebra ℕ (Equiv.Perm (Fin 3)))) (2 • x + 3 • y)
  simpa only [LinearMap.comp_apply, map_add, map_nsmul] using h

/-- The adjacent-transposition basis terms do not commute in the
symmetric-group algebra over `ℕ`. -/
theorem natPermutationGroupAlgebra_swap_mul_ne :
    (MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1) 1 :
      MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) *
        MonoidAlgebra.single (Equiv.swap (1 : Fin 3) 2) 1 ≠
      MonoidAlgebra.single (Equiv.swap (1 : Fin 3) 2) 1 *
        MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1) 1 := by
  intro h
  simp only [MonoidAlgebra.single_mul_single, mul_one] at h
  have hg := MonoidAlgebra.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h
  have he := congrArg (fun g : Equiv.Perm (Fin 3) ↦ g (0 : Fin 3)) hg
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at he

/-- For every product in the coordinate ring of `GL₂` over `ℚ`, the flipped
 tensor formula combines antipode reversal with multiplicativity of comultiplication. -/
theorem generalLinearTwo_comul_antipode_mul
    (x y : GeneralLinearCoordinateRing.CoordinateRing ℚ (Fin 2)) :
    Coalgebra.comul (R := ℚ) (antipode ℚ (x * y)) =
      map (antipode ℚ) (antipode ℚ)
        (TensorProduct.comm ℚ _ _
          (Coalgebra.comul (R := ℚ) x * Coalgebra.comul (R := ℚ) y)) := by
  rw [comul_antipode, Bialgebra.comul_mul]

end HopfAlgebra

namespace GeneralLinearCoordinateRing

private abbrev TwoCoordinates := CoordinateRing ℚ (Fin 2)
private abbrev TwoMatrices := Matrix.GeneralLinearGroup (Fin 2) ℚ

private def upperShear : TwoMatrices where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def lowerShear : TwoMatrices where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private theorem shear_determinants :
    (upperShear : Matrix (Fin 2) (Fin 2) ℚ).det = 1 ∧
      (lowerShear : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  norm_num [upperShear, lowerShear, Matrix.det_fin_two]

private theorem shear_inverses :
    ((upperShear⁻¹ : TwoMatrices) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, -1; 0, 1] ∧
      ((lowerShear⁻¹ : TwoMatrices) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; -1, 1] :=
  ⟨rfl, rfl⟩

private def evaluatePair (p q : TwoMatrices) :
    TwoCoordinates ⊗[ℚ] TwoCoordinates →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.lift (evaluate p) (evaluate q) (fun _ _ ↦ Commute.all _ _)

private theorem evaluatePair_tmul (p q : TwoMatrices) (x y : TwoCoordinates) :
    evaluatePair p q (x ⊗ₜ[ℚ] y) = evaluate p x * evaluate q y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem evaluate_antipode_entry (p : TwoMatrices) (i j : Fin 2) :
    evaluate p (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) i j)) = p⁻¹ i j := by
  rw [native_antipode_matrix]
  have h := congrArg (fun z : TwoMatrices ↦ z⁻¹ i j) (toGL_evaluate (K := ℚ) p)
  simpa only [toGL, ← Matrix.GeneralLinearGroup.map_inv,
    Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using h

private theorem upperRight_isSkewPrimitive :
    Coalgebra.IsSkewPrimitiveElem ℚ (matrix ℚ (Fin 2) 0 0) (matrix ℚ (Fin 2) 1 1)
      (matrix ℚ (Fin 2) 0 1) where
  counit_eq_zero := by
    rw [native_counit_matrix]
    norm_num [Matrix.one_apply]
  comul_eq_tmul_add_tmul := by
    rw [native_comul_matrix, Fin.sum_univ_two]

private theorem upperRight_ne_zero : matrix ℚ (Fin 2) 0 1 ≠ 0 := by
  intro h
  have h' := congrArg (evaluate upperShear) h
  rw [evaluate_matrix, map_zero] at h'
  norm_num [upperShear] at h'

/-- The nonzero upper-right coordinate of `GL₂` is sent to a skew-primitive
 element with the reversed antipode endpoints. -/
theorem upperRight_antipode_skewPrimitive :
    matrix ℚ (Fin 2) 0 1 ≠ 0 ∧
      Coalgebra.IsSkewPrimitiveElem ℚ
        (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 1 1))
        (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0))
        (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 1)) :=
  ⟨upperRight_ne_zero, upperRight_isSkewPrimitive.antipode⟩

private theorem ordered_comul_entry :
    evaluatePair upperShear lowerShear
      (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0)) = 2 := by
  rw [native_comul_matrix, Fin.sum_univ_two]
  simp only [map_add, evaluatePair_tmul, evaluate_matrix]
  norm_num [upperShear, lowerShear]

private theorem flipped_comul_entry :
    evaluatePair upperShear lowerShear
      (TensorProduct.comm ℚ TwoCoordinates TwoCoordinates
        (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0))) = 1 := by
  rw [native_comul_matrix, Fin.sum_univ_two]
  simp only [map_add, TensorProduct.comm_tmul, evaluatePair_tmul, evaluate_matrix]
  norm_num [upperShear, lowerShear]

private theorem flipped_antipode_comul_entry :
    evaluatePair upperShear lowerShear
      (map (HopfAlgebra.antipode ℚ) (HopfAlgebra.antipode ℚ)
        (TensorProduct.comm ℚ TwoCoordinates TwoCoordinates
          (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0)))) = 1 := by
  rw [native_comul_matrix, Fin.sum_univ_two]
  simp only [map_add, TensorProduct.comm_tmul, TensorProduct.map_tmul,
    evaluatePair_tmul, evaluate_antipode_entry]
  norm_num [upperShear, lowerShear]

private theorem comul_antipode_entry :
    evaluatePair upperShear lowerShear
      (Coalgebra.comul (R := ℚ)
        (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0))) = 1 := by
  rw [HopfAlgebra.comul_antipode]
  exact flipped_antipode_comul_entry

private theorem unflipped_antipode_comul_entry :
    evaluatePair upperShear lowerShear
      (map (HopfAlgebra.antipode ℚ) (HopfAlgebra.antipode ℚ)
        (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0))) = 2 := by
  rw [native_comul_matrix, Fin.sum_univ_two]
  simp only [map_add, TensorProduct.map_tmul, evaluatePair_tmul, evaluate_antipode_entry]
  norm_num [upperShear, lowerShear]

private theorem comul_entry_ne_flip :
    Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0) ≠
      TensorProduct.comm ℚ TwoCoordinates TwoCoordinates
        (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0)) := by
  intro h
  have h' := congrArg (evaluatePair upperShear lowerShear) h
  rw [ordered_comul_entry, flipped_comul_entry] at h'
  norm_num at h'

private theorem comul_antipode_entry_ne_unflipped :
    Coalgebra.comul (R := ℚ) (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0)) ≠
      map (HopfAlgebra.antipode ℚ) (HopfAlgebra.antipode ℚ)
        (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0)) := by
  intro h
  have h' := congrArg (evaluatePair upperShear lowerShear) h
  rw [comul_antipode_entry, unflipped_antipode_comul_entry] at h'
  norm_num at h'

/-- The antipode square preserves the ordered upper-left coordinate coproduct
of `GL₂` over `ℚ`; that coproduct is not its tensor flip. -/
theorem upperLeft_comul_antipode_antipode :
    Coalgebra.comul (R := ℚ)
        (HopfAlgebra.antipode ℚ (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0))) =
      matrix ℚ (Fin 2) 0 0 ⊗ₜ[ℚ] matrix ℚ (Fin 2) 0 0 +
        matrix ℚ (Fin 2) 0 1 ⊗ₜ[ℚ] matrix ℚ (Fin 2) 1 0 ∧
      Coalgebra.comul (R := ℚ)
          (HopfAlgebra.antipode ℚ (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0))) ≠
        TensorProduct.comm ℚ _ _ (Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0)) := by
  have hs :
      Coalgebra.comul (R := ℚ)
          (HopfAlgebra.antipode ℚ (HopfAlgebra.antipode ℚ (matrix ℚ (Fin 2) 0 0))) =
        Coalgebra.comul (R := ℚ) (matrix ℚ (Fin 2) 0 0) := by
    rw [HopfAlgebra.comul_antipode_antipode]
    simp only [native_comul_matrix, Fin.sum_univ_two, map_add, TensorProduct.map_tmul,
      LinearMap.comp_apply, HopfAlgebra.antipode_antipode]
  constructor
  · simpa only [native_comul_matrix, Fin.sum_univ_two] using hs
  · rw [hs]
    exact comul_entry_ne_flip

end GeneralLinearCoordinateRing
