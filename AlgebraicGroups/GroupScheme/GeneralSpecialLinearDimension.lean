/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.RingTheory.KrullDimension.FiniteType
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Data.ENat.Monoid
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.SpecialLinear

/-!
# Dimensions of the finite general and special linear group schemes

For a field `K` and a finite matrix index type `n`, this module calculates the
Krull dimensions of the published determinant-localized general linear coordinate
ring and determinant-one special linear Hopf quotient, as well as the topological
Krull dimensions of their actual affine underlying schemes. The formula for SL
uses natural-number subtraction: its rank-zero case has dimension zero.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8: the determinant-localized
  presentation of finite `GL` over a field and the finite `SL` subgroup.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), XI §16,
  Example 16.3: the positive-rank, field-base dimension of `SL_n`.
* Mathlib, `RingTheory/KrullDimension/Polynomial` and
  `RingTheory/KrullDimension/Regular`: polynomial dimensions, maximal-ideal
  height increments and the conditional hypersurface dimension theorem. The proof also
  uses this library's `MvPolynomial.height_ker_eval` and the coordinate-ring
  equivalences, rather than a general dimension-of-open-subscheme formula.
-/

public section

set_option warningAsError true

noncomputable section

open TauCeti.GeneralLinear

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (n : Type u) [Fintype n]

private theorem dimension_polynomialRing :
    ringKrullDim ((TauCeti.MatrixMonoid.CoordinateRing K (Fintype.card n))) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, pow_two]

private theorem dimension_gl :
    ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_eq_of_ringEquiv
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)).toRingEquiv]
  change ringKrullDim (Localization.Away (Matrix.det
    (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K))) = _
  rw [TauCeti.ringKrullDim_localization_away K
    (Matrix.det_mvPolynomialX_ne_zero (Fin (Fintype.card n)) K)]
  exact dimension_polynomialRing K n

private theorem dimension_sl_positive (hpos : 0 < Fintype.card n) :
    ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  let R := (TauCeti.MatrixMonoid.CoordinateRing K (Fintype.card n))
  let determinant := (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det
  let identity : Fin (Fintype.card n) × Fin (Fintype.card n) → K :=
    fun index => (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) K) index.1 index.2
  let relation : R := determinant - 1
  let prime := RingHom.ker (MvPolynomial.eval identity)
  have hmax : prime.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun k => ⟨MvPolynomial.C k, MvPolynomial.eval_C k⟩)
  have hheight : (prime.height : WithBot ℕ∞) = ringKrullDim R := by
    have := hmax
    rw [MvPolynomial.height_eq_natCard_of_isMaximal prime, dimension_polynomialRing]
    simp [Fintype.card_prod, pow_two]
  have det_identity : MvPolynomial.eval identity determinant = 1 := by
    change (MvPolynomial.eval identity)
      ((Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det) = 1
    rw [Matrix.eval_det_mvPolynomialX]
    change (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det = 1
    exact Matrix.det_one
  have hmem : relation ∈ prime := by
    change MvPolynomial.eval identity relation = 0
    simp [relation, det_identity]
  have hne : relation ≠ 0 := by
    have hn : Nonempty (Fin (Fintype.card n)) := Fin.pos_iff_nonempty.mp hpos
    intro h
    have hh := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    have det_zero : MvPolynomial.eval
        (fun _ : Fin (Fintype.card n) × Fin (Fintype.card n) => (0 : K)) determinant = 0 := by
      change (MvPolynomial.eval (fun _ : Fin (Fintype.card n) × Fin (Fintype.card n) => (0 : K)))
        ((Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det) = 0
      rw [Matrix.eval_det_mvPolynomialX]
      change (0 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det = 0
      exact Matrix.det_zero
    have hzeroCoeff : MvPolynomial.constantCoeff determinant = 0 := by
      simpa only [MvPolynomial.eval_zero'] using det_zero
    simp [relation, hzeroCoeff] at hh
  have hreg : relation ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hne
  have hquot : ringKrullDim (R ⧸ Ideal.span {relation}) + 1 = ringKrullDim R := by
    exact @Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      _ _ _ _ hreg _ hmax.isPrime hheight hmem
  have hdim : ringKrullDim (R ⧸ Ideal.span {relation}) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
    apply (ENat.WithBot.add_one_cancel).mp
    rw [hquot, dimension_polynomialRing]
    have hm : 0 < Fintype.card n ^ 2 := pow_pos hpos _
    have hh : Fintype.card n ^ 2 - 1 + 1 = Fintype.card n ^ 2 :=
      Nat.sub_add_cancel hm
    calc
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) =
          ((Fintype.card n ^ 2 - 1 + 1 : ℕ) : WithBot ℕ∞) :=
        congrArg (fun count : ℕ => (count : WithBot ℕ∞)) hh.symm
      _ = ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
  calc
    ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
        ringKrullDim (SpecialLinearCoordinateRing.PolynomialCoordinateRing K n) :=
      (ringKrullDim_eq_of_ringEquiv
        (SpecialLinearCoordinateRing.polynomialEquiv K n).toRingEquiv).symm
    _ = ringKrullDim (R ⧸ Ideal.span {relation}) := rfl
    _ = _ := hdim

private theorem dimension_sl_empty (hzero : Fintype.card n = 0) :
    ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  have hn : IsEmpty (Fin (Fintype.card n)) := by rw [hzero]; infer_instance
  let R := (TauCeti.MatrixMonoid.CoordinateRing K (Fintype.card n))
  have hdet : (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det - 1 = 0 :=
      by
    simp [Matrix.det_isEmpty]
  have hideal : SpecialLinearCoordinateRing.polynomialIdeal K n = ⊥ := by
    simp [SpecialLinearCoordinateRing.polynomialIdeal]
  calc
    ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
        ringKrullDim (SpecialLinearCoordinateRing.PolynomialCoordinateRing K n) :=
      (ringKrullDim_eq_of_ringEquiv
        (SpecialLinearCoordinateRing.polynomialEquiv K n).toRingEquiv).symm
    _ = ringKrullDim (R ⧸ (⊥ : Ideal R)) := by
      change ringKrullDim (R ⧸ SpecialLinearCoordinateRing.polynomialIdeal K n) = _
      exact congrArg (fun I : Ideal R => ringKrullDim (R ⧸ I)) hideal
    _ = ringKrullDim R := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
    _ = ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
      rw [dimension_polynomialRing, hzero]
      simp

/-- The determinant-localized coordinate ring has dimension `card(n)²` over any
field, including finite fields and rank zero. This extends the finite `GL`
presentation in Milne, *Algebraic Groups*, §2.8; the proof uses mathlib's
polynomial evaluation heights and a regular-hypersurface quotient. -/
theorem generalLinearCoordinateRing_ringKrullDim :
    ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  dimension_gl K n

/-- The actual determinant-one Hopf quotient has dimension `card(n)² - 1`,
with natural subtraction, including the empty index type. Milne, *Basic Theory
of Affine Group Schemes*, XI §16, Example 16.3 gives the positive-rank field
dimension; the proof here uses mathlib's hypersurface theorem and treats rank
zero separately. -/
theorem specialLinearCoordinateRing_ringKrullDim :
    ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  by_cases hzero : Fintype.card n = 0
  · exact dimension_sl_empty K n hzero
  · exact dimension_sl_positive K n (Nat.pos_of_ne_zero hzero)

/-- The underlying affine scheme of `GL(n)` has dimension `card(n)²`, by the
coordinate-ring calculation and mathlib's prime-spectrum dimension bridge. -/
theorem generalLinearGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).left =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  rw [TauCeti.GeneralLinear.groupScheme_X_left]
  change topologicalKrullDim
    (PrimeSpectrum ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)))) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact generalLinearCoordinateRing_ringKrullDim K n

/-- The underlying affine scheme of `SL(n)` has dimension `card(n)² - 1`
with natural subtraction, by the coordinate-ring calculation and mathlib's
prime-spectrum dimension bridge. -/
theorem specialLinearGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).left =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  rw [TauCeti.SpecialLinear.groupScheme_X_left]
  change topologicalKrullDim
    (PrimeSpectrum ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)))) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact specialLinearCoordinateRing_ringKrullDim K n

end AlgebraicGeometry
