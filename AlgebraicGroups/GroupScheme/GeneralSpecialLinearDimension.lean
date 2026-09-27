/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.PolynomialRationalPointHeight
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
-/

public section

set_option warningAsError true

noncomputable section

open GeneralLinearCoordinateRing

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (n : Type u) [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem dimension_polynomialRing :
    ringKrullDim (GeneralLinearCoordinateRing.PolynomialRing K n) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, pow_two]

private theorem dimension_gl :
    ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  let R := GeneralLinearCoordinateRing.PolynomialRing K n
  let determinant := GeneralLinearCoordinateRing.determinant K n
  let identity : n × n → K := fun index => (1 : Matrix n n K) index.1 index.2
  let q : Polynomial R := Polynomial.C determinant * Polynomial.X - 1
  let evaluation := Polynomial.eval₂RingHom (MvPolynomial.eval identity) (1 : K)
  let prime := RingHom.ker evaluation
  have hmax : prime.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _
      (fun k => ⟨Polynomial.C (MvPolynomial.C k), by simp [evaluation]⟩)
  have hover : prime.LiesOver (RingHom.ker (MvPolynomial.eval identity)) := by
    constructor
    ext p
    simp [prime, evaluation, Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker]
  have hheight : (prime.height : WithBot ℕ∞) = ringKrullDim (Polynomial R) := by
    have h : prime.height =
        (RingHom.ker (MvPolynomial.eval identity)).height + 1 :=
      @Polynomial.height_eq_height_add_one _ _ _ _ _ hmax hover
    rw [h, MvPolynomial.height_ker_eval, Polynomial.ringKrullDim_of_isNoetherianRing,
      dimension_polynomialRing]
    simp [Fintype.card_prod, pow_two]
  have det_identity : MvPolynomial.eval identity determinant = 1 := by
    change (MvPolynomial.eval identity) ((Matrix.mvPolynomialX n n K).det) = 1
    rw [Matrix.eval_det_mvPolynomialX]
    change (1 : Matrix n n K).det = 1
    exact Matrix.det_one
  have hmem : q ∈ prime := by
    change evaluation q = 0
    simp [q, evaluation, det_identity]
  have hne : q ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval₂ (MvPolynomial.eval identity) (0 : K)) h
    simp [q, Polynomial.eval₂_sub] at hh
  have hreg : q ∈ nonZeroDivisors (Polynomial R) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hne
  have hquot : ringKrullDim (Polynomial R ⧸ Ideal.span {q}) + 1 =
      ringKrullDim (Polynomial R) := by
    exact @Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      _ _ _ _ hreg _ hmax.isPrime hheight hmem
  have hdim : ringKrullDim (Polynomial R ⧸ Ideal.span {q}) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
    apply (ENat.WithBot.add_one_cancel).mp
    rw [hquot, Polynomial.ringKrullDim_of_isNoetherianRing, dimension_polynomialRing]
  calc
    ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing K n) =
        ringKrullDim (AdjoinRoot q) :=
      ringKrullDim_eq_of_ringEquiv (GeneralLinearCoordinateRing.quotientEquiv K n).toRingEquiv
    _ = ringKrullDim (Polynomial R ⧸ Ideal.span {q}) := rfl
    _ = _ := hdim

private theorem dimension_sl_positive (hpos : 0 < Fintype.card n) :
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  let R := GeneralLinearCoordinateRing.PolynomialRing K n
  let determinant := GeneralLinearCoordinateRing.determinant K n
  let identity : n × n → K := fun index => (1 : Matrix n n K) index.1 index.2
  let relation : R := determinant - 1
  let prime := RingHom.ker (MvPolynomial.eval identity)
  have hmax : prime.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun k => ⟨MvPolynomial.C k, MvPolynomial.eval_C k⟩)
  have hheight : (prime.height : WithBot ℕ∞) = ringKrullDim R := by
    rw [MvPolynomial.height_ker_eval, dimension_polynomialRing]
    simp [Fintype.card_prod, pow_two]
  have det_identity : MvPolynomial.eval identity determinant = 1 := by
    change (MvPolynomial.eval identity) ((Matrix.mvPolynomialX n n K).det) = 1
    rw [Matrix.eval_det_mvPolynomialX]
    change (1 : Matrix n n K).det = 1
    exact Matrix.det_one
  have hmem : relation ∈ prime := by
    change MvPolynomial.eval identity relation = 0
    simp [relation, det_identity]
  have hne : relation ≠ 0 := by
    have hn : Nonempty n := Fintype.card_pos_iff.mp hpos
    intro h
    have hh := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    have det_zero : MvPolynomial.eval (fun _ : n × n => (0 : K)) determinant = 0 := by
      change (MvPolynomial.eval (fun _ : n × n => (0 : K)))
        ((Matrix.mvPolynomialX n n K).det) = 0
      rw [Matrix.eval_det_mvPolynomialX]
      change (0 : Matrix n n K).det = 0
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
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
        ringKrullDim (SpecialLinearCoordinateRing.PolynomialCoordinateRing K n) :=
      (ringKrullDim_eq_of_ringEquiv
        (SpecialLinearCoordinateRing.polynomialEquiv K n).toRingEquiv).symm
    _ = ringKrullDim (R ⧸ Ideal.span {relation}) := rfl
    _ = _ := hdim

private theorem dimension_sl_empty (hzero : Fintype.card n = 0) :
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  have hn : IsEmpty n := Fintype.card_eq_zero_iff.mp hzero
  let R := GeneralLinearCoordinateRing.PolynomialRing K n
  have hdet : GeneralLinearCoordinateRing.determinant K n - 1 = 0 := by
    simp [GeneralLinearCoordinateRing.determinant, Matrix.det_isEmpty]
  have hideal : SpecialLinearCoordinateRing.polynomialIdeal K n = ⊥ := by
    simp [SpecialLinearCoordinateRing.polynomialIdeal, hdet]
  calc
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
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

/-- The actual determinant-localized coordinate ring has dimension `card(n)²`. -/
theorem generalLinearCoordinateRing_ringKrullDim :
    ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  dimension_gl K n

/-- The actual determinant-one Hopf quotient has dimension `card(n)² - 1`,
with natural subtraction, including the empty index type. -/
theorem specialLinearCoordinateRing_ringKrullDim :
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  by_cases hzero : Fintype.card n = 0
  · exact dimension_sl_empty K n hzero
  · exact dimension_sl_positive K n (Nat.pos_of_ne_zero hzero)

/-- The underlying affine scheme of `GL(n)` has dimension `card(n)²`. -/
theorem generalLinearGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (generalLinearGroupUnderlyingScheme K n).left =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (GeneralLinearCoordinateRing.CoordinateRing K n)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact generalLinearCoordinateRing_ringKrullDim K n

/-- The underlying affine scheme of `SL(n)` has dimension `card(n)² - 1`
with natural subtraction. -/
theorem specialLinearGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (specialLinearGroupUnderlyingScheme K n).left =
      ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (SpecialLinearCoordinateRing.CoordinateRing K n)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact specialLinearCoordinateRing_ringKrullDim K n

end AlgebraicGeometry
