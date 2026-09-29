/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.PolynomialRationalPointHeight
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Data.ENat.Monoid

/-!
# Dimension of a polynomial localization with a rational point

The localization of a finite-variable polynomial ring over a field at `f` has the
same Krull dimension as the polynomial ring whenever a rational evaluation does
not vanish on `f`. The stated witness works without an infinite-field hypothesis,
even when the variable type is empty.
-/

public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

/-- A principal open in finite-dimensional affine space containing a rational point
has the full Krull dimension of affine space. -/
theorem ringKrullDim_localizationAway_of_eval_ne_zero
    (K : Type u) [Field K] (σ : Type v) [Fintype σ]
    (f : MvPolynomial σ K) (a : σ → K) (ha : eval a f ≠ 0) :
    ringKrullDim (Localization.Away f) =
      ((Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  let R := MvPolynomial σ K
  let q : Polynomial R := Polynomial.C f * Polynomial.X - 1
  let evaluation := Polynomial.eval₂RingHom (eval a) (eval a f)⁻¹
  let prime := RingHom.ker evaluation
  have hmax : prime.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _
      (fun k => ⟨Polynomial.C (MvPolynomial.C k), by simp [evaluation]⟩)
  have hover : prime.LiesOver (RingHom.ker (eval a)) := by
    constructor
    ext p
    simp [prime, evaluation, Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker]
  have hheight : (prime.height : WithBot ℕ∞) = ringKrullDim (Polynomial R) := by
    have h : prime.height = (RingHom.ker (eval a)).height + 1 :=
      @Polynomial.height_eq_height_add_one _ _ _ _ _ hmax hover
    rw [h, MvPolynomial.height_ker_eval,
      Polynomial.ringKrullDim_of_isNoetherianRing,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
    simp [Nat.card_eq_fintype_card]
  have hmem : q ∈ prime := by
    change evaluation q = 0
    simp [q, evaluation, ha]
  have hne : q ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval₂ (eval a) (0 : K)) h
    simp [q, Polynomial.eval₂_sub] at hh
  have hreg : q ∈ nonZeroDivisors (Polynomial R) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hne
  have hquot : ringKrullDim (Polynomial R ⧸ Ideal.span {q}) + 1 =
      ringKrullDim (Polynomial R) := by
    exact @Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      _ _ _ _ hreg _ hmax.isPrime hheight hmem
  have hdim : ringKrullDim (Polynomial R ⧸ Ideal.span {q}) =
      ((Fintype.card σ : ℕ) : WithBot ℕ∞) := by
    apply (ENat.WithBot.add_one_cancel).mp
    rw [hquot, Polynomial.ringKrullDim_of_isNoetherianRing,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
    simp [Nat.card_eq_fintype_card]
  calc
    ringKrullDim (Localization.Away f) = ringKrullDim (AdjoinRoot q) :=
      ringKrullDim_eq_of_ringEquiv (Localization.awayEquivAdjoin f).toRingEquiv
    _ = ringKrullDim (Polynomial R ⧸ Ideal.span {q}) := rfl
    _ = _ := hdim

end MvPolynomial
