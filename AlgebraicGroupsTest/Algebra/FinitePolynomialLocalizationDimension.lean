/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension
public import Mathlib.Algebra.Field.ZMod

/-!
# Clients of finite polynomial localization dimension

Examples exercise the empty-variable case, a singleton, a positive-rank
multivariate polynomial, and a finite coefficient field.
-/

public section

set_option warningAsError true

open MvPolynomial

example (K : Type*) [Field K] (a : Fin 0 → K) :
    ringKrullDim (Localization.Away (MvPolynomial.C (1 : K) : MvPolynomial (Fin 0) K)) =
      (0 : WithBot ℕ∞) := by
  simpa only [Fintype.card_fin, Nat.cast_zero] using
    MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero
    K (Fin 0) (MvPolynomial.C (1 : K)) a (by simp)

example (K : Type*) [Field K] :
    ringKrullDim (Localization.Away (MvPolynomial.X 0 + MvPolynomial.C 1 :
      MvPolynomial (Fin 1) K)) = (1 : WithBot ℕ∞) := by
  simpa only [Fintype.card_fin, Nat.cast_one] using
    MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero K (Fin 1)
      (MvPolynomial.X 0 + MvPolynomial.C 1) (fun _ => (0 : K)) (by simp)

example : ringKrullDim (Localization.Away (MvPolynomial.X 0 + MvPolynomial.C 1 :
    MvPolynomial (Fin 1) (ZMod 2))) = (1 : WithBot ℕ∞) := by
  simpa only [Fintype.card_fin, Nat.cast_one] using
    MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero (ZMod 2)
    (Fin 1) (MvPolynomial.X 0 + MvPolynomial.C 1) (fun _ => 0) (by simp)

example (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) (a : Fin 2 → K)
    (ha : eval a f ≠ 0) :
    ringKrullDim (Localization.Away f) = (2 : WithBot ℕ∞) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero K (Fin 2) f a ha
