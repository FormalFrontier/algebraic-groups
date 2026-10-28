/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.RingTheory.KrullDimension.FiniteType
public import Mathlib.Algebra.Field.ZMod

/-!
# Clients of finite polynomial localization dimension

Examples exercise the empty-variable case, a singleton, a positive-rank
multivariate polynomial, and a finite coefficient field.
-/

public section

set_option warningAsError true

open MvPolynomial

example (K : Type*) [Field K] (_a : Fin 0 → K) :
    ringKrullDim (Localization.Away (MvPolynomial.C (1 : K) : MvPolynomial (Fin 0) K)) =
      (0 : WithBot ℕ∞) := by
  rw [TauCeti.ringKrullDim_localization_away K (by simp),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

example (K : Type*) [Field K] :
    ringKrullDim (Localization.Away (MvPolynomial.X 0 + MvPolynomial.C 1 :
      MvPolynomial (Fin 1) K)) = (1 : WithBot ℕ∞) := by
  have hf : (MvPolynomial.X 0 + MvPolynomial.C 1 : MvPolynomial (Fin 1) K) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    simp at this
  rw [TauCeti.ringKrullDim_localization_away K hf,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

example : ringKrullDim (Localization.Away (MvPolynomial.X 0 + MvPolynomial.C 1 :
    MvPolynomial (Fin 1) (ZMod 2))) = (1 : WithBot ℕ∞) := by
  have hf : (MvPolynomial.X 0 + MvPolynomial.C 1 : MvPolynomial (Fin 1) (ZMod 2)) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (fun _ => (0 : ZMod 2))) h
    simp at this
  rw [TauCeti.ringKrullDim_localization_away (ZMod 2) hf,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

example (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) (a : Fin 2 → K)
    (ha : eval a f ≠ 0) :
    ringKrullDim (Localization.Away f) = (2 : WithBot ℕ∞) := by
  have hf : f ≠ 0 := fun h => ha (by simp [h])
  rw [TauCeti.ringKrullDim_localization_away K hf,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp
