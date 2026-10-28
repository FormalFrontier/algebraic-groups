/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.DiagonalDimension
public import Mathlib.Algebra.Field.ZMod

/-!
# Clients of the canonical split-torus presentation and dimension

These statements exercise arbitrary commutative bases, a zero ring, finite
fields and the empty, singleton and two-element matrix index types.
-/

public section

set_option warningAsError true

noncomputable section

open TauCeti.SplitTorus

universe u

example (K : Type u) [CommRing K] (ι : Type u) [Finite ι] :
    MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) ≃ₐ[K]
      Localization.Away (polynomialDenominator K ι) :=
  polynomialLocalizationEquiv K ι

example (K : Type u) [CommRing K] (ι : Type u) [Finite ι] (i : ι) :
    polynomialLocalizationEquiv K ι
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : K)) =
      algebraMap (MvPolynomial ι K) (Localization.Away (polynomialDenominator K ι))
        (MvPolynomial.X i) :=
  polynomialLocalizationEquiv_variable K ι i

example (K : Type u) [CommRing K] (ι : Type u) [Finite ι] (i : ι) :
    (polynomialLocalizationEquiv K ι).symm
      (algebraMap (MvPolynomial ι K) (Localization.Away (polynomialDenominator K ι))
        (MvPolynomial.X i)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : K) :=
  polynomialLocalizationEquiv_symm_variable K ι i

example : MonoidAlgebra (ZMod 1) (Multiplicative (Fin 0 →₀ ℤ)) ≃ₐ[ZMod 1]
    Localization.Away (polynomialDenominator (ZMod 1) (Fin 0)) :=
  polynomialLocalizationEquiv (ZMod 1) (Fin 0)

example (K : Type u) [Field K] (ι : Type u) [Fintype ι] :
    ringKrullDim (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  simpa only [Nat.card_eq_fintype_card] using ringKrullDim_coordinateRing K ι

example : ringKrullDim (MonoidAlgebra (ZMod 2) (Multiplicative (Fin 0 →₀ ℤ))) =
    (0 : WithBot ℕ∞) := by
  simpa using ringKrullDim_coordinateRing (ZMod 2) (Fin 0)

example : ringKrullDim (MonoidAlgebra (ZMod 2) (Multiplicative (Fin 1 →₀ ℤ))) =
    (1 : WithBot ℕ∞) := by
  simpa using ringKrullDim_coordinateRing (ZMod 2) (Fin 1)

example : ringKrullDim (MonoidAlgebra (ZMod 2) (Multiplicative (Fin 2 →₀ ℤ))) =
    (2 : WithBot ℕ∞) := by
  simpa using ringKrullDim_coordinateRing (ZMod 2) (Fin 2)

example (K : Type u) [Field K] (ι : Type u) [Fintype ι] :
    topologicalKrullDim (groupScheme K ι).X.left =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  simpa only [Nat.card_eq_fintype_card] using topologicalKrullDim_groupScheme K ι
