/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.LocalizedCoordinateQuotient

@[expose] public section

set_option warningAsError true

noncomputable section

namespace LocalizedCoordinateQuotientClient

open MvPolynomial

private def selected : Set (Fin 2) := {0}

example : eraseCoordinates ℤ selected (X 0) = X ⟨0, by simp [selected]⟩ := by
  exact eraseCoordinates_X_mem ℤ selected 0 (by simp [selected])

example : eraseCoordinates ℤ selected (X 1) = 0 := by
  exact eraseCoordinates_X_not_mem ℤ selected 1 (by simp [selected])

example (f : MvPolynomial (Fin 2) ℤ) :
    localizedCoordinateQuotientEquiv ℤ selected f
        ((Ideal.Quotient.mkₐ ℤ (localizedCoordinateIdeal ℤ selected f))
          (algebraMap (MvPolynomial (Fin 2) ℤ) (Localization.Away f) (X 0))) =
      algebraMap (MvPolynomial selected ℤ)
        (Localization.Away (eraseCoordinates ℤ selected f)) (X ⟨0, by simp [selected]⟩) := by
  exact localizedCoordinateQuotientEquiv_coordinate ℤ selected f 0 (by simp [selected])

example (f : MvPolynomial (Fin 2) ℤ) :
    (localizedCoordinateQuotientEquiv ℤ selected f).symm
        (algebraMap (MvPolynomial selected ℤ)
          (Localization.Away (eraseCoordinates ℤ selected f)) (X ⟨0, by simp [selected]⟩)) =
      (Ideal.Quotient.mkₐ ℤ (localizedCoordinateIdeal ℤ selected f))
        (algebraMap (MvPolynomial (Fin 2) ℤ) (Localization.Away f) (X 0)) := by
  exact localizedCoordinateQuotientEquiv_symm_coordinate ℤ selected f ⟨0, by simp [selected]⟩

example (f : MvPolynomial (Fin 2) ℤ) :
    (Ideal.Quotient.mkₐ ℤ (localizedCoordinateIdeal ℤ selected f))
      (algebraMap (MvPolynomial (Fin 2) ℤ) (Localization.Away f) (X 1)) = 0 := by
  exact quotient_killed ℤ selected f 1 (by simp [selected])

example : eraseCoordinates ℤ selected (X 1 : MvPolynomial (Fin 2) ℤ) = 0 := by
  exact eraseCoordinates_X_not_mem ℤ selected 1 (by simp [selected])

example :
    (Localization.Away (X 1 : MvPolynomial (Fin 2) ℤ) ⧸
        localizedCoordinateIdeal ℤ selected (X 1)) ≃ₐ[ℤ]
      Localization.Away (0 : MvPolynomial selected ℤ) := by
  rw [← eraseCoordinates_X_not_mem ℤ selected 1 (by simp [selected])]
  exact localizedCoordinateQuotientEquiv ℤ selected (X 1)

example (f : MvPolynomial (Fin 2) ℤ) :
    (Localization.Away f ⧸ localizedCoordinateIdeal ℤ (Set.univ : Set (Fin 2)) f) ≃ₐ[ℤ]
      Localization.Away (eraseCoordinates ℤ Set.univ f) :=
  localizedCoordinateQuotientEquiv ℤ Set.univ f

example (f : MvPolynomial (Fin 2) ℤ) :
    (Localization.Away f ⧸ localizedCoordinateIdeal ℤ (∅ : Set (Fin 2)) f) ≃ₐ[ℤ]
      Localization.Away (eraseCoordinates ℤ ∅ f) :=
  localizedCoordinateQuotientEquiv ℤ ∅ f

example : eraseCoordinates ℤ (∅ : Set (Fin 2)) (X 0) = 0 := by
  exact eraseCoordinates_X_not_mem ℤ ∅ 0 (by simp)

example :
    (Localization.Away (C (2 : ℤ) : MvPolynomial Empty ℤ) ⧸
        localizedCoordinateIdeal ℤ (Set.univ : Set Empty) (C 2)) ≃ₐ[ℤ]
      Localization.Away (eraseCoordinates ℤ Set.univ (C 2 : MvPolynomial Empty ℤ)) :=
  localizedCoordinateQuotientEquiv ℤ Set.univ (C 2)

end LocalizedCoordinateQuotientClient
