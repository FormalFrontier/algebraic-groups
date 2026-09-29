/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.DiagonalDimension
public import Mathlib.Algebra.Field.ZMod

/-!
# Clients of the native finite diagonal presentation and dimension

These statements exercise arbitrary commutative bases, a zero ring, finite
fields and the empty, singleton and two-element matrix index types.
-/

public section

set_option warningAsError true

noncomputable section

open DiagonalCoordinateRing GeneralLinearCoordinateRing

universe u

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [DecidableEq ι] :
    DiagonalCoordinateRing.CoordinateRing K ι ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) :=
  localizedPolynomialEquiv K ι

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [DecidableEq ι] (i : ι) :
    localizedPolynomialEquiv K ι (quotient K ι (matrix K ι i i)) =
      algebraMap (MvPolynomial (diagonalIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
          (determinant K ι))) (MvPolynomial.X ⟨(i, i), rfl⟩) :=
  localizedPolynomialEquiv_diagonal K ι i

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [DecidableEq ι] (i : ι) :
    (localizedPolynomialEquiv K ι).symm
      (algebraMap (MvPolynomial (diagonalIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
          (determinant K ι))) (MvPolynomial.X ⟨(i, i), rfl⟩)) =
        quotient K ι (matrix K ι i i) :=
  localizedPolynomialEquiv_symm_diagonal K ι i

example : DiagonalCoordinateRing.CoordinateRing (ZMod 1) (Fin 0) ≃ₐ[ZMod 1]
    Localization.Away (MvPolynomial.eraseCoordinates (ZMod 1)
      (diagonalIndices (Fin 0)) (determinant (ZMod 1) (Fin 0))) :=
  localizedPolynomialEquiv (ZMod 1) (Fin 0)

example (K : Type u) [Field K] (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ringKrullDim (DiagonalCoordinateRing.CoordinateRing K ι) =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.diagonalCoordinateRing_ringKrullDim K ι

example : ringKrullDim (DiagonalCoordinateRing.CoordinateRing (ZMod 2) (Fin 0)) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.diagonalCoordinateRing_ringKrullDim (ZMod 2) (Fin 0)

example : ringKrullDim (DiagonalCoordinateRing.CoordinateRing (ZMod 2) (Fin 1)) =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.diagonalCoordinateRing_ringKrullDim (ZMod 2) (Fin 1)

example : ringKrullDim (DiagonalCoordinateRing.CoordinateRing (ZMod 2) (Fin 2)) =
    (2 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.diagonalCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example (K : Type u) [Field K] (ι : Type u) [Fintype ι] [DecidableEq ι] :
    topologicalKrullDim (AlgebraicGeometry.diagonalGroupUnderlyingScheme K ι).left =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.diagonalGroupUnderlyingScheme_topologicalKrullDim K ι
