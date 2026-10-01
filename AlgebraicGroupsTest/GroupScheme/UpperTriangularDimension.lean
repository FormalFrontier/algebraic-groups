/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularDimension
public import Mathlib.Algebra.Field.ZMod

/-!
# Ordinary clients of the finite upper-triangular presentation and dimension

These independent imports exercise the native quotient over arbitrary bases,
including the zero ring and empty index type, and concrete finite- and
infinite-field dimensions. No private producer declarations are used.
-/

public section

set_option warningAsError true

noncomputable section

open UpperTriangularCoordinateRing GeneralLinearCoordinateRing

universe u

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι] :
    UpperTriangularCoordinateRing.CoordinateRing K ι ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        (determinant K ι)) :=
  localizedPolynomialEquiv K ι

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]
    (i j : ι) (hji : ¬ j < i) :
    localizedPolynomialEquiv K ι (quotient K ι (matrix K ι i j)) =
      algebraMap (MvPolynomial (retainedIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
          (determinant K ι)))
        (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩) :=
  localizedPolynomialEquiv_entry K ι i j hji

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]
    (i j : ι) (hji : ¬ j < i) :
    (localizedPolynomialEquiv K ι).symm
      (algebraMap (MvPolynomial (retainedIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
          (determinant K ι)))
        (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩)) =
      quotient K ι (matrix K ι i j) :=
  localizedPolynomialEquiv_symm_entry K ι i j hji

example : UpperTriangularCoordinateRing.CoordinateRing (ZMod 1) (Fin 0) ≃ₐ[ZMod 1]
    Localization.Away (MvPolynomial.eraseCoordinates (ZMod 1)
      (retainedIndices (Fin 0)) (determinant (ZMod 1) (Fin 0))) :=
  localizedPolynomialEquiv (ZMod 1) (Fin 0)

example : UpperTriangularCoordinateRing.CoordinateRing ℤ (Fin 0) ≃ₐ[ℤ]
    Localization.Away (MvPolynomial.eraseCoordinates ℤ
      (retainedIndices (Fin 0)) (determinant ℤ (Fin 0))) :=
  localizedPolynomialEquiv ℤ (Fin 0)

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι] :
    MvPolynomial.eval
      (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
      (MvPolynomial.eraseCoordinates K (retainedIndices ι) (determinant K ι)) = 1 :=
  erasedDeterminant_eval_one K ι

example : ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing (ZMod 2) (Fin 0)) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) (Fin 0)

example : ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing (ZMod 2) (Fin 1)) =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) (Fin 1)

example : ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing (ZMod 2) (Fin 2)) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example : ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing ℚ (Fin 2)) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim ℚ (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.upperTriangularGroupUnderlyingScheme (ZMod 2) (Fin 2)).left =
      (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularGroupUnderlyingScheme_topologicalKrullDim
    (ZMod 2) (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.upperTriangularGroupUnderlyingScheme ℚ (Fin 0)).left =
      (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularGroupUnderlyingScheme_topologicalKrullDim
    ℚ (Fin 0)
