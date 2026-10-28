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

open TauCeti.GeneralLinear.UpperTriangular

universe u

example (K : Type u) [CommRing K] (n : ℕ) :
    coordinateHopfAlgebra K n ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
        (Matrix.mvPolynomialX (Fin n) (Fin n) K).det) :=
  localizedPolynomialEquiv K n

example (K : Type u) [CommRing K] (n : ℕ)
    (i j : Fin n) (hji : ¬ j < i) :
    localizedPolynomialEquiv K n
      ((coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i j)) =
      algebraMap (MvPolynomial (retainedIndices (Fin n)) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
          (Matrix.mvPolynomialX (Fin n) (Fin n) K).det))
        (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩) :=
  localizedPolynomialEquiv_entry K n i j hji

example (K : Type u) [CommRing K] (n : ℕ)
    (i j : Fin n) (hji : ¬ j < i) :
    (localizedPolynomialEquiv K n).symm
      (algebraMap (MvPolynomial (retainedIndices (Fin n)) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
          (Matrix.mvPolynomialX (Fin n) (Fin n) K).det))
        (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩)) =
      (coordinateMap K n).hom (TauCeti.GeneralLinear.genericMatrix K n i j) :=
  localizedPolynomialEquiv_symm_entry K n i j hji

example : coordinateHopfAlgebra (ZMod 1) 0 ≃ₐ[ZMod 1]
    Localization.Away (MvPolynomial.eraseCoordinates (ZMod 1)
      (retainedIndices (Fin 0)) (Matrix.mvPolynomialX (Fin 0) (Fin 0) (ZMod 1)).det) :=
  localizedPolynomialEquiv (ZMod 1) 0

example : coordinateHopfAlgebra ℤ 0 ≃ₐ[ℤ]
    Localization.Away (MvPolynomial.eraseCoordinates ℤ
      (retainedIndices (Fin 0)) (Matrix.mvPolynomialX (Fin 0) (Fin 0) ℤ).det) :=
  localizedPolynomialEquiv ℤ 0

example (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι] :
    MvPolynomial.eval
      (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
      (MvPolynomial.eraseCoordinates K (retainedIndices ι) (Matrix.mvPolynomialX ι ι K).det) = 1 :=
  erasedDeterminant_eval_one K ι

example : ringKrullDim (coordinateHopfAlgebra (ZMod 2) 0) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) 0

example : ringKrullDim (coordinateHopfAlgebra (ZMod 2) 1) =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) 1

example : ringKrullDim (coordinateHopfAlgebra (ZMod 2) 2) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim (ZMod 2) 2

example : ringKrullDim (coordinateHopfAlgebra ℚ 2) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim ℚ 2

example : topologicalKrullDim
    (groupScheme (ZMod 2) 2).X.left =
      (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularGroupUnderlyingScheme_topologicalKrullDim
    (ZMod 2) 2

example : topologicalKrullDim
    (groupScheme ℚ 0).X.left =
      (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.upperTriangularGroupUnderlyingScheme_topologicalKrullDim
    ℚ 0
