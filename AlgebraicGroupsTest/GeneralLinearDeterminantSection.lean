/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection
public import Mathlib.Data.ZMod.Basic

/-!
# External-client checks for the GL determinant section

The tests import the public module alone and exercise arbitrary-base, nonidentity
units in ranks one and two, a zero coefficient ring, coefficient changes, native
scheme-point readbacks, and the section law for arbitrary (not only affine) tests.
-/

public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]
    (pivot : n)

example : CategoryTheory.SplitEpi (generalLinearDeterminantSchemeHom K n) :=
  generalLinearDeterminantSplitEpi K n pivot

example (T : Over (Spec (.of K)))
    (point : T ⟶ multiplicativeGroupUnderlyingScheme K) :
    (point ≫ (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom = point :=
  generalLinearDeterminantSection_testScheme K n pivot T point

example (R : Type u) [CommRing R] [Algebra K R] (unit : Rˣ) :
    multiplicativeGroupMulEquivPoints K R unit ≫
      (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom =
    generalLinearGroupMulEquivPoints K n R (generalLinearDiagonalHom n pivot unit) :=
  generalLinearDeterminantSection_point K n R pivot unit

example (R : Type u) [CommRing R] [Algebra K R] (unit : Rˣ) (i j : n) :
    (Spec.preimage (multiplicativeGroupMulEquivPoints K R unit ≫
      (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom).left).hom
      (matrix K n i j) =
    if i = j then (if i = pivot then (unit : R) else 1) else 0 := by
  rw [generalLinearDeterminantSection_point K n R pivot unit,
    generalLinearGroupPoint_preimage_entry]
  exact generalLinearDiagonalHom_apply n pivot unit i j

example (R S : Type u) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (unit : Rˣ) :
    Matrix.GeneralLinearGroup.map f.toRingHom (generalLinearDiagonalHom n pivot unit) =
      generalLinearDiagonalHom n pivot (Units.map f unit) :=
  generalLinearDiagonalHom_natural n pivot f.toRingHom unit

example : Matrix.GeneralLinearGroup.det
    (generalLinearDiagonalHom (Fin 1) 0 (-1 : ℤˣ)) = -1 := by
  exact generalLinearDiagonalHom_det (Fin 1) 0 (-1 : ℤˣ)

example : Matrix.GeneralLinearGroup.det
    (generalLinearDiagonalHom (Fin 2) 1 (-1 : ℤˣ)) = -1 := by
  exact generalLinearDiagonalHom_det (Fin 2) 1 (-1 : ℤˣ)

example : (generalLinearDiagonalHom (Fin 2) 1 (-1 : ℤˣ)) (0 : Fin 2) 0 = 1 := by
  simp

example : (generalLinearDiagonalHom (Fin 2) 1 (-1 : ℤˣ)) (1 : Fin 2) 1 = -1 := by
  simp

example : (generalLinearDiagonalHom (Fin 2) 1 (-1 : ℤˣ)) (0 : Fin 2) 1 = 0 := by
  simp

example : Matrix.GeneralLinearGroup.det
    (generalLinearDiagonalHom (Fin 2) 0 (1 : (ZMod 1)ˣ)) = 1 := by
  exact generalLinearDiagonalHom_det (Fin 2) 0 (1 : (ZMod 1)ˣ)

example (T : Over (Spec (.of (ZMod 1))))
    (point : T ⟶ multiplicativeGroupUnderlyingScheme (ZMod 1)) :
    (point ≫ (generalLinearDeterminantSectionSchemeHom (ZMod 1) (Fin 1) 0).hom.hom) ≫
      (generalLinearDeterminantSchemeHom (ZMod 1) (Fin 1)).hom.hom = point :=
  generalLinearDeterminantSection_testScheme (ZMod 1) (Fin 1) 0 T point

example : (Spec.preimage
    (generalLinearDeterminantSectionSchemeHom (ZMod 1) (Fin 1) 0).hom.hom.left).hom
      (matrix (ZMod 1) (Fin 1) 0 0) =
    multiplicativeGroupCoordinate (ZMod 1) := by
  simpa using generalLinearDeterminantSection_preimage_entry (ZMod 1) (Fin 1) 0 0 0

example (i j : n) :
    (Spec.preimage (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (matrix K n i j) =
      if i = j then (if i = pivot then multiplicativeGroupCoordinate K else 1) else 0 :=
  generalLinearDeterminantSection_preimage_entry K n pivot i j

example : (Spec.preimage
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (detInverse K n) = LaurentPolynomial.T (-1) :=
  generalLinearDeterminantSection_preimage_detInverse K n pivot

end AlgebraicGeometry

#lint
