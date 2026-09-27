/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth
public import Mathlib.Data.ZMod.Basic

/-!
# Public-client checks for finite GL and SL smoothness

The tests use only the public smoothness leaf: arbitrary commutative base rings,
empty/rank-one/rank-two index sets, zero rings, native affine structure morphisms,
finite presentations, normalization entry evaluation and the quotient retraction.
These original checks are provided under Apache-2.0.
-/

public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

universe u

namespace AlgebraicGroupsTest.GeneralSpecialLinearSmooth

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

example : Algebra.FinitePresentation K
    (GeneralLinearCoordinateRing.CoordinateRing K n) := inferInstance

example : Algebra.FinitePresentation K
    (SpecialLinearCoordinateRing.CoordinateRing K n) := inferInstance

example : Algebra.Smooth K
    (GeneralLinearCoordinateRing.CoordinateRing K n) := inferInstance

example : Algebra.Smooth K
    (SpecialLinearCoordinateRing.CoordinateRing K n) := inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme K n).hom := inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme K n).hom := inferInstance

variable (pivot : n)

example : (SpecialLinearCoordinateRing.quotient K n).comp
      (AlgebraicGeometry.specialLinearNormalizationSection K n pivot) =
      AlgHom.id K (SpecialLinearCoordinateRing.CoordinateRing K n) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient K n pivot

example (i j : n) :
    AlgebraicGeometry.specialLinearNormalizationSection K n pivot
        (SpecialLinearCoordinateRing.entry K n i j) =
      (AlgebraicGeometry.specialLinearNormalization K n pivot : Matrix n n
        (GeneralLinearCoordinateRing.CoordinateRing K n)) i j :=
  AlgebraicGeometry.specialLinearNormalizationSection_entry K n pivot i j

example (i j : n) :
    (SpecialLinearCoordinateRing.quotient K n)
        (AlgebraicGeometry.specialLinearNormalizationSection K n pivot
          (SpecialLinearCoordinateRing.entry K n i j)) =
      SpecialLinearCoordinateRing.entry K n i j := by
  have retraction := AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient
    K n pivot
  have readback := congrArg
    (fun f : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K]
        SpecialLinearCoordinateRing.CoordinateRing K n ↦
      f (SpecialLinearCoordinateRing.entry K n i j)) retraction
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using readback

example : Algebra.Smooth ℤ (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 0)) :=
  inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme ℤ (Fin 0)).hom :=
  inferInstance

example : Algebra.Smooth ℤ (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 1)) :=
  inferInstance

example : Algebra.Smooth ℤ (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 2)) :=
  inferInstance

example : (SpecialLinearCoordinateRing.quotient ℤ (Fin 1)).comp
      (AlgebraicGeometry.specialLinearNormalizationSection ℤ (Fin 1) 0) =
      AlgHom.id ℤ (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 1)) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient ℤ (Fin 1) 0

example : (SpecialLinearCoordinateRing.quotient ℤ (Fin 2)).comp
      (AlgebraicGeometry.specialLinearNormalizationSection ℤ (Fin 2) 1) =
      AlgHom.id ℤ (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 2)) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient ℤ (Fin 2) 1

example : Algebra.Smooth (ZMod 1)
    (GeneralLinearCoordinateRing.CoordinateRing (ZMod 1) (Fin 0)) := inferInstance

example : Algebra.Smooth (ZMod 1)
    (SpecialLinearCoordinateRing.CoordinateRing (ZMod 1) (Fin 0)) := inferInstance

example : Algebra.Smooth (ZMod 1)
    (SpecialLinearCoordinateRing.CoordinateRing (ZMod 1) (Fin 2)) := inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme (ZMod 1) (Fin 1)).hom :=
  inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom :=
  inferInstance

example : AlgebraicGeometry.Smooth
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme (ZMod 1) (Fin 2)).hom :=
  inferInstance

end AlgebraicGroupsTest.GeneralSpecialLinearSmooth
