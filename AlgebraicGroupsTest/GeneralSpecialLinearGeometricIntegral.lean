/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral
public import Mathlib.Data.ZMod.Basic

/-!
# Ordinary-import clients for finite GL and SL integrality

The generic clients exercise the actual structure morphisms without imposing
field or domain assumptions on the base. Concrete clients check domains and
integral total spaces over the nonfield domain `ℤ`, including rank zero.
-/

public section

set_option warningAsError true

open AlgebraicGeometry GeneralLinearCoordinateRing SpecialLinearCoordinateRing

universe u

namespace AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

example : GeometricallyIntegral (generalLinearGroupUnderlyingScheme K n).hom :=
  inferInstance

example : GeometricallyIntegral (specialLinearGroupUnderlyingScheme K n).hom :=
  inferInstance

example [IsDomain K] : IsDomain (GeneralLinearCoordinateRing.CoordinateRing K n) :=
  inferInstance

example [IsDomain K] : IsIntegral (specialLinearGroupUnderlyingScheme K n).left :=
  inferInstance

example : IsDomain (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 0)) :=
  inferInstance

example : IsIntegral (generalLinearGroupUnderlyingScheme ℤ (Fin 0)).left :=
  inferInstance

example : IsDomain (GeneralLinearCoordinateRing.CoordinateRing ℤ (Fin 1)) :=
  inferInstance

example : IsIntegral (specialLinearGroupUnderlyingScheme ℤ (Fin 1)).left :=
  inferInstance

example : IsDomain (SpecialLinearCoordinateRing.CoordinateRing ℤ (Fin 2)) :=
  inferInstance

example : IsIntegral (generalLinearGroupUnderlyingScheme ℤ (Fin 2)).left :=
  inferInstance

example : GeometricallyIntegral
    (generalLinearGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom :=
  inferInstance

example : GeometricallyIntegral
    (specialLinearGroupUnderlyingScheme (ZMod 1) (Fin 2)).hom :=
  inferInstance

end AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral
