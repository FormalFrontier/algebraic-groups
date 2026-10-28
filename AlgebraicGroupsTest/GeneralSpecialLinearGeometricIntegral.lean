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

open AlgebraicGeometry TauCeti.GeneralLinear SpecialLinearCoordinateRing

universe u

namespace AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

example : GeometricallyIntegral ((groupScheme K (Fintype.card n)).X).hom :=
  inferInstance

example : GeometricallyIntegral ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).hom :=
  inferInstance

example [IsDomain K] : IsDomain ((coordinateHopfAlgebra K (Fintype.card n))) :=
  inferInstance

example [IsDomain K] : IsIntegral ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).left :=
  inferInstance

example : IsDomain ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ (Fintype.card (Fin 0)))) :=
  inferInstance

example : IsIntegral ((groupScheme ℤ (Fintype.card (Fin 0))).X).left :=
  inferInstance

example : IsDomain ((coordinateHopfAlgebra ℤ (Fintype.card (Fin 1)))) :=
  inferInstance

example : IsIntegral ((TauCeti.SpecialLinear.groupScheme ℤ (Fintype.card (Fin 1))).X).left :=
  inferInstance

example : IsDomain ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ (Fintype.card (Fin 2)))) :=
  inferInstance

example : IsIntegral ((groupScheme ℤ (Fintype.card (Fin 2))).X).left :=
  inferInstance

example : GeometricallyIntegral
    ((groupScheme (ZMod 1) (Fintype.card (Fin 0))).X).hom :=
  inferInstance

example : GeometricallyIntegral
    ((TauCeti.SpecialLinear.groupScheme (ZMod 1) (Fintype.card (Fin 2))).X).hom :=
  inferInstance

end AlgebraicGroupsTest.GeneralSpecialLinearGeometricIntegral
