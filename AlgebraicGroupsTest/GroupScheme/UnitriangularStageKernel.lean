/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageKernel
public import Mathlib.Data.ZMod.Basic

/-!
# Clients of the native unitriangular stage kernel

These examples instantiate the underlying over-scheme pullback square at
rank three and at degenerate ranks and bases, including the empty product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

variable (K : Type) [CommRing K]

example : IsPullback (unitriangularStageSuccessor K 3 1).hom.hom
    (toUnit (unitriangularStageScheme K 3 2).toMon.X)
    (unitriangularStageCoordinateMap K 3 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 1 =>
      additiveGroupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 3 1 (by omega)

example {T : Over (Spec (.of K))}
    (first second : T ⟶ (unitriangularStageScheme K 3 2).toMon.X)
    (hsame : first ≫ (unitriangularStageSuccessor K 3 1).hom.hom =
      second ≫ (unitriangularStageSuccessor K 3 1).hom.hom) : first = second := by
  apply (unitriangularStageCoordinateMap_isPullback K 3 1 (by omega)).hom_ext hsame
  exact toUnit_unique _ _

example : IsPullback (unitriangularStageSuccessor K 0 1).hom.hom
    (toUnit (unitriangularStageScheme K 0 2).toMon.X)
    (unitriangularStageCoordinateMap K 0 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 0 1 =>
      additiveGroupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 0 1 (by omega)

example : IsPullback (unitriangularStageSuccessor K 1 1).hom.hom
    (toUnit (unitriangularStageScheme K 1 2).toMon.X)
    (unitriangularStageCoordinateMap K 1 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 1 1 =>
      additiveGroupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 1 1 (by omega)

example : IsPullback (unitriangularStageSuccessor K 3 3).hom.hom
    (toUnit (unitriangularStageScheme K 3 4).toMon.X)
    (unitriangularStageCoordinateMap K 3 3 (by omega)).hom.hom
    η[((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 3 3 =>
      additiveGroupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 3 3 (by omega)

example : IsPullback (unitriangularStageSuccessor (ZMod 1) 0 2).hom.hom
    (toUnit (unitriangularStageScheme (ZMod 1) 0 3).toMon.X)
    (unitriangularStageCoordinateMap (ZMod 1) 0 2 (by omega)).hom.hom
    η[((∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex 0 2 =>
      additiveGroupScheme (ZMod 1)).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback (ZMod 1) 0 2 (by omega)

end AlgebraicGeometry
