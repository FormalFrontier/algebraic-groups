/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients
import Mathlib.Data.ZMod.Basic

/-!
# Import-only checks for successive unitriangular superdiagonals

These examples use only the public producer API, including empty dimensions,
empty superdiagonals, arbitrary commutative rings and noninjective coefficient maps.
The coordinate theorem intentionally requires `1 ≤ r`.
-/

namespace AlgebraicGroupsTest.UnitriangularSuperdiagonalQuotients

open Matrix.UnitriangularGroup

private theorem coordinate_evaluation (n r : ℕ) (R : Type) [CommRing R]
    (hr : 1 ≤ r) (x : superdiagonalSubgroup n R r)
    (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr x) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 :=
  superdiagonalCoordinateHom_apply n R r hr x ij

private theorem exact_kernel (n r : ℕ) (R : Type) [CommRing R] (hr : 1 ≤ r) :
    (superdiagonalCoordinateHom n R r hr).ker =
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r) :=
  superdiagonalCoordinateHom_ker n R r hr

private theorem normal_kernel (n r : ℕ) (R : Type) [CommRing R] :
    ((superdiagonalSubgroup n R (r + 1)).subgroupOf
      (superdiagonalSubgroup n R r)).Normal := inferInstance

private theorem every_coordinate_has_lift (n r : ℕ) (R : Type) [CommRing R]
    (hr : 1 ≤ r) (a : Multiplicative (superdiagonalIndex n r → R)) :
    ∃ x : superdiagonalSubgroup n R r,
      superdiagonalCoordinateHom n R r hr x = a :=
  superdiagonalCoordinateHom_surjective n R r hr a

private theorem quotient_evaluation (n r : ℕ) (R : Type) [CommRing R]
    (hr : 1 ≤ r) (x : superdiagonalSubgroup n R r)
    (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd
        (superdiagonalQuotientEquiv n R r hr
          (x : superdiagonalSubgroup n R r ⧸
            (superdiagonalSubgroup n R (r + 1)).subgroupOf
              (superdiagonalSubgroup n R r))) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 :=
  superdiagonalQuotientEquiv_mk n R r hr x ij

private theorem arbitrary_ring_map_square (n r : ℕ) (R S : Type)
    [CommRing R] [CommRing S] (f : R →+* S) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r ⧸
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r)) :
    superdiagonalQuotientEquiv n S r hr (superdiagonalQuotientMap n R f r x) =
      superdiagonalCoordinateMap n R f r
        (superdiagonalQuotientEquiv n R r hr x) :=
  superdiagonalQuotientEquiv_natural n R f r hr x

private theorem empty_dimension (R : Type) [CommRing R] :
    Function.Surjective (superdiagonalCoordinateHom 0 R 1 (by omega)) :=
  superdiagonalCoordinateHom_surjective 0 R 1 (by omega)

private theorem singleton_dimension (R : Type) [CommRing R] :
    Function.Surjective (superdiagonalCoordinateHom 1 R 1 (by omega)) :=
  superdiagonalCoordinateHom_surjective 1 R 1 (by omega)

private theorem empty_superdiagonal (R : Type) [CommRing R] :
    Function.Surjective (superdiagonalCoordinateHom 3 R 5 (by omega)) :=
  superdiagonalCoordinateHom_surjective 3 R 5 (by omega)

private theorem zero_ring :
    Function.Surjective (superdiagonalCoordinateHom 2 (ZMod 1) 1 (by omega)) :=
  superdiagonalCoordinateHom_surjective 2 (ZMod 1) 1 (by omega)

private theorem characteristic_two :
    Function.Surjective (superdiagonalCoordinateHom 3 (ZMod 2) 2 (by omega)) :=
  superdiagonalCoordinateHom_surjective 3 (ZMod 2) 2 (by omega)

private theorem nonreduced :
    Function.Surjective (superdiagonalCoordinateHom 3 (ZMod 4) 1 (by omega)) :=
  superdiagonalCoordinateHom_surjective 3 (ZMod 4) 1 (by omega)

private theorem nonreduced_to_characteristic_two
    (f : ZMod 4 →+* ZMod 2)
    (x : superdiagonalSubgroup 3 (ZMod 4) 1 ⧸
      (superdiagonalSubgroup 3 (ZMod 4) 2).subgroupOf
        (superdiagonalSubgroup 3 (ZMod 4) 1)) :
    superdiagonalQuotientEquiv 3 (ZMod 2) 1 (by omega)
        (superdiagonalQuotientMap 3 (ZMod 4) f 1 x) =
      superdiagonalCoordinateMap 3 (ZMod 4) f 1
        (superdiagonalQuotientEquiv 3 (ZMod 4) 1 (by omega) x) :=
  superdiagonalQuotientEquiv_natural 3 (ZMod 4) f 1 (by omega) x

end AlgebraicGroupsTest.UnitriangularSuperdiagonalQuotients
