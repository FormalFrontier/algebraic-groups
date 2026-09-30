/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.FiniteTriangularGeometry
public import Mathlib.Data.ZMod.Basic

/-! # Ordinary clients of native finite triangular geometry

The examples apply the instances to actual structure morphisms, including the
zero ring, a reducible base, and empty, singleton, and nontrivial finite orders.
-/

@[expose] public section

set_option warningAsError true

open AlgebraicGeometry

universe u

namespace AlgebraicGroupsTest.GroupScheme.FiniteTriangularGeometry

variable (K : Type u) [CommRing K] (index : Type u) [Fintype index]
  [DecidableEq index]

example : Smooth (multiplicativeGroupUnderlyingScheme K).hom := inferInstance
example : GeometricallyIntegral (multiplicativeGroupUnderlyingScheme K).hom := inferInstance
example : Smooth (diagonalGroupUnderlyingScheme K index).hom := inferInstance
example : GeometricallyIntegral (diagonalGroupUnderlyingScheme K index).hom := inferInstance

variable (order : Type u) [Fintype order] [LinearOrder order]

example : Smooth (upperTriangularGroupUnderlyingScheme K order).hom := inferInstance
example : GeometricallyIntegral (upperTriangularGroupUnderlyingScheme K order).hom :=
  inferInstance

example : Smooth (multiplicativeGroupUnderlyingScheme (ZMod 1)).hom := inferInstance
example : GeometricallyIntegral (multiplicativeGroupUnderlyingScheme (ZMod 1)).hom :=
  inferInstance
example : Smooth (diagonalGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance
example : GeometricallyIntegral (diagonalGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom :=
  inferInstance
example : Smooth (upperTriangularGroupUnderlyingScheme (ZMod 1) (Fin 1)).hom :=
  inferInstance
example : GeometricallyIntegral (upperTriangularGroupUnderlyingScheme (ZMod 1) (Fin 1)).hom :=
  inferInstance

example : Smooth (multiplicativeGroupUnderlyingScheme (ℤ × ℤ)).hom := inferInstance
example : GeometricallyIntegral (multiplicativeGroupUnderlyingScheme (ℤ × ℤ)).hom :=
  inferInstance
example : Smooth (diagonalGroupUnderlyingScheme (ℤ × ℤ) (Fin 3)).hom := inferInstance
example : GeometricallyIntegral (diagonalGroupUnderlyingScheme (ℤ × ℤ) (Fin 3)).hom :=
  inferInstance
example : Smooth (upperTriangularGroupUnderlyingScheme (ℤ × ℤ) (Fin 3)).hom :=
  inferInstance
example : GeometricallyIntegral (upperTriangularGroupUnderlyingScheme (ℤ × ℤ) (Fin 3)).hom :=
  inferInstance

example : Smooth (diagonalGroupUnderlyingScheme ℤ (Fin 1)).hom := inferInstance
example : GeometricallyIntegral (diagonalGroupUnderlyingScheme ℤ (Fin 1)).hom :=
  inferInstance
example : Smooth (upperTriangularGroupUnderlyingScheme ℤ (Fin 0)).hom := inferInstance
example : GeometricallyIntegral (upperTriangularGroupUnderlyingScheme ℤ (Fin 0)).hom :=
  inferInstance

example : IsIntegral (multiplicativeGroupUnderlyingScheme ℤ).left := inferInstance
example : IsIntegral (diagonalGroupUnderlyingScheme ℤ (Fin 0)).left := inferInstance
example : IsIntegral (diagonalGroupUnderlyingScheme ℤ (Fin 1)).left := inferInstance
example : IsIntegral (diagonalGroupUnderlyingScheme ℤ (Fin 3)).left := inferInstance
example : IsIntegral (upperTriangularGroupUnderlyingScheme ℤ (Fin 0)).left := inferInstance
example : IsIntegral (upperTriangularGroupUnderlyingScheme ℤ (Fin 1)).left := inferInstance
example : IsIntegral (upperTriangularGroupUnderlyingScheme ℤ (Fin 3)).left := inferInstance

end AlgebraicGroupsTest.GroupScheme.FiniteTriangularGeometry
