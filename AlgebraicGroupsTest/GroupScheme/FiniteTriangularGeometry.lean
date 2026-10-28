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

open AlgebraicGeometry TauCeti.GeneralLinear.UpperTriangular

universe u

namespace AlgebraicGroupsTest.GroupScheme.FiniteTriangularGeometry

variable (K : Type u) [CommRing K] (index : Type u) [Finite index]

example : Smooth ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).hom := inferInstance
example : GeometricallyIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme
  K).X).hom := inferInstance
example : Smooth ((TauCeti.SplitTorus.groupScheme K index).X).hom := inferInstance
example : GeometricallyIntegral ((TauCeti.SplitTorus.groupScheme K index).X).hom := inferInstance

variable (rank : ℕ)

example : Smooth ((groupScheme K rank).X).hom := inferInstance
example : GeometricallyIntegral ((groupScheme K rank).X).hom :=
  inferInstance

example : Smooth ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme (ZMod 1)).X).hom :=
  inferInstance
example : GeometricallyIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme (ZMod
  1)).X).hom :=
  inferInstance
example : Smooth ((TauCeti.SplitTorus.groupScheme (ZMod 1) (Fin 0)).X).hom := inferInstance
example : GeometricallyIntegral ((TauCeti.SplitTorus.groupScheme (ZMod 1) (Fin 0)).X).hom :=
  inferInstance
example : Smooth ((groupScheme (ZMod 1) 1).X).hom :=
  inferInstance
example : GeometricallyIntegral ((groupScheme (ZMod 1) 1).X).hom :=
  inferInstance

example : Smooth ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme (ℤ × ℤ)).X).hom :=
  inferInstance
example : GeometricallyIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme (ℤ ×
  ℤ)).X).hom :=
  inferInstance
example : Smooth ((TauCeti.SplitTorus.groupScheme (ℤ × ℤ) (Fin 3)).X).hom := inferInstance
example : GeometricallyIntegral ((TauCeti.SplitTorus.groupScheme (ℤ × ℤ) (Fin 3)).X).hom :=
  inferInstance
example : Smooth ((groupScheme (ℤ × ℤ) 3).X).hom :=
  inferInstance
example : GeometricallyIntegral ((groupScheme (ℤ × ℤ) 3).X).hom :=
  inferInstance

example : Smooth ((TauCeti.SplitTorus.groupScheme ℤ (Fin 1)).X).hom := inferInstance
example : GeometricallyIntegral ((TauCeti.SplitTorus.groupScheme ℤ (Fin 1)).X).hom :=
  inferInstance
example : Smooth ((groupScheme ℤ 0).X).hom := inferInstance
example : GeometricallyIntegral ((groupScheme ℤ 0).X).hom :=
  inferInstance

example : IsIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme ℤ).X).left :=
  inferInstance
example : IsIntegral ((TauCeti.SplitTorus.groupScheme ℤ (Fin 0)).X).left := inferInstance
example : IsIntegral ((TauCeti.SplitTorus.groupScheme ℤ (Fin 1)).X).left := inferInstance
example : IsIntegral ((TauCeti.SplitTorus.groupScheme ℤ (Fin 3)).X).left := inferInstance
example : IsIntegral ((groupScheme ℤ 0).X).left := inferInstance
example : IsIntegral ((groupScheme ℤ 1).X).left := inferInstance
example : IsIntegral ((groupScheme ℤ 3).X).left := inferInstance

end AlgebraicGroupsTest.GroupScheme.FiniteTriangularGeometry
