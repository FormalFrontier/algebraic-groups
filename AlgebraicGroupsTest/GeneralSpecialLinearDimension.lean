/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension
public import Mathlib.Algebra.Field.ZMod

/-!
# Public-client checks for finite GL/SL dimensions

These examples import the production API and check rational-point height, both
actual coordinate rings, and both underlying schemes over arbitrary fields,
in ranks zero, one and two, and in characteristic two.
-/

public section

set_option warningAsError true

noncomputable section

universe u v

namespace AlgebraicGroupsTest.GeneralSpecialLinearDimension

variable (K : Type u) [Field K] (σ : Type v) [Fintype σ]

example (point : σ → K) : (RingHom.ker (MvPolynomial.eval point)).height =
    (Fintype.card σ : ℕ∞) :=
  MvPolynomial.height_ker_eval K σ point

variable (n : Type u) [Fintype n] [DecidableEq n]

example : ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing K n) =
    ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim K n

example : ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K n) =
    ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim K n

example : topologicalKrullDim
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme K n).left =
    ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim K n

example : topologicalKrullDim
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme K n).left =
    ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim K n

variable (F : Type) [Field F]

example : ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing F (Fin 0)) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 0)

example : ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing F (Fin 0)) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 0)

example : topologicalKrullDim
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme F (Fin 0)).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 0)

example : topologicalKrullDim
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme F (Fin 0)).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 0)

example : ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing F (Fin 1)) =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 1)

example : ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing F (Fin 1)) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 1)

example : topologicalKrullDim
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme F (Fin 1)).left =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 1)

example : topologicalKrullDim
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme F (Fin 1)).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 1)

example : ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing F (Fin 2)) =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 2)

example : ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing F (Fin 2)) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme F (Fin 2)).left =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme F (Fin 2)).left =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 2)

example : ringKrullDim
    (GeneralLinearCoordinateRing.CoordinateRing (ZMod 2) (Fin 2)) =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example : ringKrullDim
    (SpecialLinearCoordinateRing.CoordinateRing (ZMod 2) (Fin 2)) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.generalLinearGroupUnderlyingScheme (ZMod 2) (Fin 2)).left =
    (4 : WithBot ℕ∞) := by
  simpa using
    AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim (ZMod 2) (Fin 2)

example : topologicalKrullDim
    (AlgebraicGeometry.specialLinearGroupUnderlyingScheme (ZMod 2) (Fin 2)).left =
    (3 : WithBot ℕ∞) := by
  simpa using
    AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim (ZMod 2) (Fin 2)

end AlgebraicGroupsTest.GeneralSpecialLinearDimension
