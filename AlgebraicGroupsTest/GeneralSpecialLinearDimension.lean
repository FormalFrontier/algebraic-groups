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
by
  have hm : (RingHom.ker (MvPolynomial.eval point)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩)
  simpa only [Nat.card_eq_fintype_card] using
    MvPolynomial.height_eq_natCard_of_isMaximal (RingHom.ker (MvPolynomial.eval point))

variable (n : Type u) [Fintype n] [DecidableEq n]

example : ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) =
    ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim K n

example : ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) =
    ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim K n

example : topologicalKrullDim
    ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).left =
    ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim K n

example : topologicalKrullDim
    ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).left =
    ((Fintype.card n ^ 2 - 1 : ℕ) : WithBot ℕ∞) :=
  AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim K n

variable (F : Type) [Field F]

example : ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra F (Fintype.card (Fin 0)))) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 0)

example : ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra F (Fintype.card (Fin 0)))) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 0)

example : topologicalKrullDim
    ((TauCeti.GeneralLinear.groupScheme F (Fintype.card (Fin 0))).X).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 0)

example : topologicalKrullDim
    ((TauCeti.SpecialLinear.groupScheme F (Fintype.card (Fin 0))).X).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 0)

example : ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra F (Fintype.card (Fin 1)))) =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 1)

example : ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra F (Fintype.card (Fin 1)))) =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 1)

example : topologicalKrullDim
    ((TauCeti.GeneralLinear.groupScheme F (Fintype.card (Fin 1))).X).left =
    (1 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 1)

example : topologicalKrullDim
    ((TauCeti.SpecialLinear.groupScheme F (Fintype.card (Fin 1))).X).left =
    (0 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 1)

example : ringKrullDim ((TauCeti.GeneralLinear.coordinateHopfAlgebra F (Fintype.card (Fin 2)))) =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim F (Fin 2)

example : ringKrullDim ((TauCeti.SpecialLinear.coordinateHopfAlgebra F (Fintype.card (Fin 2)))) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim F (Fin 2)

example : topologicalKrullDim
    ((TauCeti.GeneralLinear.groupScheme F (Fintype.card (Fin 2))).X).left =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 2)

example : topologicalKrullDim
    ((TauCeti.SpecialLinear.groupScheme F (Fintype.card (Fin 2))).X).left =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim F (Fin 2)

example : ringKrullDim
    ((TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) (Fintype.card (Fin 2)))) =
    (4 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example : ringKrullDim
    ((TauCeti.SpecialLinear.coordinateHopfAlgebra (ZMod 2) (Fintype.card (Fin 2)))) =
    (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim (ZMod 2) (Fin 2)

example : topologicalKrullDim
    ((TauCeti.GeneralLinear.groupScheme (ZMod 2) (Fintype.card (Fin 2))).X).left =
    (4 : WithBot ℕ∞) := by
  simpa using
    AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim (ZMod 2) (Fin 2)

example : topologicalKrullDim
    ((TauCeti.SpecialLinear.groupScheme (ZMod 2) (Fintype.card (Fin 2))).X).left =
    (3 : WithBot ℕ∞) := by
  simpa using
    AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim (ZMod 2) (Fin 2)

end AlgebraicGroupsTest.GeneralSpecialLinearDimension
