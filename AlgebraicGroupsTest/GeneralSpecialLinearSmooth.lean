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

open CategoryTheory TauCeti.GeneralLinear SpecialLinearCoordinateRing

universe u

namespace AlgebraicGroupsTest.GeneralSpecialLinearSmooth

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

example : Algebra.FinitePresentation K
    ((coordinateHopfAlgebra K (Fintype.card n))) := inferInstance

example : Algebra.FinitePresentation K
    ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := inferInstance

example : Algebra.Smooth K
    ((coordinateHopfAlgebra K (Fintype.card n))) := inferInstance

example : Algebra.Smooth K
    ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := inferInstance

example : AlgebraicGeometry.Smooth
    ((groupScheme K (Fintype.card n)).X).hom := inferInstance

example : AlgebraicGeometry.Smooth
    ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).hom := inferInstance

variable (pivot : n)

example : ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom).comp
      (AlgebraicGeometry.specialLinearNormalizationSection K n pivot) =
      AlgHom.id K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient K n pivot

example (i j : n) :
    AlgebraicGeometry.specialLinearNormalizationSection K n pivot
        (((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
          (reindexedGenericMatrix K n i j))) =
      (AlgebraicGeometry.specialLinearNormalization K n pivot : Matrix n n
        ((coordinateHopfAlgebra K (Fintype.card n)))) i j :=
  AlgebraicGeometry.specialLinearNormalizationSection_entry K n pivot i j

example (i j : n) :
    ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom)
        (AlgebraicGeometry.specialLinearNormalizationSection K n pivot
          (((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
          (reindexedGenericMatrix K n i j)))) =
      ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
          (reindexedGenericMatrix K n i j)) := by
  have retraction := AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient
    K n pivot
  have readback := congrArg
    (fun f : (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) →ₐ[K]
        (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) ↦
      f (((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom
          (reindexedGenericMatrix K n i j)))) retraction
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using readback

example : Algebra.Smooth ℤ ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 0)) :=
  inferInstance

example : AlgebraicGeometry.Smooth
    ((TauCeti.SpecialLinear.groupScheme ℤ (Fintype.card (Fin 0))).X).hom :=
  inferInstance

example : Algebra.Smooth ℤ ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 1)) :=
  inferInstance

example : Algebra.Smooth ℤ ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2)) :=
  inferInstance

example : ((TauCeti.SpecialLinear.coordinateMap ℤ (Fintype.card (Fin 1))).hom.toAlgHom).comp
      (AlgebraicGeometry.specialLinearNormalizationSection ℤ (Fin 1) 0) =
      AlgHom.id ℤ ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 1)) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient ℤ (Fin 1) 0

example : ((TauCeti.SpecialLinear.coordinateMap ℤ (Fintype.card (Fin 2))).hom.toAlgHom).comp
      (AlgebraicGeometry.specialLinearNormalizationSection ℤ (Fin 2) 1) =
      AlgHom.id ℤ ((TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2)) :=
  AlgebraicGeometry.specialLinearNormalizationSection_comp_quotient ℤ (Fin 2) 1

example : Algebra.Smooth (ZMod 1)
    ((coordinateHopfAlgebra (ZMod 1) (Fintype.card (Fin 0)))) := inferInstance

example : Algebra.Smooth (ZMod 1)
    ((TauCeti.SpecialLinear.coordinateHopfAlgebra (ZMod 1) (Fintype.card (Fin 0)))) := inferInstance

example : Algebra.Smooth (ZMod 1)
    ((TauCeti.SpecialLinear.coordinateHopfAlgebra (ZMod 1) (Fintype.card (Fin 2)))) := inferInstance

example : AlgebraicGeometry.Smooth
    ((groupScheme (ZMod 1) (Fintype.card (Fin 1))).X).hom :=
  inferInstance

example : AlgebraicGeometry.Smooth
    ((TauCeti.SpecialLinear.groupScheme (ZMod 1) (Fintype.card (Fin 0))).X).hom :=
  inferInstance

example : AlgebraicGeometry.Smooth
    ((TauCeti.SpecialLinear.groupScheme (ZMod 1) (Fintype.card (Fin 2))).X).hom :=
  inferInstance

end AlgebraicGroupsTest.GeneralSpecialLinearSmooth
