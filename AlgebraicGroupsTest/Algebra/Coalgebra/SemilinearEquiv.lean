/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.Equiv
import Mathlib.Algebra.Module.ULift

/-!
# Simultaneous scalar and carrier universe lift of a coalgebra

The canonical down equivalences change both the scalar semiring and the module carrier.
The tensor comparison recovers the original comultiplication, and the down map on scalars
recovers the original counit. The two original universes and two lift levels are independent.
The full coalgebra is constructed on the given lifted module structure.
-/

universe u v p q

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

example {R : Type u} {C : Type v} [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] (x : ULift.{q} C) :
    let σ : ULift.{p} R ≃+* R := ULift.ringEquiv
    let e : ULift.{q} C ≃ₛₗ[(σ : ULift.{p} R →+* R)] C :=
      { toAddEquiv := AddEquiv.ulift, map_smul' := fun _ _ => rfl }
    let c := LinearEquiv.coalgebraOfRingEquiv σ e
    TensorProduct.congr e e
        (@CoalgebraStruct.comul (ULift.{p} R) (ULift.{q} C) _ _ _ c.toCoalgebraStruct x) =
        Coalgebra.comul (R := R) x.down ∧
      (@CoalgebraStruct.counit (ULift.{p} R) (ULift.{q} C) _ _ _ c.toCoalgebraStruct x).down =
        Coalgebra.counit (R := R) x.down := by
  dsimp only
  constructor
  · exact LinearEquiv.congr_coalgebraOfRingEquiv_comul _ _ _
  · rw [LinearEquiv.coalgebraOfRingEquiv_counit_apply]
    rfl
