/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPoints
public import SchemeProperties.ClosedPointProducts
public import Mathlib.Algebra.Group.Commutator

/-!
# Commutator sections on closed points

Fixing either argument of a commutator gives a continuous map on the closed
points of a group scheme locally of finite type over an algebraically closed
field. The group structure is the one induced by the given group scheme, and
the topology is the original subspace topology. These statements do not assert
joint continuity for the ordinary product topology on the closed-point space.

## References

- Mathlib, `CategoryTheory.GrpObj.commutator` and `Continuous.restrict`.
- SchemeProperties,
  `AlgebraicGeometry.Scheme.Hom.mapsTo_closedPoints_of_comp_eq`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- The commutator with a fixed second argument is continuous on closed points. -/
theorem groupSchemeClosedPoints_continuous_commutator_const
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)] (g : closedPoints G) :
    Continuous (fun x : closedPoints G ↦
      @Bracket.bracket (closedPoints G) (closedPoints G)
        (@commutatorElement (closedPoints G) (groupSchemeClosedPointsGroup f)) x g) := by
  let := groupSchemeClosedPointsGroup f
  let E := groupSchemePointMulEquivClosedPoint f
  let p := E.symm g
  -- Freeze the second coordinate before restricting the scheme map to closed points.
  let a : Over.mk f ⟶ Over.mk f :=
    lift (𝟙 (Over.mk f)) (toUnit (Over.mk f) ≫ p) ≫ GrpObj.commutator (Over.mk f)
  have ha : Set.MapsTo a.left (closedPoints G) (closedPoints G) :=
    Scheme.Hom.mapsTo_closedPoints_of_comp_eq f f a.left a.w
  refine (Continuous.restrict ha a.left.continuous).congr ?_
  intro x
  obtain ⟨q, rfl⟩ := E.surjective x
  have hp : E p = g := E.apply_symm_apply g
  have hq : q ≫ a = q * p * q⁻¹ * p⁻¹ := by
    dsimp only [a]
    rw [GrpObj.lift_commutator_eq_mul_mul_inv_inv]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
      ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  calc
    ha.restrict a.left (closedPoints G) (closedPoints G) (E q) = E (q ≫ a) := by
      apply Subtype.ext
      simpa only [Set.MapsTo.val_restrict_apply, E,
        groupSchemePointMulEquivClosedPoint_apply,
        groupSchemePointEquivClosedPoint_apply_value] using
        (show a.left (q.left (IsLocalRing.closedPoint K)) =
          (q ≫ a).left (IsLocalRing.closedPoint K) from rfl)
    _ = E (q * p * q⁻¹ * p⁻¹) := congrArg E hq
    _ = ⁅E q, g⁆ := by
      simp only [map_mul, map_inv, hp, commutatorElement_def]

/-- The commutator with a fixed first argument is continuous on closed points. -/
theorem groupSchemeClosedPoints_continuous_const_commutator
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)] (g : closedPoints G) :
    Continuous (fun x : closedPoints G ↦
      @Bracket.bracket (closedPoints G) (closedPoints G)
        (@commutatorElement (closedPoints G) (groupSchemeClosedPointsGroup f)) g x) := by
  let := groupSchemeClosedPointsGroup f
  have h := (groupSchemeClosedPoints_continuous_inv f).comp
    (groupSchemeClosedPoints_continuous_commutator_const f g)
  refine h.congr ?_
  intro x
  change (⁅x, g⁆)⁻¹ = ⁅g, x⁆
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

end AlgebraicGeometry
