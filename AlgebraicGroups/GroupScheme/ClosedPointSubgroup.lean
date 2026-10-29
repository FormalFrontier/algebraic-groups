/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPoints
public import GroupTheory.Topology.Algebra.Group.LocallyClosed

/-!
# Locally closed subgroups of group-scheme closed points

For a group scheme locally of finite type over an algebraically closed field,
a subgroup of its closed-point group is closed exactly when it is a neighborhood
of the identity within its closure. In particular, locally closed subgroups are
closed. The group is precisely `groupSchemeClosedPointsGroup` for the given
group object, and the topology is the original closed-point subspace topology.

Left translations come from scheme isomorphisms. Together with continuous
inversion, they give separate continuity of multiplication; joint continuity is
neither assumed nor asserted. The subgroup criteria are imported from
`GroupTheory.Topology.Algebra.Group.LocallyClosed`.

## Limitations

The conclusion is closedness of a subset of the closed-point space, not a closed
immersion of schemes, representability or descent, or equality of possibly
nonreduced subgroup schemes. The additive group's closed-point multiplication
is not jointly continuous; see `AlgebraicGroups.GroupScheme.AdditiveClosedPoints`.

## References

- J. S. Milne, *Algebraic Groups* (2017), items 1.7–1.8, for the closed-point
  group, inversion and translation, as formalized in
  `AlgebraicGroups.GroupScheme.ClosedPoints`.
- GroupTheory, `Subgroup.isClosed_iff_mem_nhdsWithin_one` and
  `Subgroup.isClosed_iff_isLocallyClosed`, for the subgroup criteria under
  separate continuity and continuous inversion. These generalize Mathlib's
  `Subgroup.isClosed_of_isLocallyClosed` on the same group and topology.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

private theorem groupSchemeClosedPoints_separatelyContinuousMul
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)] :
    @SeparatelyContinuousMul (closedPoints G) inferInstance
      (groupSchemeClosedPointsGroup f).toMul := by
  let := groupSchemeClosedPointsGroup f
  let E := groupSchemePointMulEquivClosedPoint f
  have hleft (g : closedPoints G) : Continuous (g * ·) := by
    obtain ⟨a, rfl⟩ := E.surjective g
    apply (groupSchemeMulLeftClosedPointsHomeomorph f a).continuous.congr
    intro x
    obtain ⟨p, rfl⟩ := E.surjective x
    change groupSchemeMulLeftClosedPointsHomeomorph f a
      (groupSchemePointEquivClosedPoint f p) = E a * E p
    rw [groupSchemeMulLeftClosedPointsHomeomorph_apply_point]
    exact E.map_mul a p
  refine ⟨fun {a} => hleft a, fun {a} => ?_⟩
  -- Right translation is inversion, left translation by the inverse, then inversion.
  have hinv := groupSchemeClosedPoints_continuous_inv f
  simpa only [Function.comp_def, mul_inv_rev, inv_inv] using
    hinv.comp ((hleft a⁻¹).comp hinv)

/-- A subgroup of the canonical closed-point group is closed exactly when it
is a neighborhood of the identity within its closure, in the closed-point
subspace topology. This applies GroupTheory's separately continuous subgroup
criterion to the closed-point group of Milne, *Algebraic Groups* (2017), item 1.7. -/
theorem groupSchemeClosedPoints_isClosed_iff_mem_nhdsWithin_closure
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)]
    (H : @Subgroup (closedPoints G) (groupSchemeClosedPointsGroup f)) :
    IsClosed (H : Set (closedPoints G)) ↔
      (H : Set (closedPoints G)) ∈
        nhdsWithin
          (@One.one (closedPoints G) (groupSchemeClosedPointsGroup f).toOne)
          (closure (H : Set (closedPoints G))) := by
  let := groupSchemeClosedPointsGroup f
  let : SeparatelyContinuousMul (closedPoints G) :=
    groupSchemeClosedPoints_separatelyContinuousMul f
  let : ContinuousInv (closedPoints G) :=
    ⟨groupSchemeClosedPoints_continuous_inv f⟩
  exact H.isClosed_iff_mem_nhdsWithin_one

/-- A locally closed subgroup of the canonical closed-point group is closed
in the closed-point subspace topology. This uses GroupTheory's locally closed
subgroup criterion and the translations of Milne, *Algebraic Groups* (2017),
items 1.7–1.8, without joint continuity of multiplication. -/
theorem groupSchemeClosedPoints_isClosed_of_isLocallyClosed
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsAlgClosed K]
    [GrpObj (Over.mk f)]
    (H : @Subgroup (closedPoints G) (groupSchemeClosedPointsGroup f))
    (hH : IsLocallyClosed (H : Set (closedPoints G))) :
    IsClosed (H : Set (closedPoints G)) := by
  let := groupSchemeClosedPointsGroup f
  let : SeparatelyContinuousMul (closedPoints G) :=
    groupSchemeClosedPoints_separatelyContinuousMul f
  let : ContinuousInv (closedPoints G) :=
    ⟨groupSchemeClosedPoints_continuous_inv f⟩
  exact H.isClosed_iff_isLocallyClosed.mpr hH

end AlgebraicGeometry
