/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointKernel
public import AlgebraicGroups.GroupScheme.RootsOfUnity

/-!
# Roots of unity among closed points

For every natural order, the original roots-of-unity inclusion identifies its
closed points with the kernel of the power map on the multiplicative group's
closed points. In particular every closed point killed by that power has a
unique lift through the original inclusion.

Order zero is included: the power map is constant one, and the original kernel
is the whole multiplicative group. The original group-algebra model and all-order
pullback are used, not a positive-order polynomial presentation. Local finite type
of the kernel is derived by the generic comparison. No topology on the ground
field is required.

## References

- `AlgebraicGroups.GroupScheme.RootsOfUnity`, for the original power pullback
  on all test schemes, following Milne, *Algebraic Groups* (2017), item 2.4.
- Mathlib, `MonObj.comp_pow`, for powering on generalized points.
- `AlgebraicGroups.GroupScheme.ClosedPointKernel`, for the continuous kernel
  comparison and its unique-lift eliminator.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- The original power endomorphism acts by the same natural power in the
canonical closed-point group of the multiplicative group.
This is an explicit rewrite theorem, retaining the original bundled power map. -/
theorem multiplicativeGroupClosedPointsMap_pow (n : ℕ)
    (x : closedPoints (multiplicativeGroupUnderlyingScheme K).left) :
    groupSchemeClosedPointsMap
      (gG := (multiplicativeGroupScheme K).grp)
      (gH := (multiplicativeGroupScheme K).grp)
      (multiplicativeGroupUnderlyingScheme K).hom
      (multiplicativeGroupUnderlyingScheme K).hom
      ((𝟙 (multiplicativeGroupScheme K)) ^ n).hom.hom x =
    @Pow.pow (closedPoints (multiplicativeGroupUnderlyingScheme K).left) ℕ
      (@NPow.toPow _
        (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
          inferInstance inferInstance (multiplicativeGroupScheme K).grp).toNPow) x n := by
  let : GrpObj (Over.mk (multiplicativeGroupUnderlyingScheme K).hom) :=
    (multiplicativeGroupScheme K).grp
  let := @groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
    inferInstance inferInstance (multiplicativeGroupScheme K).grp
  obtain ⟨p, rfl⟩ :=
    (groupSchemePointEquivClosedPoint (multiplicativeGroupUnderlyingScheme K).hom).surjective x
  rw [groupSchemeClosedPointsMap_apply_point]
  have hp : p ≫ ((𝟙 (multiplicativeGroupScheme K)) ^ n).hom.hom = p ^ n := by
    rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    change p ≫ (𝟙 (Over.mk (multiplicativeGroupUnderlyingScheme K).hom)) ^ n = p ^ n
    rw [MonObj.comp_pow, Category.comp_id]
  rw [hp]
  exact map_pow (@groupSchemePointMulEquivClosedPoint _ _ _
    (multiplicativeGroupUnderlyingScheme K).hom inferInstance inferInstance
    (multiplicativeGroupScheme K).grp) p n

/-- A closed point of the multiplicative group has `n`-th power one exactly
when it lifts uniquely through the original roots-of-unity inclusion.
This includes `n = 0`, without a positive-order hypothesis. -/
theorem rootsOfUnityClosedPoints_pow_eq_one_iff (n : ℕ)
    (x : closedPoints (multiplicativeGroupUnderlyingScheme K).left) :
    @Pow.pow (closedPoints (multiplicativeGroupUnderlyingScheme K).left) ℕ
      (@NPow.toPow _
        (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
          inferInstance inferInstance (multiplicativeGroupScheme K).grp).toNPow) x n =
      @One.one (closedPoints (multiplicativeGroupUnderlyingScheme K).left)
        (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
          inferInstance inferInstance (multiplicativeGroupScheme K).grp).toOne ↔
      ∃! y : closedPoints (rootsOfUnityScheme K n).left,
        (rootsOfUnityGroupSchemeInclusion K n).hom.hom.left y.val = x.val := by
  have h := groupSchemeKernelClosedPoints_existsUnique
    (gG := (multiplicativeGroupScheme K).grp)
    (gH := (multiplicativeGroupScheme K).grp)
    (gN := (rootsOfUnityGroupScheme K n).grp)
    (multiplicativeGroupUnderlyingScheme K).hom
    (multiplicativeGroupUnderlyingScheme K).hom
    (rootsOfUnityScheme K n).hom
    ((𝟙 (multiplicativeGroupScheme K)) ^ n).hom.hom
    (rootsOfUnityGroupSchemeInclusion K n).hom.hom
    (rootsOfUnityPowerSquare_isPullback_over K n) x
  rwa [multiplicativeGroupClosedPointsMap_pow] at h

end AlgebraicGeometry
