/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointHom
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection

/-!
# The determinant split on closed points

The determinant character and its specified one-pivot diagonal section induce
split continuous homomorphisms on the canonical closed-point groups over an
algebraically closed field. Consequently the determinant's subgroup range
is the whole multiplicative closed-point group. The pivot is required only for
the section and full-range assertion, not for the determinant map itself.

## References

- `AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection`, for the
  group-scheme split, following Milne, *Basic Theory of Affine Group Schemes*,
  XIII §3, item 3.14, and Mathlib's one-pivot determinant witness.
- `AlgebraicGroups.GroupScheme.ClosedPointHom`, for the continuous map and its
  identity and composition laws, using Mathlib's point homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]
variable (n : Type u) [Fintype n] [DecidableEq n]

/-- The original group-scheme determinant section induces a split of the
canonical continuous closed-point determinant homomorphism. -/
theorem generalLinearDeterminantClosedPoints_comp_section (pivot : n) :
    @ContinuousMonoidHom.comp
      (closedPoints (multiplicativeGroupUnderlyingScheme K).left)
      (closedPoints (generalLinearGroupUnderlyingScheme K n).left)
      (closedPoints (multiplicativeGroupUnderlyingScheme K).left)
      (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
        inferInstance inferInstance (multiplicativeGroupScheme K).grp).toMonoid
      (@groupSchemeClosedPointsGroup _ _ _ (generalLinearGroupUnderlyingScheme K n).hom
        inferInstance inferInstance (generalLinearGroupScheme K n).grp).toMonoid
      (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
        inferInstance inferInstance (multiplicativeGroupScheme K).grp).toMonoid
      inferInstance inferInstance inferInstance
      (groupSchemeClosedPointsMap
        (gG := (generalLinearGroupScheme K n).grp)
        (gH := (multiplicativeGroupScheme K).grp)
        (generalLinearGroupUnderlyingScheme K n).hom
        (multiplicativeGroupUnderlyingScheme K).hom
        (generalLinearDeterminantSchemeHom K n).hom.hom)
      (groupSchemeClosedPointsMap
        (gG := (multiplicativeGroupScheme K).grp)
        (gH := (generalLinearGroupScheme K n).grp)
        (multiplicativeGroupUnderlyingScheme K).hom
        (generalLinearGroupUnderlyingScheme K n).hom
        (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) =
      @ContinuousMonoidHom.id (closedPoints (multiplicativeGroupUnderlyingScheme K).left)
        (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
          inferInstance inferInstance (multiplicativeGroupScheme K).grp).toMonoid
        inferInstance := by
  let := @groupSchemeClosedPointsGroup _ _ _ (generalLinearGroupUnderlyingScheme K n).hom
    inferInstance inferInstance (generalLinearGroupScheme K n).grp
  let := @groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
    inferInstance inferInstance (multiplicativeGroupScheme K).grp
  rw [← groupSchemeClosedPointsMap_comp
      (gG := (multiplicativeGroupScheme K).grp)
      (gH := (generalLinearGroupScheme K n).grp)
      (gJ := (multiplicativeGroupScheme K).grp)
      (fG := (multiplicativeGroupUnderlyingScheme K).hom)
      (fH := (generalLinearGroupUnderlyingScheme K n).hom)
      (fJ := (multiplicativeGroupUnderlyingScheme K).hom)
      (φ := (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom)
      (ψ := (generalLinearDeterminantSchemeHom K n).hom.hom),
    ← groupSchemeClosedPointsMap_id (gG := (multiplicativeGroupScheme K).grp)
      (multiplicativeGroupUnderlyingScheme K).hom]
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun f : multiplicativeGroupScheme K ⟶ multiplicativeGroupScheme K ↦
    f.hom.hom.left x.val) (generalLinearDeterminantSectionSchemeHom_comp_det K n pivot)
  simpa [Grp.comp_hom_hom, Grp.id_hom_hom] using h

/-- With a supplied pivot, the determinant's range on closed points is
all of the canonical multiplicative closed-point group. -/
theorem generalLinearDeterminantClosedPoints_range (pivot : n) :
    @MonoidHom.range
      (closedPoints (generalLinearGroupUnderlyingScheme K n).left)
      (@groupSchemeClosedPointsGroup _ _ _ (generalLinearGroupUnderlyingScheme K n).hom
        inferInstance inferInstance (generalLinearGroupScheme K n).grp)
      (closedPoints (multiplicativeGroupUnderlyingScheme K).left)
      (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
        inferInstance inferInstance (multiplicativeGroupScheme K).grp)
      (@ContinuousMonoidHom.toMonoidHom _ _
        (@groupSchemeClosedPointsGroup _ _ _ (generalLinearGroupUnderlyingScheme K n).hom
          inferInstance inferInstance (generalLinearGroupScheme K n).grp).toMonoid
        (@groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
          inferInstance inferInstance (multiplicativeGroupScheme K).grp).toMonoid
        inferInstance inferInstance
        (groupSchemeClosedPointsMap
          (gG := (generalLinearGroupScheme K n).grp)
          (gH := (multiplicativeGroupScheme K).grp)
          (generalLinearGroupUnderlyingScheme K n).hom
          (multiplicativeGroupUnderlyingScheme K).hom
          (generalLinearDeterminantSchemeHom K n).hom.hom)) = ⊤ := by
  let := @groupSchemeClosedPointsGroup _ _ _ (generalLinearGroupUnderlyingScheme K n).hom
    inferInstance inferInstance (generalLinearGroupScheme K n).grp
  let := @groupSchemeClosedPointsGroup _ _ _ (multiplicativeGroupUnderlyingScheme K).hom
    inferInstance inferInstance (multiplicativeGroupScheme K).grp
  apply MonoidHom.range_eq_top.mpr
  intro y
  refine ⟨groupSchemeClosedPointsMap
    (gG := (multiplicativeGroupScheme K).grp)
    (gH := (generalLinearGroupScheme K n).grp)
    (multiplicativeGroupUnderlyingScheme K).hom
    (generalLinearGroupUnderlyingScheme K n).hom
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom y, ?_⟩
  exact DFunLike.congr_fun (generalLinearDeterminantClosedPoints_comp_section K n pivot) y

end AlgebraicGeometry
