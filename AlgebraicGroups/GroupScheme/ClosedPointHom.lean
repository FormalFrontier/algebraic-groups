/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous homomorphisms on group-scheme closed points

A homomorphism of group schemes locally of finite type over an algebraically
closed field induces a continuous monoid homomorphism on their canonical
closed-point groups. Its algebraic map is the composite of Mathlib's
`CategoryTheory.IsMonHom.monoidHom` with the existing rational-point comparisons.
Its topology is the original closed-point subspace topology. Joint continuity
of multiplication is not required.

The range is the usual `MonoidHom.range`. Closedness of a general range requires
a locally closed image; it is not asserted for every group-scheme morphism.
No conclusion about scheme immersions or nonreduced subgroup schemes follows.

## References

- Mathlib, `CategoryTheory.IsMonHom.monoidHom`, for postcomposition on points,
  and `ContinuousMonoidHom`, for the continuous bundle and its identity and composition.
- `AlgebraicGroups.GroupScheme.ClosedPoints`, for the canonical group and
  rational-point comparison, following Milne, *Algebraic Groups* (2017), item 1.7.
- `AlgebraicGroups.GroupScheme.ClosedPointSubgroup`, for the locally closed
  subgroup criterion without joint continuity of multiplication.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {G H J : Scheme.{u}}
variable (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K))
variable [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
variable [gG : GrpObj (Over.mk fG)] [gH : GrpObj (Over.mk fH)]
variable (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]

/-- The canonical continuous homomorphism on closed points, with the full
monoid structures projected from the given canonical closed-point groups. -/
def groupSchemeClosedPointsMap :
    @ContinuousMonoidHom (closedPoints G) (closedPoints H)
      (groupSchemeClosedPointsGroup fG).toMonoid
      (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance := by
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  let h := (groupSchemePointMulEquivClosedPoint fH).toMonoidHom.comp
    ((IsMonHom.monoidHom φ (𝟙_ (Over (Spec (.of K))))).comp
      (groupSchemePointMulEquivClosedPoint fG).symm.toMonoidHom)
  have hval (x : closedPoints G) : (h x).val = φ.left x.val := by
    change (groupSchemePointEquivClosedPoint fH
      ((groupSchemePointEquivClosedPoint fG).symm x ≫ φ)).val = _
    rw [groupSchemePointEquivClosedPoint_apply_value]
    change φ.left (((groupSchemePointEquivClosedPoint fG).symm x).left
      (IsLocalRing.closedPoint K)) = _
    rw [groupSchemePointEquivClosedPoint_symm_apply_value]
  refine { h with continuous_toFun := ?_ }
  apply continuous_induced_rng.mpr
  change Continuous (fun x : closedPoints G => (h x).val)
  have hc : Continuous (fun x : closedPoints G => φ.left x.val) :=
    φ.left.continuous.comp continuous_subtype_val
  exact hc.congr (fun x => (hval x).symm)

/-- The algebraic projection is exactly postcomposition through the existing
rational-point group equivalences. -/
theorem groupSchemeClosedPointsMap_toMonoidHom :
    (@ContinuousMonoidHom.toMonoidHom _ _
      (groupSchemeClosedPointsGroup fG).toMonoid
      (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
      (groupSchemeClosedPointsMap fG fH φ)) =
      @MonoidHom.comp _ _ _ (groupSchemeClosedPointsGroup fG).toMulOne
        inferInstance (groupSchemeClosedPointsGroup fH).toMulOne
        (@MulEquiv.toMonoidHom _ _ inferInstance
          (groupSchemeClosedPointsGroup fH).toMulOneClass
          (groupSchemePointMulEquivClosedPoint fH))
        (@MonoidHom.comp _ _ _ (groupSchemeClosedPointsGroup fG).toMulOne
          inferInstance inferInstance
          (IsMonHom.monoidHom φ (𝟙_ (Over (Spec (.of K)))))
          (@MulEquiv.toMonoidHom _ _ (groupSchemeClosedPointsGroup fG).toMulOneClass
            inferInstance
            (@MulEquiv.symm _ _ inferInstance (groupSchemeClosedPointsGroup fG).toMul
              (groupSchemePointMulEquivClosedPoint fG)))) := rfl

/-- Application of the canonical map through the rational-point comparison. -/
theorem groupSchemeClosedPointsMap_apply (x : closedPoints G) :
    groupSchemeClosedPointsMap fG fH φ x =
      groupSchemePointEquivClosedPoint fH
        ((groupSchemePointEquivClosedPoint fG).symm x ≫ φ) := rfl

/-- On underlying scheme points, the canonical map is the original morphism. -/
@[simp]
theorem groupSchemeClosedPointsMap_apply_value (x : closedPoints G) :
    (groupSchemeClosedPointsMap fG fH φ x).val = φ.left x.val := by
  rw [groupSchemeClosedPointsMap_apply, groupSchemePointEquivClosedPoint_apply_value]
  change φ.left (((groupSchemePointEquivClosedPoint fG).symm x).left
    (IsLocalRing.closedPoint K)) = _
  rw [groupSchemePointEquivClosedPoint_symm_apply_value]

/-- Naturality of the existing rational-point group comparison. -/
@[simp]
theorem groupSchemeClosedPointsMap_apply_point
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk fG) :
    groupSchemeClosedPointsMap fG fH φ (groupSchemePointEquivClosedPoint fG p) =
      groupSchemePointEquivClosedPoint fH (p ≫ φ) := by
  simp only [groupSchemeClosedPointsMap_apply, Equiv.symm_apply_apply]

/-- Inverse-comparison readback of the canonical closed-point map. -/
@[simp]
theorem groupSchemeClosedPointsMap_symm_apply (x : closedPoints G) :
    (@MulEquiv.symm _ _ inferInstance (groupSchemeClosedPointsGroup fH).toMul
      (groupSchemePointMulEquivClosedPoint fH))
        (groupSchemeClosedPointsMap fG fH φ x) =
      (@MulEquiv.symm _ _ inferInstance (groupSchemeClosedPointsGroup fG).toMul
        (groupSchemePointMulEquivClosedPoint fG)) x ≫ φ := by
  change (groupSchemePointEquivClosedPoint fH).symm
    (groupSchemePointEquivClosedPoint fH
      ((groupSchemePointEquivClosedPoint fG).symm x ≫ φ)) = _
  exact Equiv.symm_apply_apply _ _

/-- Identity group-scheme morphisms induce the continuous identity. -/
@[simp]
theorem groupSchemeClosedPointsMap_id :
    groupSchemeClosedPointsMap fG fG (𝟙 (Over.mk fG)) =
      @ContinuousMonoidHom.id (closedPoints G)
        (groupSchemeClosedPointsGroup fG).toMonoid inferInstance := by
  let := groupSchemeClosedPointsGroup fG
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  simp

variable (fJ : J ⟶ Spec (.of K)) [LocallyOfFiniteType fJ] [gJ : GrpObj (Over.mk fJ)]

/-- Composition of group-scheme morphisms induces continuous composition. -/
@[simp]
theorem groupSchemeClosedPointsMap_comp
    (ψ : Over.mk fH ⟶ Over.mk fJ) [IsMonHom ψ] :
    groupSchemeClosedPointsMap fG fJ (φ ≫ ψ) =
      @ContinuousMonoidHom.comp (closedPoints G) (closedPoints H) (closedPoints J)
        (groupSchemeClosedPointsGroup fG).toMonoid
        (groupSchemeClosedPointsGroup fH).toMonoid
        (groupSchemeClosedPointsGroup fJ).toMonoid inferInstance inferInstance inferInstance
        (groupSchemeClosedPointsMap fH fJ ψ) (groupSchemeClosedPointsMap fG fH φ) := by
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  let := groupSchemeClosedPointsGroup fJ
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  simp

/-- Membership in the range is the original scheme-point image condition. -/
theorem mem_groupSchemeClosedPointsMap_range (y : closedPoints H) :
    y ∈ @MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH)
      (@ContinuousMonoidHom.toMonoidHom _ _
        (groupSchemeClosedPointsGroup fG).toMonoid
        (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
        (groupSchemeClosedPointsMap fG fH φ)) ↔
      ∃ x : closedPoints G, φ.left x.val = y.val := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (groupSchemeClosedPointsMap_apply_value fG fH φ x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext ((groupSchemeClosedPointsMap_apply_value fG fH φ x).trans hx)⟩

/-- A locally closed image of a group-scheme homomorphism is closed
in the original closed-point subspace, by the locally closed subgroup criterion. -/
theorem groupSchemeClosedPointsMap_isClosed_range
    (hLC : IsLocallyClosed
      (@MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
        (closedPoints H) (groupSchemeClosedPointsGroup fH)
        (@ContinuousMonoidHom.toMonoidHom _ _
          (groupSchemeClosedPointsGroup fG).toMonoid
          (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
          (groupSchemeClosedPointsMap fG fH φ)) : Set (closedPoints H))) :
    IsClosed
      (@MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
        (closedPoints H) (groupSchemeClosedPointsGroup fH)
        (@ContinuousMonoidHom.toMonoidHom _ _
          (groupSchemeClosedPointsGroup fG).toMonoid
          (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
          (groupSchemeClosedPointsMap fG fH φ)) : Set (closedPoints H)) :=
  groupSchemeClosedPoints_isClosed_of_isLocallyClosed fH _ hLC

end AlgebraicGeometry
