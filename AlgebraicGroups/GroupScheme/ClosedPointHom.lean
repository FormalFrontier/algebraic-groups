/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointSubgroup
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import SchemeProperties.LocallyConstructiblePreimage

/-!
# Continuous homomorphisms on group-scheme closed points

A homomorphism of group schemes locally of finite type over an algebraically
closed field induces a continuous monoid homomorphism on their canonical
closed-point groups. Its algebraic map is the composite of Mathlib's
`CategoryTheory.IsMonHom.monoidHom` with the existing rational-point comparisons.
Its topology is the original closed-point subspace topology. Joint continuity
of multiplication is not required.

The range is the usual `MonoidHom.range`, and its carrier is the preimage of
the original scheme-point range under the target closed-point inclusion.
A locally closed range is closed. A quasi-compact group-scheme morphism has
closed range on closed points, by Chevalley's theorem and the single-member
subgroup criterion. Closedness is not asserted for every group-scheme morphism.
No conclusion about scheme immersions or nonreduced subgroup schemes follows.

## References

- Mathlib, `CategoryTheory.IsMonHom.monoidHom`, for postcomposition on points,
  and `ContinuousMonoidHom`, for the continuous bundle and its identity and composition.
- `AlgebraicGroups.GroupScheme.ClosedPoints`, for the canonical group and
  rational-point comparison, following Milne, *Algebraic Groups* (2017), item 1.7.
- `AlgebraicGroups.GroupScheme.ClosedPointSubgroup`, for the locally closed
  subgroup criterion without joint continuity of multiplication.
- Mathlib, `LocallyOfFiniteType.jacobsonSpace` and
  `nonempty_inter_closedPoints`, for a closed point in each nonempty closed fibre.
- Mathlib, `Scheme.Hom.isLocallyConstructible_image` (Chevalley's theorem), and
  SchemeProperties, `IsLocallyConstructible.exists_isLocallyClosedAt_preimage`,
  for a locally closed member of the closed-point range.
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

/-- The canonical closed-point range is the preimage of the original
scheme-point range under the target closed-point inclusion. A nonempty fibre
over a closed point is closed, and contains a closed point because the source
is Jacobson. No quasi-compactness of the morphism is needed. -/
theorem groupSchemeClosedPointsMap_range_eq_preimage :
    (@MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH)
      (@ContinuousMonoidHom.toMonoidHom _ _
        (groupSchemeClosedPointsGroup fG).toMonoid
        (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
        (groupSchemeClosedPointsMap fG fH φ)) : Set (closedPoints H)) =
      (Subtype.val : closedPoints H → H) ⁻¹' Set.range φ.left := by
  ext y
  refine (mem_groupSchemeClosedPointsMap_range fG fH φ y).trans ?_
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.val, hx⟩
  · rintro ⟨x, hx⟩
    let : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace fG
    obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints
      (X := G) (Z := φ.left ⁻¹' ({y.val} : Set H))
      ⟨x, hx⟩ (y.property.preimage φ.left.continuous).isLocallyClosed
    exact ⟨⟨z, hzclosed⟩, hz⟩

/-- A quasi-compact homomorphism of group schemes locally of finite type over
an algebraically closed field has closed range in the target closed-point subspace.
This combines Chevalley's theorem with the single-member subgroup criterion. -/
theorem groupSchemeClosedPointsMap_isClosed_range_of_quasiCompact
    [QuasiCompact φ.left] :
    IsClosed
      (@MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
        (closedPoints H) (groupSchemeClosedPointsGroup fH)
        (@ContinuousMonoidHom.toMonoidHom _ _
          (groupSchemeClosedPointsGroup fG).toMonoid
          (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
          (groupSchemeClosedPointsMap fG fH φ)) : Set (closedPoints H)) := by
  have hw : φ.left ≫ fH = fG := φ.w
  let : LocallyOfFiniteType (φ.left ≫ fH) := by
    rw [hw]
    infer_instance
  let : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left fH
  let : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian fH
  let : LocallyOfFinitePresentation φ.left :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (X := G) (Y := H) (f := φ.left)).mpr inferInstance
  have hLC : Topology.IsLocallyConstructible (Set.range φ.left) := by
    simpa only [Set.image_univ] using
      (φ.left.isLocallyConstructible_image
        (s := (Set.univ : Set G)) Topology.IsLocallyConstructible.univ)
  let R := @MonoidHom.range (closedPoints G) (groupSchemeClosedPointsGroup fG)
    (closedPoints H) (groupSchemeClosedPointsGroup fH)
    (@ContinuousMonoidHom.toMonoidHom _ _
      (groupSchemeClosedPointsGroup fG).toMonoid
      (groupSchemeClosedPointsGroup fH).toMonoid inferInstance inferInstance
      (groupSchemeClosedPointsMap fG fH φ))
  have hR : (R : Set (closedPoints H)) =
      (Subtype.val : closedPoints H → H) ⁻¹' Set.range φ.left :=
    groupSchemeClosedPointsMap_range_eq_preimage fG fH φ
  have hne : ((Subtype.val : closedPoints H → H) ⁻¹' Set.range φ.left).Nonempty := by
    rw [← hR]
    exact ⟨_, @Subgroup.one_mem _ (groupSchemeClosedPointsGroup fH) R⟩
  obtain ⟨x, hx, hxLC⟩ :=
    _root_.IsLocallyConstructible.exists_isLocallyClosedAt_preimage
      hLC continuous_subtype_val hne
  rw [← hR] at hx hxLC
  exact (groupSchemeClosedPoints_isClosed_iff_isLocallyClosedAt fH R hx).mpr hxLC

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

/-- A dominant group-scheme homomorphism has dense range on the canonical
closed-point groups with their original subspace topologies. Local finite type
over the field makes the source Jacobson; no quasi-compactness of the morphism
is required. -/
theorem groupSchemeClosedPointsMap_denseRange [IsDominant φ.left] :
    DenseRange (groupSchemeClosedPointsMap fG fH φ) := by
  let : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace fG
  have hG : Dense (closedPoints G) := dense_iff_closure_eq.mpr closure_closedPoints
  have hd : DenseRange (φ.left ∘ (Subtype.val : closedPoints G → G)) :=
    φ.left.denseRange.comp hG.denseRange_val φ.left.continuous
  change Dense (Set.range (groupSchemeClosedPointsMap fG fH φ))
  apply Subtype.dense_iff.2
  intro y _
  rw [← Set.range_comp]
  simpa only [Function.comp_def, groupSchemeClosedPointsMap_apply_value] using hd y

/-- A dominant quasi-compact homomorphism of group schemes locally of finite
 type over an algebraically closed field is surjective on closed points. -/
theorem groupSchemeClosedPointsMap_surjective
    [IsDominant φ.left] [QuasiCompact φ.left] :
    Function.Surjective (groupSchemeClosedPointsMap fG fH φ) := by
  have hclosed : IsClosed (Set.range (groupSchemeClosedPointsMap fG fH φ)) :=
    groupSchemeClosedPointsMap_isClosed_range_of_quasiCompact fG fH φ
  exact Set.range_eq_univ.mp
    (hclosed.closure_eq.symm.trans
      (dense_iff_closure_eq.mp (groupSchemeClosedPointsMap_denseRange fG fH φ)))

end AlgebraicGeometry
