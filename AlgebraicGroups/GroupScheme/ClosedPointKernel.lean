/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPointHom
public import AlgebraicGroups.GroupObject.Quotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Closed points of scheme-theoretic kernels

The closed points of a given unit fibre of a group-scheme homomorphism are
continuously multiplicatively equivalent to the kernel of its homomorphism
on closed points. The comparison commutes with the given inclusion. The kernel
structure morphism is locally of finite type because that inclusion is closed.

The topology is the closed-point subspace topology, not a topological-group
structure. The original pullback still describes points on every test scheme;
the closed-point comparison makes no assertion that schemes are determined by
their closed points.

## References

- Mathlib, `IsMonHom.Normal.of_isPullback_η`, for normality of a unit fibre,
  `MonoidHom.ofInjective`, for the equivalence onto a range, and
  `Equiv.toHomeomorphOfIsInducing`, for the topological comparison. The final
  bundle is the stock `ContinuousMulEquiv`.
- `AlgebraicGroups.GroupObject.Quotient`, for range equals kernel on all test
  objects, and `AlgebraicGroups.GroupScheme.ClosedPointHom`, for the canonical
  continuous map obtained from rational-point comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- A given pullback of a monoid unit over a field has closed-immersion inclusion.
No object structure on the source or the supplied fibre is needed. -/
theorem groupSchemeKernel_isClosedImmersion
    {K : Type u} [Field K] {G H N : Scheme.{u}}
    (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K)) (fN : N ⟶ Spec (.of K))
    [MonObj (Over.mk fH)] (φ : Over.mk fG ⟶ Over.mk fH)
    (i : Over.mk fN ⟶ Over.mk fG)
    (hN : IsPullback i (toUnit (Over.mk fN)) φ η[Over.mk fH]) :
    IsClosedImmersion i.left := by
  let : IsClosedImmersion η[Over.mk fH].left :=
    isClosedImmersion_of_comp_eq_id fH η[Over.mk fH].left (by simpa using (η[Over.mk fH]).w)
  have h : IsPullback i.left fN φ.left η[Over.mk fH].left := by
    simpa using hN.map (Over.forget (Spec (.of K)))
  exact MorphismProperty.of_isPullback h.flip (inferInstance : IsClosedImmersion η[Over.mk fH].left)

variable {K : Type u} [Field K] [IsAlgClosed K] {G H N : Scheme.{u}}
variable (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K)) (fN : N ⟶ Spec (.of K))
variable [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
variable [gG : GrpObj (Over.mk fG)] [gH : GrpObj (Over.mk fH)]
variable [gN : GrpObj (Over.mk fN)]
variable (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]
variable (i : Over.mk fN ⟶ Over.mk fG) [IsMonHom i]
variable (hN : IsPullback i (toUnit (Over.mk fN)) φ η[Over.mk fH])

omit [IsAlgClosed K] [LocallyOfFiniteType fH] gG gN [IsMonHom φ] [IsMonHom i] in
include hN in
private theorem kernelLocallyOfFiniteType : LocallyOfFiniteType fN := by
  let : IsClosedImmersion i.left := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
  rw [← show i.left ≫ fG = fN from i.w]
  infer_instance

include hN in
/-- The range of the given kernel inclusion on closed points is the stock
kernel of the given homomorphism on closed points. -/
theorem groupSchemeClosedPointsMap_range_eq_ker :
    @MonoidHom.range (closedPoints N)
      (@groupSchemeClosedPointsGroup K _ N fN
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN)
      (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (↑(@groupSchemeClosedPointsMap K _ _ N G fN fG
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN gG i _)) =
    @MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
      (↑(groupSchemeClosedPointsMap fG fH φ)) := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  let : IsMonHom.Normal i := IsMonHom.Normal.of_isPullback_η φ hN
  have hr := IsMonHom.Normal.monoidHom_range_eq_ker_of_isPullback i φ hN
    (𝟙_ (Over (Spec (.of K))))
  ext x
  obtain ⟨q, rfl⟩ := (groupSchemePointEquivClosedPoint fG).surjective x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := (groupSchemePointEquivClosedPoint fN).surjective y
    change groupSchemeClosedPointsMap fN fG i
      (groupSchemePointEquivClosedPoint fN p) = groupSchemePointEquivClosedPoint fG q at hy
    have hp : p ≫ i = q := (groupSchemePointEquivClosedPoint fG).injective (by
      rwa [groupSchemeClosedPointsMap_apply_point] at hy)
    have hq : q ∈ (IsMonHom.monoidHom φ (𝟙_ (Over (Spec (.of K))))).ker := by
      rw [← hr]
      exact ⟨p, hp⟩
    change groupSchemeClosedPointsMap fG fH φ
      (groupSchemePointEquivClosedPoint fG q) = 1
    rw [groupSchemeClosedPointsMap_apply_point]
    change q ≫ φ = 1 at hq
    exact (congrArg (groupSchemePointEquivClosedPoint fH) hq).trans
      (groupSchemePointMulEquivClosedPoint fH).map_one
  · intro hx
    change groupSchemeClosedPointsMap fG fH φ
      (groupSchemePointEquivClosedPoint fG q) = 1 at hx
    have hq : q ∈ (IsMonHom.monoidHom φ (𝟙_ (Over (Spec (.of K))))).ker := by
      change q ≫ φ = 1
      apply (groupSchemePointMulEquivClosedPoint fH).injective
      simpa only [groupSchemePointMulEquivClosedPoint_apply,
        groupSchemeClosedPointsMap_apply_point, map_one] using hx
    rw [← hr] at hq
    obtain ⟨p, hp⟩ := hq
    refine ⟨groupSchemePointEquivClosedPoint fN p, ?_⟩
    change p ≫ i = q at hp
    change groupSchemeClosedPointsMap fN fG i
      (groupSchemePointEquivClosedPoint fN p) = groupSchemePointEquivClosedPoint fG q
    rw [groupSchemeClosedPointsMap_apply_point, hp]

/-- The closed-point kernel is closed in the original closed-point topology. -/
theorem groupSchemeClosedPointsMap_isClosed_ker :
    IsClosed (@MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
      (↑(groupSchemeClosedPointsMap fG fH φ)) : Set (closedPoints G)) := by
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  have hs : IsClosed ({(1 : closedPoints H).val} : Set H) := (1 : closedPoints H).property
  have hs' : IsClosed ({1} : Set (closedPoints H)) := by
    convert hs.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
  exact hs'.preimage (groupSchemeClosedPointsMap fG fH φ).continuous

include hN in
/-- The given kernel inclusion induces a closed embedding of closed-point spaces. -/
theorem groupSchemeKernelClosedPoints_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (@groupSchemeClosedPointsMap K _ _ N G fN fG
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN gG i _) := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let : IsClosedImmersion i.left := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
  have he : Topology.IsEmbedding (groupSchemeClosedPointsMap fN fG i) :=
    .of_comp (groupSchemeClosedPointsMap fN fG i).continuous continuous_subtype_val (by
      simpa only [Function.comp_def, groupSchemeClosedPointsMap_apply_value] using
        i.left.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  refine ⟨he, ?_⟩
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  change IsClosed ((↑(groupSchemeClosedPointsMap fN fG i) :
    closedPoints N →* closedPoints G).range : Set (closedPoints G))
  rw [groupSchemeClosedPointsMap_range_eq_ker fG fH fN φ i hN]
  exact groupSchemeClosedPointsMap_isClosed_ker fG fH φ

/-- The canonical continuous multiplicative comparison from the closed points of
a given scheme-theoretic kernel to the kernel of its closed-point homomorphism. -/
def groupSchemeKernelClosedPointsEquiv :
    @ContinuousMulEquiv (closedPoints N) inferInstance
      (@MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
        (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
        (↑(groupSchemeClosedPointsMap fG fH φ))) inferInstance
      (@groupSchemeClosedPointsGroup K _ N fN
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN).toMul inferInstance := by
  let : LocallyOfFiniteType fN := by
    let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
    rw [← show i.left ≫ fG = fN from i.w]
    infer_instance
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  let I := groupSchemeClosedPointsMap fN fG i
  have he := groupSchemeKernelClosedPoints_isClosedEmbedding fG fH fN φ i hN
  let e := (MonoidHom.ofInjective he.injective).trans
    (MulEquiv.subgroupCongr (groupSchemeClosedPointsMap_range_eq_ker fG fH fN φ i hN))
  have hi : Topology.IsInducing e := by
    exact he.isEmbedding.isInducing.codRestrict (fun x =>
      (groupSchemeClosedPointsMap_range_eq_ker fG fH fN φ i hN) ▸
        (show I x ∈ I.toMonoidHom.range from ⟨x, rfl⟩))
  exact ContinuousMulEquiv.mk' (e.toEquiv.toHomeomorphOfIsInducing hi) e.map_mul

/-- The comparison commutes with the given kernel inclusion. -/
@[simp]
theorem groupSchemeKernelClosedPointsEquiv_apply
    (x : closedPoints N) :
    (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN x).val =
      @groupSchemeClosedPointsMap K _ _ N G fN fG
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN gG i _ x := rfl

/-- On underlying scheme points, the comparison is the original inclusion. -/
theorem groupSchemeKernelClosedPointsEquiv_apply_value (x : closedPoints N) :
    (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN x).val.val = i.left x.val := by
  rw [groupSchemeKernelClosedPointsEquiv_apply, groupSchemeClosedPointsMap_apply_value]

/-- Applying the inverse comparison recovers the prescribed ambient closed point. -/
@[simp]
theorem groupSchemeKernelClosedPointsEquiv_symm_apply
    (y : @MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
      (↑(groupSchemeClosedPointsMap fG fH φ))) :
    @groupSchemeClosedPointsMap K _ _ N G fN fG
      (by
        let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
        rw [← show i.left ≫ fG = fN from i.w]
        infer_instance) _ gN gG i _
      ((@ContinuousMulEquiv.symm _ _ inferInstance inferInstance
        (@groupSchemeClosedPointsGroup K _ N fN
          (by
            let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
            rw [← show i.left ≫ fG = fN from i.w]
            infer_instance) _ gN).toMul inferInstance
        (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN)) y) = y.val := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  exact congrArg Subtype.val
    ((groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN).apply_symm_apply y)

/-- On scheme points, the inverse comparison is an inverse to the original inclusion. -/
theorem groupSchemeKernelClosedPointsEquiv_symm_apply_value
    (y : @MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
      (↑(groupSchemeClosedPointsMap fG fH φ))) :
    i.left ((@ContinuousMulEquiv.symm _ _ inferInstance inferInstance
        (@groupSchemeClosedPointsGroup K _ N fN
          (by
            let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
            rw [← show i.left ≫ fG = fN from i.w]
            infer_instance) _ gN).toMul inferInstance
        (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN)) y).val =
      y.val.val := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  have h := congrArg Subtype.val
    (groupSchemeKernelClosedPointsEquiv_symm_apply fG fH fN φ i hN y)
  simpa only [groupSchemeClosedPointsMap_apply_value] using h

/-- The comparison on rational points is postcomposition with the given inclusion. -/
theorem groupSchemeKernelClosedPointsEquiv_apply_point
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk fN) :
    (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN
      (@groupSchemePointEquivClosedPoint K _ N fN
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ p)).val = groupSchemePointEquivClosedPoint fG (p ≫ i) := by
  rw [groupSchemeKernelClosedPointsEquiv_apply, groupSchemeClosedPointsMap_apply_point]

/-- The inverse comparison is the lift in the original unit-pullback square.
The equality `hy` specifies the rational representative of the ambient closed point. -/
theorem groupSchemeKernelClosedPointsEquiv_symm_apply_point
    (y : @MonoidHom.ker (closedPoints G) (groupSchemeClosedPointsGroup fG)
      (closedPoints H) (groupSchemeClosedPointsGroup fH).toMulOneClass
      (↑(groupSchemeClosedPointsMap fG fH φ)))
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk fG)
    (hq : q ≫ φ = η[Over.mk fH])
    (hy : y.val = groupSchemePointEquivClosedPoint fG q) :
    (@ContinuousMulEquiv.symm _ _ inferInstance inferInstance
        (@groupSchemeClosedPointsGroup K _ N fN
          (by
            let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
            rw [← show i.left ≫ fG = fN from i.w]
            infer_instance) _ gN).toMul inferInstance
        (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN)) y =
      @groupSchemePointEquivClosedPoint K _ N fN
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ (hN.lift q (𝟙 _) (by simpa using hq)) := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  apply (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN).injective
  apply Subtype.ext
  rw [ContinuousMulEquiv.apply_symm_apply, groupSchemeKernelClosedPointsEquiv_apply_point,
    hN.lift_fst]
  exact hy

/-- The original unit corresponds to the unit of the closed-point kernel. -/
@[simp]
theorem groupSchemeKernelClosedPointsEquiv_unit :
    groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN
      (@groupSchemePointEquivClosedPoint K _ N fN
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ η[Over.mk fN]) = 1 := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  have hη : η[Over.mk fN] = (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk fN) := by
    simp [Hom.one_def]
  change groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN
    ((groupSchemePointMulEquivClosedPoint fN) η[Over.mk fN]) = 1
  rw [hη, map_one, map_one]

/-- The scheme-induced inverse agrees with inversion in the stock kernel. -/
theorem groupSchemeKernelClosedPointsEquiv_inv (x : closedPoints N) :
    (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN
      (groupSchemeInvClosedPointsHomeomorph fN x)).val =
      groupSchemeInvClosedPointsHomeomorph fG
        (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN x).val := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  simp only [groupSchemeInvClosedPointsHomeomorph_apply, map_inv, Subgroup.coe_inv]

include hN in
/-- A closed point is in the kernel precisely when it has a unique lift through
its original scheme-theoretic kernel inclusion. -/
theorem groupSchemeKernelClosedPoints_existsUnique (x : closedPoints G) :
    groupSchemeClosedPointsMap fG fH φ x =
      @One.one (closedPoints H) (groupSchemeClosedPointsGroup fH).toOne ↔
      ∃! y : closedPoints N, i.left y.val = x.val := by
  let : LocallyOfFiniteType fN := kernelLocallyOfFiniteType fG fH fN φ i hN
  let := groupSchemeClosedPointsGroup fN
  let := groupSchemeClosedPointsGroup fG
  let := groupSchemeClosedPointsGroup fH
  have he := groupSchemeKernelClosedPoints_isClosedEmbedding fG fH fN φ i hN
  constructor
  · intro hx
    let y := (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN).symm ⟨x, hx⟩
    have hyv : i.left y.val = x.val :=
      groupSchemeKernelClosedPointsEquiv_symm_apply_value fG fH fN φ i hN ⟨x, hx⟩
    refine ⟨y, hyv, ?_⟩
    intro z hz
    apply he.injective
    apply Subtype.ext
    simpa only [groupSchemeClosedPointsMap_apply_value] using hz.trans hyv.symm
  · rintro ⟨y, hy, -⟩
    have hv : (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN y).val = x := by
      apply Subtype.ext
      simpa only [groupSchemeKernelClosedPointsEquiv_apply_value] using hy
    have hx := (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN y).property
    change groupSchemeClosedPointsMap fG fH φ
      (groupSchemeKernelClosedPointsEquiv fG fH fN φ i hN y).val = 1 at hx
    rwa [hv] at hx

include hN in
/-- The range of the original kernel inclusion is closed, without a local-closedness premise. -/
theorem groupSchemeKernelClosedPoints_isClosed_range :
    IsClosed (Set.range
      (@groupSchemeClosedPointsMap K _ _ N G fN fG
        (by
          let := groupSchemeKernel_isClosedImmersion fG fH fN φ i hN
          rw [← show i.left ≫ fG = fN from i.w]
          infer_instance) _ gN gG i _)) :=
  (groupSchemeKernelClosedPoints_isClosedEmbedding fG fH fN φ i hN).isClosed_range

end AlgebraicGeometry
