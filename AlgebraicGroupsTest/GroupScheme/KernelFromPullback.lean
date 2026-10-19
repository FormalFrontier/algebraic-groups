/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Kernel
public import AlgebraicGroupsTest.GroupScheme.DiagonalKernel
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Group structures on scheme-theoretic kernel pullbacks

These uses compose the internal monoid limit construction with the group-object
extension on a kernel. The apex, structure map and inclusion are the supplied
scheme and arrows. Only the scheme pullback is an input; its monoid dictionary
and its slice pullback property are constructed here. The base is arbitrary and
the target is only a monoid object.

For the projection `D₂ → Gₘ` over `Spec ℤ`, the computed dictionary gives
a group of kernel points. The sections `(1, 1)` and `(1, -1)` are distinct,
the first is its group unit, and the original inclusion preserves the product
and inverse of these points.

## References

The group extension and its characteristic equations are from AlgebraicGroups.
The limit construction and slice infrastructure are from Mathlib, in particular
the work of Kim Morrison, Bhavik Mehta and Andrew Yang. This module was written
by Formal Frontier Agents with AI assistance.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

variable (S : Scheme.{u})
variable {G H : Over S} [GrpObj G] [MonObj H]
variable (f : G ⟶ H) [IsMonHom f]
variable {N : Scheme.{u}} (p : N ⟶ S) (i : N ⟶ G.left)
variable (hPB : IsPullback i p f.left (η[H]).left)

private def kernelInclusion : Over.mk p ⟶ G :=
  Over.homMk i (by
    calc
      i ≫ G.hom = i ≫ f.left ≫ H.hom := by rw [f.w]
      _ = p ≫ (η[H]).left ≫ H.hom := by
        rw [← Category.assoc, hPB.w, Category.assoc]
      _ = p := by rw [(η[H]).w]; exact Category.comp_id _)

private lemma kernelInclusion_left : (kernelInclusion S f p i hPB).left = i := rfl

private lemma kernelIsPullback :
    IsPullback (kernelInclusion S f p i hPB) (toUnit (Over.mk p)) f η[H] := by
  have w : kernelInclusion S f p i hPB ≫ f = toUnit (Over.mk p) ≫ η[H] := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, kernelInclusion_left, Over.toUnit_left,
      Over.mk_left, Over.mk_hom] using hPB.w
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
  apply isLimitOfIsLimitPullbackConeMap (Over.forget S) w
  exact hPB.isLimit

private def kernelDiagram : WalkingCospan ⥤ Mon (Over S) :=
  cospan (Mon.ofHom f) (Mon.ofHom η[H])

private def kernelCone : Cone (kernelDiagram S f ⋙ Mon.forget (Over S)) :=
  (Cone.postcompose
    (cospanCompIso (Mon.forget (Over S)) (Mon.ofHom f) (Mon.ofHom η[H])).inv).obj
      (kernelIsPullback S f p i hPB).cone

private def kernelConeIsLimit : IsLimit (kernelCone S f p i hPB) :=
  (IsLimit.postcomposeInvEquiv
    (cospanCompIso (Mon.forget (Over S)) (Mon.ofHom f) (Mon.ofHom η[H]))
      (kernelIsPullback S f p i hPB).cone).symm
        (kernelIsPullback S f p i hPB).isLimit

private def kernelLimit : Mon (Over S) :=
  Mon.limit (kernelDiagram S f) (kernelCone S f p i hPB)
    (kernelConeIsLimit S f p i hPB)

private def kernelMonoid : MonObj (Over.mk p) :=
  (kernelLimit S f p i hPB).mon

private def kernelLimitCone : Cone (kernelDiagram S f) :=
  Mon.limitCone (kernelDiagram S f) (kernelCone S f p i hPB)
    (kernelConeIsLimit S f p i hPB)

private lemma kernelLimitCone_component (j : WalkingCospan) :
    ((kernelLimitCone S f p i hPB).π.app j).hom =
      (kernelIsPullback S f p i hPB).cone.π.app j ≫
        (cospanCompIso (Mon.forget (Over S)) (Mon.ofHom f)
          (Mon.ofHom η[H])).inv.app j := rfl

private lemma kernelLimitCone_left :
    ((kernelLimitCone S f p i hPB).π.app .left).hom =
      kernelInclusion S f p i hPB := by
  have h : (cospanCompIso (Mon.forget (Over S)) (Mon.ofHom f)
      (Mon.ofHom η[H])).inv.app .left = 𝟙 G :=
    cospanCompIso_inv_app_left _ _ _
  exact (kernelLimitCone_component S f p i hPB .left).trans
    ((congrArg (fun k : G ⟶ G =>
      (kernelIsPullback S f p i hPB).cone.π.app .left ≫ k) h).trans
        ((Category.comp_id _).trans (kernelIsPullback S f p i hPB).cone_fst))

private lemma kernelLimitCone_right :
    ((kernelLimitCone S f p i hPB).π.app .right).hom = toUnit (Over.mk p) := by
  have h : (cospanCompIso (Mon.forget (Over S)) (Mon.ofHom f)
      (Mon.ofHom η[H])).inv.app .right = 𝟙 (𝟙_ (Over S)) :=
    cospanCompIso_inv_app_right _ _ _
  exact (kernelLimitCone_component S f p i hPB .right).trans
    ((congrArg (fun k : (𝟙_ (Over S)) ⟶ (𝟙_ (Over S)) =>
      (kernelIsPullback S f p i hPB).cone.π.app .right ≫ k) h).trans
        ((Category.comp_id _).trans (kernelIsPullback S f p i hPB).cone_snd))

private lemma kernelInclusion_isMonHom :
    @IsMonHom (Over S) _ _ (Over.mk p) G (kernelMonoid S f p i hPB)
      inferInstance (kernelInclusion S f p i hPB) := by
  rw [← kernelLimitCone_left S f p i hPB]
  exact ((kernelLimitCone S f p i hPB).π.app .left).isMonHom_hom

private lemma kernelToUnit_isMonHom :
    @IsMonHom (Over S) _ _ (Over.mk p) (𝟙_ (Over S)) (kernelMonoid S f p i hPB)
      inferInstance (toUnit (Over.mk p)) := by
  rw [← kernelLimitCone_right S f p i hPB]
  exact ((kernelLimitCone S f p i hPB).π.app .right).isMonHom_hom

private def kernelGrpObj : GrpObj (Over.mk p) := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact GrpObj.ofIsPullback f (kernelInclusion S f p i hPB)
    (kernelIsPullback S f p i hPB)

private lemma kernelGrpObj_toMonObj :
    (kernelGrpObj S f p i hPB).toMonObj = (kernelLimit S f p i hPB).mon := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact GrpObj.ofIsPullback_toMonObj f (kernelInclusion S f p i hPB)
    (kernelIsPullback S f p i hPB)

private def kernelProjection :
    Grp.mk (grp := kernelGrpObj S f p i hPB) (Over.mk p) ⟶ Grp.mk G := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact GrpObj.ofIsPullbackHom f (kernelInclusion S f p i hPB)
    (kernelIsPullback S f p i hPB)

private lemma kernelProjection_hom :
    (kernelProjection S f p i hPB).hom.hom = kernelInclusion S f p i hPB := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact GrpObj.ofIsPullbackHom_hom f (kernelInclusion S f p i hPB)
    (kernelIsPullback S f p i hPB)

private lemma kernelProjection_isMonHom :
    @IsMonHom (Over S) _ _ (Over.mk p) G (kernelGrpObj S f p i hPB).toMonObj
      inferInstance (kernelInclusion S f p i hPB) := by
  rw [← kernelProjection_hom S f p i hPB]
  exact (kernelProjection S f p i hPB).hom.isMonHom_hom

private lemma kernel_inverse_comp :
    (kernelGrpObj S f p i hPB).inv ≫ kernelInclusion S f p i hPB =
      kernelInclusion S f p i hPB ≫ ι[G] := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact GrpObj.ofIsPullback_inv_comp f (kernelInclusion S f p i hPB)
    (kernelIsPullback S f p i hPB)

private lemma kernel_inverse_left_comp :
    (kernelGrpObj S f p i hPB).inv.left ≫ i = i ≫ (ι[G]).left := by
  simpa only [Over.comp_left, kernelInclusion_left] using
    congrArg (fun k : Over.mk p ⟶ G => k.left) (kernel_inverse_comp S f p i hPB)

private lemma kernel_one_comp :
    (kernelMonoid S f p i hPB).one ≫ kernelInclusion S f p i hPB = η[G] := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact IsMonHom.one_hom (kernelInclusion S f p i hPB)

private lemma kernel_one_toUnit :
    (kernelMonoid S f p i hPB).one ≫ toUnit (Over.mk p) = 𝟙 (𝟙_ (Over S)) := by
  letI := kernelMonoid S f p i hPB
  letI := kernelToUnit_isMonHom S f p i hPB
  exact IsMonHom.one_hom (toUnit (Over.mk p))

private lemma kernel_mul_comp :
    (kernelMonoid S f p i hPB).mul ≫ kernelInclusion S f p i hPB =
      (kernelInclusion S f p i hPB ⊗ₘ kernelInclusion S f p i hPB) ≫ μ[G] := by
  letI := kernelMonoid S f p i hPB
  letI := kernelInclusion_isMonHom S f p i hPB
  exact IsMonHom.mul_hom (kernelInclusion S f p i hPB)

private lemma kernel_mul_toUnit :
    (kernelMonoid S f p i hPB).mul ≫ toUnit (Over.mk p) =
      toUnit (Over.mk p ⊗ Over.mk p) :=
  isTerminalTensorUnit.hom_ext _ _

private lemma kernelUnitSquare :
    (η[G]).left ≫ f.left = (𝟙 S) ≫ (η[H]).left := by
  simpa only [Over.comp_left, Category.id_comp] using
    congrArg (fun k : 𝟙_ (Over S) ⟶ H => k.left) (IsMonHom.one_hom f)

private lemma kernel_one_left :
    (kernelMonoid S f p i hPB).one.left =
      hPB.lift (η[G]).left (𝟙 S) (kernelUnitSquare S f) := by
  apply hPB.hom_ext
  · rw [hPB.lift_fst]
    simpa only [Over.comp_left, kernelInclusion_left] using
      congrArg (fun k : 𝟙_ (Over S) ⟶ G => k.left) (kernel_one_comp S f p i hPB)
  · rw [hPB.lift_snd]
    simpa only [Over.comp_left, Over.toUnit_left, Over.id_left,
      Over.mk_hom, Over.tensorUnit_left] using
      congrArg (fun k : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) => k.left)
        (kernel_one_toUnit S f p i hPB)

private lemma kernelGrpObj_one_left :
    (kernelGrpObj S f p i hPB).toMonObj.one.left =
      hPB.lift (η[G]).left (𝟙 S) (kernelUnitSquare S f) := by
  rw [kernelGrpObj_toMonObj]
  exact kernel_one_left S f p i hPB

section Boundaries

variable (G : Over S) [GrpObj G]
variable {N : Scheme.{u}} (p : N ⟶ S) (i : N ⟶ G.left)

-- For an identity arrow, the produced projection is the original source unit.
example (hPB : IsPullback i p (𝟙 G.left) (η[G]).left) :
    IsIso p ∧
      (kernelProjection S (𝟙 G) p i hPB).hom.hom.left = p ≫ (η[G]).left := by
  rw [kernelProjection_hom, kernelInclusion_left]
  exact ⟨hPB.isIso_snd_of_isIso, by simpa only [Category.comp_id] using hPB.w⟩

-- For a terminal target, the produced projection is an isomorphism.
example (hPB : IsPullback i p G.hom (𝟙 S)) :
    IsIso (kernelProjection S (toUnit G) p i hPB).hom.hom.left ∧
      p = (kernelProjection S (toUnit G) p i hPB).hom.hom.left ≫ G.hom := by
  have hp : (kernelProjection S (toUnit G) p i hPB).hom.hom.left = i :=
    (congrArg (fun k : Over.mk p ⟶ G => k.left)
      (kernelProjection_hom S (toUnit G) p i hPB)).trans
        (kernelInclusion_left S (toUnit G) p i hPB)
  refine ⟨hp.symm ▸ hPB.isIso_fst_of_isIso, ?_⟩
  exact (show p = i ≫ G.hom from by
    simpa only [Category.comp_id] using hPB.w.symm).trans
      (congrArg (fun k : N ⟶ G.left => k ≫ G.hom) hp.symm)

end Boundaries

-- A supplied unit pullback retains its original apex and has equal projections.
example (H : Over S) [MonObj H] {N : Scheme.{u}} (p i : N ⟶ S)
    (hPB : IsPullback i p (η[H]).left (η[H]).left) :
    IsIso p ∧ (kernelProjection S η[H] p i hPB).hom.hom.left = p := by
  haveI : Mono (η[H]).left := ⟨by
    intro Z a b h
    have h' := congrArg (fun k => k ≫ H.hom) h
    simpa only [Category.assoc, (η[H]).w, Over.tensorUnit_hom,
      Over.tensorUnit_left, Category.comp_id] using h'⟩
  rw [kernelProjection_hom, kernelInclusion_left]
  exact ⟨hPB.isIso_snd_iso_of_mono, (cancel_mono (η[H]).left).mp hPB.w⟩

section IntegerDiagonal

private abbrev integerKernelBase : Scheme := Spec (.of ℤ)
private abbrev integerKernelDomain : Over integerKernelBase :=
  integerKernelBase.asOver integerKernelBase
private abbrev integerKernelSource := diagonalGroupScheme ℤ (Fin 2)
private abbrev integerKernelTarget := (multiplicativeGroupScheme ℤ).toMon

local instance : GrpObj (diagonalGroupScheme ℤ (Fin 2)).X :=
  (diagonalGroupScheme ℤ (Fin 2)).grp
local instance : MonObj (multiplicativeGroupScheme ℤ).toMon.X :=
  (multiplicativeGroupScheme ℤ).toMon.mon

private abbrev integerKernelMap : integerKernelSource.X ⟶ integerKernelTarget.X :=
  (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom

private theorem integerKernelMap_isMonHom : IsMonHom integerKernelMap :=
  (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.isMonHom_hom

attribute [local instance] integerKernelMap_isMonHom

private abbrev integerKernel : Scheme :=
  pullback integerKernelMap.left (η[integerKernelTarget.X]).left
private abbrev integerKernelP : integerKernel ⟶ integerKernelBase :=
  pullback.snd integerKernelMap.left (η[integerKernelTarget.X]).left
private abbrev integerKernelI : integerKernel ⟶ integerKernelSource.X.left :=
  pullback.fst integerKernelMap.left (η[integerKernelTarget.X]).left
private abbrev integerKernelSquare :
    IsPullback integerKernelI integerKernelP integerKernelMap.left
      (η[integerKernelTarget.X]).left :=
  IsPullback.of_hasPullback _ _
private abbrev integerKernelOver : Over integerKernelBase := Over.mk integerKernelP

-- Install the computed group on the original scheme pullback before using its points.
private instance integerKernelGrpObj : GrpObj integerKernelOver :=
  kernelGrpObj integerKernelBase integerKernelMap integerKernelP integerKernelI
    integerKernelSquare

private abbrev integerKernelInclusion : integerKernelOver ⟶ integerKernelSource.X :=
  kernelInclusion integerKernelBase integerKernelMap integerKernelP integerKernelI
    integerKernelSquare

private theorem integerKernelInclusion_isMonHom : IsMonHom integerKernelInclusion :=
  kernelProjection_isMonHom integerKernelBase integerKernelMap integerKernelP integerKernelI
    integerKernelSquare

attribute [local instance] integerKernelInclusion_isMonHom

private abbrev integerKernelPositive : integerKernelDomain ⟶ integerKernelOver :=
  Over.homMk
    (pullback.lift
      (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)).left
      (𝟙 _) diagonalGroup_integerPoints_squares.1)
    (by exact (pullback.lift_snd _ _ _).trans integerSpec_asOver_hom.symm)

private abbrev integerKernelNegative : integerKernelDomain ⟶ integerKernelOver :=
  Over.homMk
    (pullback.lift
      (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
        (fun k => if k = 0 then 1 else -1)).left
      (𝟙 _) diagonalGroup_integerPoints_squares.2)
    (by exact (pullback.lift_snd _ _ _).trans integerSpec_asOver_hom.symm)

private lemma integerKernelPositive_comp :
    integerKernelPositive ≫ integerKernelInclusion =
      diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

private lemma integerKernelNegative_comp :
    integerKernelNegative ≫ integerKernelInclusion =
      diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
        (fun k => if k = 0 then 1 else -1) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

-- The two points are distinct; the all-one lift is the unit of the computed Hom group.
example : integerKernelPositive ≠ integerKernelNegative ∧
    integerKernelPositive = (1 : integerKernelDomain ⟶ integerKernelOver) := by
  have hpoints := diagonalKernel_integerPoints integerKernel integerKernelI integerKernelP
    integerKernelSquare
  have hchosen := diagonalKernel_integerPoints_pullback
  constructor
  · intro h
    exact hchosen.2.2.2.2.1
      (congrArg (fun q : integerKernelDomain ⟶ integerKernelOver => q.left) h)
  · apply Over.OverMorphism.ext
    have h : integerKernelPositive.left =
        (kernelGrpObj integerKernelBase integerKernelMap integerKernelP integerKernelI
          integerKernelSquare).toMonObj.one.left :=
      hchosen.2.2.2.2.2.1.trans
        (hpoints.2.2.2.2.2.2.2.2.trans
          (kernelGrpObj_one_left integerKernelBase integerKernelMap integerKernelP
            integerKernelI integerKernelSquare).symm)
    simp only [Hom.one_def, Over.comp_left, Over.toUnit_left,
      integerSpec_asOver_hom, Over.tensorUnit_left]
    exact h.trans (Category.id_comp _).symm

-- Multiplication uses the stored monoid and its original monoid-hom projection.
example : (integerKernelPositive * integerKernelNegative) ≫ integerKernelInclusion =
    (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)) *
      (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
        (fun k => if k = 0 then 1 else -1)) := by
  rw [MonObj.mul_comp, integerKernelPositive_comp, integerKernelNegative_comp]

-- The produced inverse is consumed on the negative integer point, not assumed on the apex.
example : integerKernelNegative⁻¹ ≫ integerKernelInclusion =
    (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
      (fun k => if k = 0 then 1 else -1))⁻¹ := by
  calc
    integerKernelNegative⁻¹ ≫ integerKernelInclusion =
        integerKernelNegative ≫
          ((kernelGrpObj integerKernelBase integerKernelMap integerKernelP integerKernelI
            integerKernelSquare).inv ≫ integerKernelInclusion) := by
      rw [Hom.inv_def, Category.assoc]
    _ = integerKernelNegative ≫ (integerKernelInclusion ≫ ι[integerKernelSource.X]) := by
      rw [kernel_inverse_comp]
    _ = (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
        (fun k => if k = 0 then 1 else -1))⁻¹ := by
      rw [← Category.assoc, integerKernelNegative_comp, Hom.inv_def]

end IntegerDiagonal

end AlgebraicGeometry
