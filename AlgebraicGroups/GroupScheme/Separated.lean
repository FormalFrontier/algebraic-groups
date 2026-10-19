/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.KernelTorsor
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Separated group schemes

This file proves that a group scheme is separated when its unit section is a
closed immersion. In particular, every group scheme over a base whose underlying
space has at most one point is separated, including every field base.

The closed-unit-section criterion is relative to an arbitrary base scheme.
The at-most-one-point result needs neither finite type nor reducedness, and
allows the empty base. For a monoid morphism from a relative group scheme to a
relative monoid scheme, the kernel-unit criterion relates separatedness to the
canonical section of the pullback over the target unit. This is the whole
scheme-theoretic unit fibre, not a reduced or geometric fibre.

## Main results

- `AlgebraicGeometry.isSeparated_of_isClosedImmersion_unit`
- `AlgebraicGeometry.isSeparated_of_grpObj_of_subsingleton`
- `AlgebraicGeometry.isSeparated_of_grpObj`
- `AlgebraicGeometry.isSeparated_iff_isClosedImmersion_kernelUnit`

## References

- James S. Milne, *Algebraic Groups* (2017), Proposition 1.22 and
  Appendix A.41: the field-based result and the diagonal-as-inverse-image
  argument for separatedness.
- Mathlib, `IsSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.Separated`),
  `MorphismProperty.of_isPullback` and
  `isClosedImmersion_of_comp_eq_id`: the diagonal criterion, pullback stability
  of closed immersions and the closed-unit-section step over a base with at most
  one point.
- Mathlib, `IsPullback.of_isLimit_binaryFan_of_isTerminal`,
  `IsPullback.of_right` and `Functor.map_isPullback`: the product pullback,
  pullback pasting and preservation by the over-category forgetful functor.
- `CategoryTheory.GrpObj.isPullback_kernel_mul` in
  `AlgebraicGroups.GroupObject.KernelTorsor`: the kernel-pair orientation
  `(n, g) ↦ (i(n)g, g)` for a group source and monoid target.
- Mathlib, `GrpObj.eq_lift_inv_left` and `GrpObj.lift_inv_left_eq`
  (`Mathlib.CategoryTheory.Monoidal.Grp`): the identities proving
  that categorical left division is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The automorphism `(x, y) ↦ (x, x⁻¹y)` of the product of a group object with
itself. It implements the diagonal-to-unit argument of Milne,
*Algebraic Groups* (2017), Proposition 1.22 in a Cartesian category. -/
def leftDivIso (G : C) [GrpObj G] : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G) (lift (fst G G ≫ ι) (snd G G) ≫ μ)
  inv := lift (fst G G) (lift (fst G G) (snd G G) ≫ μ)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst, lift_snd]
      rw [← GrpObj.eq_lift_inv_left]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc]
      simp only [lift_fst_assoc, lift_snd]
      rw [GrpObj.lift_inv_left_eq]

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- A group scheme whose unit section is a closed immersion is separated.
This generalizes the argument of Milne, *Algebraic Groups* (2017),
Proposition 1.22: after categorical left division the diagonal is a base
change of the unit section. -/
theorem isSeparated_of_isClosedImmersion_unit (G : Over S) [GrpObj G]
    (hunit : IsClosedImmersion η[G].left) : IsSeparated G.hom := by
  constructor
  change IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left
  have hprod (X Y : Over S) : IsPullback (fst X Y) (snd X Y)
      (toUnit X) (toUnit Y) :=
    .of_isLimit_binaryFan_of_isTerminal (tensorProductIsBinaryProduct X Y)
      isTerminalTensorUnit
  have hi : IsPullback (G ◁ η[G]) (snd G (𝟙_ (Over S))) (snd G G) η[G] := by
    refine IsPullback.of_right ?_ (whiskerLeft_snd G η[G]) (hprod G G)
    simpa only [whiskerLeft_fst, comp_toUnit] using hprod G (𝟙_ (Over S))
  have hη : IsClosedImmersion (G ◁ η[G]).left :=
    MorphismProperty.of_isPullback ((Over.forget S).map_isPullback hi.flip) hunit
  rw [show lift (𝟙 G) (𝟙 G) =
      (ρ_ G).inv ≫ (G ◁ η[G]) ≫ (GrpObj.leftDivIso G).inv by
    ext <;> simp [GrpObj.leftDivIso]]
  dsimp only [Over.comp_left]
  have hρ : IsClosedImmersion (ρ_ G).inv.left := by
    change IsClosedImmersion ((Over.forget _).mapIso (ρ_ G)).inv
    infer_instance
  have hdiv : IsClosedImmersion (GrpObj.leftDivIso G).inv.left := by
    change IsClosedImmersion ((Over.forget _).mapIso (GrpObj.leftDivIso G)).inv
    infer_instance
  have hηdiv : IsClosedImmersion ((G ◁ η[G]).left ≫ (GrpObj.leftDivIso G).inv.left) :=
    @IsClosedImmersion.comp _ _ _ _ _ hη hdiv
  exact @IsClosedImmersion.comp _ _ _ _ _ hρ hηdiv

/-- A monoid morphism from a group scheme to a monoid scheme over any base is
separated exactly when the canonical unit section of its scheme-theoretic kernel
is a closed immersion. The kernel is `pullback q η[Q]` in `Over S`, and its unit
is the displayed pullback lift, not the ambient unit `η[G]`.

The kernel-pair description is `GrpObj.isPullback_kernel_mul`; the geometric
translation is the relative analogue of the diagonal-to-unit argument in
Milne, *Algebraic Groups* (2017), Proposition 1.22 and Appendix A.41. -/
theorem isSeparated_iff_isClosedImmersion_kernelUnit {G Q : Over S}
    [GrpObj G] [MonObj Q] (q : G ⟶ Q) [IsMonHom q] :
    IsSeparated q.left ↔ IsClosedImmersion
      (pullback.lift (f := q) (g := η[Q]) η[G] (𝟙 (𝟙_ (Over S)))
        (by simpa only [Category.id_comp] using IsMonHom.one_hom q)).left := by
  let N : Over S := pullback q η[Q]
  let i : N ⟶ G := pullback.fst q η[Q]
  let κ : 𝟙_ (Over S) ⟶ N :=
    pullback.lift (f := q) (g := η[Q]) η[G] (𝟙 (𝟙_ (Over S)))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)
  change IsSeparated q.left ↔ IsClosedImmersion κ.left
  have hpb := IsPullback.of_hasPullback q η[Q]
  constructor
  · intro hq
    have : IsSeparated (pullback.snd q η[Q]).left :=
      MorphismProperty.of_isPullback ((Over.forget S).map_isPullback hpb) hq
    have hκp : κ.left ≫ (pullback.snd q η[Q]).left = 𝟙 (𝟙_ (Over S)).left := by
      change (κ ≫ pullback.snd q η[Q]).left =
        (𝟙 (𝟙_ (Over S)) : (𝟙_ (Over S)) ⟶ (𝟙_ (Over S))).left
      simp only [κ, pullback.lift_snd]
    have : IsClosedImmersion (κ.left ≫ (pullback.snd q η[Q]).left) := by
      rw [hκp]
      infer_instance
    exact IsClosedImmersion.of_comp κ.left (pullback.snd q η[Q]).left
  · intro hκ
    have hN : IsPullback i (toUnit N) q η[Q] := by
      simpa only [show pullback.snd q η[Q] = toUnit N from toUnit_unique _ _] using hpb
    let j : G ⟶ N ⊗ G := lift (toUnit G ≫ κ) (𝟙 G)
    have hprod (X Y : Over S) : IsPullback (fst X Y) (snd X Y)
        (toUnit X) (toUnit Y) :=
      .of_isLimit_binaryFan_of_isTerminal (tensorProductIsBinaryProduct X Y)
        isTerminalTensorUnit
    have hj : IsPullback j (toUnit G) (fst N G) κ := by
      refine IsPullback.of_right ?_ (by simp only [j, lift_fst]) (hprod N G).flip
      simpa only [j, lift_snd, comp_toUnit, toUnit_unit] using
        (IsPullback.id_horiz (toUnit G))
    have hjc : IsClosedImmersion j.left :=
      MorphismProperty.of_isPullback ((Over.forget S).map_isPullback hj.flip) hκ
    have hjmul : j ≫ (i ⊗ₘ 𝟙 G) ≫ μ[G] = 𝟙 G := by
      simp only [j, lift_map_assoc, Category.comp_id, Category.assoc, κ, i,
        pullback.lift_fst, MonObj.lift_comp_one_left]
    have hjsnd : j ≫ snd N G = 𝟙 G := by simp only [j, lift_snd]
    have hpair : IsPullback ((i ⊗ₘ 𝟙 G) ≫ μ[G]).left
        (snd N G).left q.left q.left :=
      (Over.forget S).map_isPullback (GrpObj.isPullback_kernel_mul i q hN)
    let e : (N ⊗ G).left ≅ pullback q.left q.left := hpair.isoPullback
    have hdiag : j.left ≫ e.hom = pullback.diagonal q.left := by
      apply pullback.hom_ext
      · simp only [Category.assoc, e, IsPullback.isoPullback_hom_fst,
          pullback.diagonal_fst]
        simpa only [← Over.comp_left, Over.id_left] using
          congrArg (fun f : G ⟶ G => f.left) hjmul
      · simp only [Category.assoc, e, IsPullback.isoPullback_hom_snd,
          pullback.diagonal_snd]
        simpa only [← Over.comp_left, Over.id_left] using
          congrArg (fun f : G ⟶ G => f.left) hjsnd
    constructor
    rw [← hdiag]
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
      j.left e.hom).2 hjc

/-- Every group scheme over a base whose underlying space has at most one point
is separated. This extends the field statement of Milne, *Algebraic Groups*
(2017), Proposition 1.22, using Mathlib's closed-immersion theorem for sections
over a subsingleton base. No finite-type or reducedness assumption is needed. -/
theorem isSeparated_of_grpObj_of_subsingleton [Subsingleton S]
    (G : Over S) [GrpObj G] : IsSeparated G.hom := by
  have : Subsingleton (𝟙_ (Over S)).left := by
    simpa only [Over.tensorUnit_left] using (inferInstance : Subsingleton S)
  exact isSeparated_of_isClosedImmersion_unit G <|
    isClosedImmersion_of_comp_eq_id (toUnit G).left η[G].left (by
      simpa only [Over.tensorUnit_left, Over.toUnit_left, Over.tensorUnit_hom] using Over.w η[G])

variable {K : Type u} [Field K]

/-- Every group scheme over a field is separated, with no finite-type
assumption; this is Milne, *Algebraic Groups* (2017), Proposition 1.22 with
the finite-type hypothesis removed. -/
theorem isSeparated_of_grpObj (G : Over (Spec (.of K))) [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_grpObj_of_subsingleton G

end AlgebraicGeometry
