/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Separated group schemes

This file proves that a group scheme is separated when its unit section is a
closed immersion. In particular, every group scheme over a field is separated.

The closed-unit-section criterion is relative to an arbitrary base scheme;
the field case needs no finite-type hypothesis.

## Main results

- `AlgebraicGeometry.isSeparated_of_isClosedImmersion_unit`
- `AlgebraicGeometry.isSeparated_of_grpObj`

## References

- James S. Milne, *Algebraic Groups* (2017), Proposition 1.22 and
  Appendix A.41: the field-based result and the diagonal-as-inverse-image
  argument for separatedness.
- Mathlib, `IsSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.Separated`),
  `MorphismProperty.of_isPullback` and
  `isClosedImmersion_of_comp_eq_id`: the diagonal criterion, pullback stability
  of closed immersions and the closed-unit-section step over a field.
- Mathlib, `IsPullback.of_isLimit_binaryFan_of_isTerminal`,
  `IsPullback.of_right` and `Functor.map_isPullback`: the product pullback,
  pullback pasting and preservation by the over-category forgetful functor.
- Mathlib, `GrpObj.eq_lift_inv_left` and `GrpObj.lift_inv_left_eq`
  (`Mathlib.CategoryTheory.Monoidal.Grp`): the identities proving
  that categorical left division is an isomorphism.
-/

public section

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

variable {K : Type u} [Field K]

/-- Every group scheme over a field is separated, with no finite-type
assumption; this is Milne, *Algebraic Groups* (2017), Proposition 1.22 with
the finite-type hypothesis removed. -/
theorem isSeparated_of_grpObj (G : Over (Spec (.of K))) [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_isClosedImmersion_unit G <|
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom η[G].left (by simp)

end AlgebraicGeometry
