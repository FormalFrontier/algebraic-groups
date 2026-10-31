/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.FamilyTranslation
public import SchemeProperties.FlatSourceCancellation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Flatness from a family in a group scheme

Let `f : G ⟶ H` be a homomorphism of group objects over a scheme `S`. If `G` is
flat over `S`, and `i : P ⟶ G` is a family with `P` flat and surjective over `S`
and `i ≫ f` flat, then `f` is flat. The parameter `P` need not be a group object,
and no flatness assumption on `i` or on `H` over `S` is required.

The left family translation makes the second projection from `P ⊗ G` into a
flat surjective cover of `G`. The composite of this cover with `f` factors as
the base change of `i ≫ f`, followed by a right family translation and the
first projection from `H ⊗ G`. Both factors are flat. Flatness then descends
through the cover. The order of multiplication is `f(i(p)) * f(g)` throughout;
commutativity is not needed.

## Implementation notes

The products and group structures use the supplied Cartesian monoidal
structure on `Over S`. Their projections give scheme pullback squares by the
product universal property. The tensor-map pullback follows by cancellation
of the right product square.

## References

* `AlgebraicGroups.GroupObject.FamilyTranslation`, for family translations and
  their factorization under a group-object morphism.
* Mathlib's `Over.isPullback_of_binaryFan_isLimit` and `IsPullback.of_right`,
  for the pullback squares of the given products and tensor map.
* `AlgebraicGeometry.Flat.of_comp` in
  `SchemeProperties.FlatSourceCancellation`, for descent through a flat
  surjective source morphism without quasi-compactness.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Flat

/-- A group-object homomorphism is flat if its composite with a parameter
family is flat, the parameter is flat and surjective over the base, and the
source group object is flat over the base. The family needs neither a group
structure on its parameter nor flatness of its map into the source. -/
theorem of_group_hom_family
    {S : Scheme.{u}} [c : CartesianMonoidalCategory (Over S)]
    (G H : Over S) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f]
    (P : Over S) (i : P ⟶ G)
    [Flat P.hom] [Surjective P.hom] [Flat G.hom] [Flat (i ≫ f).left] :
    Flat f.left := by
  let q : P ⊗ G ⟶ G := (GrpObj.mulLeftFamily i).hom ≫ snd P G
  let a : P ⊗ G ⟶ H ⊗ G := (i ≫ f) ⊗ₘ 𝟙 G
  let b : H ⊗ G ⟶ H := (GrpObj.mulRightFamily f).hom ≫ fst H G
  have hPG : IsPullback (fst P G).left (snd P G).left P.hom G.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst P G) (snd P G)) (tensorProductIsBinaryProduct P G)
  have hHG : IsPullback (fst H G).left (snd H G).left H.hom G.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst H G) (snd H G)) (tensorProductIsBinaryProduct H G)
  have : Flat (snd P G).left :=
    MorphismProperty.of_isPullback hPG inferInstance
  have : Surjective (snd P G).left :=
    MorphismProperty.of_isPullback hPG inferInstance
  have : Flat (fst H G).left :=
    MorphismProperty.of_isPullback hHG.flip inferInstance
  have hfst : a.left ≫ (fst H G).left = (fst P G).left ≫ (i ≫ f).left := by
    simpa only [a, Over.comp_left] using
      congrArg (fun k : P ⊗ G ⟶ H => k.left) (tensorHom_fst (i ≫ f) (𝟙 G))
  have hsnd : a.left ≫ (snd H G).left = (snd P G).left := by
    simpa only [a, Over.comp_left, Over.id_left, Category.comp_id] using
      congrArg (fun k : P ⊗ G ⟶ G => k.left) (tensorHom_snd (i ≫ f) (𝟙 G))
  have hOuter : IsPullback (a.left ≫ (snd H G).left) (fst P G).left
      G.hom ((i ≫ f).left ≫ H.hom) := by
    simpa only [hsnd, Over.w] using hPG.flip
  have ha : IsPullback (fst P G).left a.left (i ≫ f).left (fst H G).left :=
    (hOuter.of_right hfst hHG.flip).flip
  have : Flat a.left := MorphismProperty.of_isPullback ha inferInstance
  have : IsIso (GrpObj.mulLeftFamily i).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.mulLeftFamily i).hom))
  have : IsIso (GrpObj.mulRightFamily f).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.mulRightFamily f).hom))
  have : Flat q.left :=
    inferInstanceAs (Flat ((GrpObj.mulLeftFamily i).hom.left ≫ (snd P G).left))
  have : Surjective q.left :=
    inferInstanceAs (Surjective ((GrpObj.mulLeftFamily i).hom.left ≫ (snd P G).left))
  have : Flat b.left :=
    inferInstanceAs (Flat ((GrpObj.mulRightFamily f).hom.left ≫ (fst H G).left))
  have hfactor : q ≫ f = a ≫ b := by
    simpa only [q, a, b, Category.assoc] using
      GrpObj.mulLeftFamily_hom_comp_snd_comp i f
  have hleft : q.left ≫ f.left = a.left ≫ b.left :=
    congrArg (fun k : P ⊗ G ⟶ H => k.left) hfactor
  have : Flat (q.left ≫ f.left) := by
    rw [hleft]
    infer_instance
  exact Flat.of_comp q.left f.left

end AlgebraicGeometry.Flat
