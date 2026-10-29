/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Stabilizer
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Stabilizers over a scheme

The underlying scheme of a stabilizer in `Over S` is canonically isomorphic to
its orbit fibre. Its inclusion is closed when the section is closed, in
particular when the action space is separated over `S`.

These geometric statements only need a monoid action. For a group action, the
generic stabilizer equivalence applies to every test `S`-scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory AlgebraicGeometry

namespace CategoryTheory.ModObj

variable {S : Scheme.{u}} (G : Over S) {X : Over S}
variable [MonObj G] [ModObj G X] (x : 𝟙_ (Over S) ⟶ X)

/-- The stabilizer fibre square remains a pullback on underlying schemes. -/
theorem stabilizerUnderlyingIsPullback :
    IsPullback (stabilizerι G x).left (stabilizer G x).hom (orbitMap G x).left x.left := by
  simpa using (stabilizerIsPullback (G := G) x).map (Over.forget S)

/-- The canonical comparison with the underlying scheme-theoretic orbit fibre. -/
def stabilizerUnderlyingIso :
    (stabilizer G x).left ≅ pullback (orbitMap G x).left x.left :=
  (stabilizerUnderlyingIsPullback G x).isoPullback

/-- The comparison identifies the first projection with the stabilizer inclusion. -/
@[reassoc (attr := simp)]
theorem stabilizerUnderlyingIso_hom_fst :
    (stabilizerUnderlyingIso G x).hom ≫ pullback.fst _ _ = (stabilizerι G x).left :=
  (stabilizerUnderlyingIsPullback G x).isoPullback_hom_fst

/-- The comparison identifies the second projection with the structure morphism. -/
@[reassoc (attr := simp)]
theorem stabilizerUnderlyingIso_hom_snd :
    (stabilizerUnderlyingIso G x).hom ≫ pullback.snd _ _ = (stabilizer G x).hom :=
  (stabilizerUnderlyingIsPullback G x).isoPullback_hom_snd

/-- Stabilizer inclusions are closed immersions when the fixed section is closed. -/
theorem stabilizerι_isClosedImmersion [IsClosedImmersion x.left] :
    IsClosedImmersion (stabilizerι G x).left :=
  MorphismProperty.of_isPullback (stabilizerUnderlyingIsPullback G x).flip
    (inferInstance : IsClosedImmersion x.left)

/-- A separated action space over the base has closed stabilizer inclusions. -/
theorem stabilizerι_isClosedImmersion_of_isSeparated [IsSeparated X.hom] :
    IsClosedImmersion (stabilizerι G x).left := by
  let : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x, Over.tensorUnit_hom]
    let : MorphismProperty.ContainsIdentities
        (fun {Y Z : Scheme.{u}} (f : Y ⟶ Z) ↦ IsClosedImmersion f) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    exact MorphismProperty.id_mem _ S
  let : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
  exact stabilizerι_isClosedImmersion G x

end CategoryTheory.ModObj
