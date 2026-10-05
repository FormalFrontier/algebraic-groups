/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.EquivalenceRelation

@[expose] public section

/-!
# Cartesian squares from internal equivalence relations

This file transports internal equivalence relations across isomorphisms and
shows that their symmetry maps are involutive isomorphisms. Composition with
the first projection exhibits a pullback: the categorical square used to
compare ranks along a finite flat relation.

These statements use only the jointly monic internal relation and its chosen
limiting cone; they require neither schemes nor an effective quotient.

## References

* Stacks Project, Lemma 39.13.4 (tag 02YE), for groupoid cartesian
  squares; Lemma 39.23.2 (tag 03BH) uses one in the invariant-norm argument,
  and Lemma 39.23.3 (tag 03BI) uses symmetry to compare relation-leg ranks.
  The results here isolate their underlying categorical consequences.
* Mathlib, `Mathlib.CategoryTheory.EquivalenceRelation`, for jointly monic
  internal relations and their limiting composition cone.
-/

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.EquivalenceRelation

universe v u

variable {C : Type u} [Category.{v, u} C]
  {R X : C} {p₁ p₂ : R ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport an internal equivalence relation across isomorphisms of its
relation object and object. -/
def transport (h : CategoryTheory.EquivalenceRelation p₁ p₂)
    {R' X' : C} (iR : R' ≅ R) (iX : X ≅ X') :
    CategoryTheory.EquivalenceRelation
      (iR.hom ≫ p₁ ≫ iX.hom) (iR.hom ≫ p₂ ≫ iX.hom) := by
  let c : PullbackCone
      (iR.hom ≫ p₂ ≫ iX.hom) (iR.hom ≫ p₁ ≫ iX.hom) :=
    PullbackCone.mk (h.c.fst ≫ iR.inv) (h.c.snd ≫ iR.inv) (by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun k ↦ k ≫ iX.hom) h.c.condition)
  have hc : IsLimit c := by
    let hp : IsPullback h.c.fst h.c.snd p₂ p₁ :=
      IsPullback.of_isLimit h.isLimit
    have hp' : IsPullback (h.c.fst ≫ iR.inv) (h.c.snd ≫ iR.inv)
        (iR.hom ≫ p₂ ≫ iX.hom) (iR.hom ≫ p₁ ≫ iX.hom) := by
      apply hp.of_iso (Iso.refl _) iR.symm iR.symm iX
      all_goals simp
    exact hp'.isLimit
  have c_fst : c.fst = h.c.fst ≫ iR.inv := rfl
  have c_snd : c.snd = h.c.snd ≫ iR.inv := rfl
  refine
    { right_cancellation := ?_
      r := iX.inv ≫ h.r ≫ iR.inv
      reflexivity₁ := by simp
      reflexivity₂ := by simp
      s := iR.hom ≫ h.s ≫ iR.inv
      symmetry₁ := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc,
          Iso.cancel_iso_hom_left]
        exact h.symmetry₁_assoc iX.hom
      symmetry₂ := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc,
          Iso.cancel_iso_hom_left]
        exact h.symmetry₂_assoc iX.hom
      c := c
      isLimit := hc
      t := h.t ≫ iR.inv
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · intro Y f g h₁ h₂
    rw [← cancel_mono iR.hom]
    apply h.toJointlyMono₂.right_cancellation
    · rw [← cancel_mono iX.hom]
      simpa only [Category.assoc] using h₁
    · rw [← cancel_mono iX.hom]
      simpa only [Category.assoc] using h₂
  · rw [c_fst]
    calc
      (h.t ≫ iR.inv) ≫ (iR.hom ≫ p₁ ≫ iX.hom) =
          h.t ≫ p₁ ≫ iX.hom := by simp
      _ = h.c.fst ≫ p₁ ≫ iX.hom := h.transitivity₁_assoc iX.hom
      _ = (h.c.fst ≫ iR.inv) ≫
          (iR.hom ≫ p₁ ≫ iX.hom) := by simp
  · rw [c_snd]
    calc
      (h.t ≫ iR.inv) ≫ (iR.hom ≫ p₂ ≫ iX.hom) =
          h.t ≫ p₂ ≫ iX.hom := by simp
      _ = h.c.snd ≫ p₂ ≫ iX.hom := h.transitivity₂_assoc iX.hom
      _ = (h.c.snd ≫ iR.inv) ≫
          (iR.hom ≫ p₂ ≫ iX.hom) := by simp

/-- The symmetry map of an internal equivalence relation is an isomorphism,
with itself as inverse. This abstracts the inverse used to compare the two
relation-leg ranks in Stacks Project, Lemma 39.23.3 (tag 03BI). -/
lemma isIso_symmetry (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    IsIso h.s := by
  have hs : h.s ≫ h.s = 𝟙 R := by
    apply h.toJointlyMono₂.right_cancellation
    · rw [Category.assoc, h.symmetry₁, h.symmetry₂, Category.id_comp]
    · rw [Category.assoc, h.symmetry₂, h.symmetry₁, Category.id_comp]
  exact ⟨⟨h.s, hs, hs⟩⟩

/-- For an internal equivalence relation, composition and the first
projection form a pullback over the first relation map. This abstracts the
groupoid cartesian square of Stacks Project, Lemma 39.13.4 (tag 02YE), without
requiring a quotient or any geometric hypotheses. -/
def isLimit_composition_fst (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    IsLimit (PullbackCone.mk h.t h.c.fst h.transitivity₁) := by
  let inverseComposeCone (z : PullbackCone p₁ p₁) : PullbackCone p₂ p₁ :=
    PullbackCone.mk (z.snd ≫ h.s) z.fst <| by
      rw [Category.assoc, h.symmetry₂]
      exact z.condition.symm
  let inverseCompose (z : PullbackCone p₁ p₁) : z.pt ⟶ h.c.pt :=
    h.isLimit.lift (inverseComposeCone z)
  have inverseCompose_fst (z : PullbackCone p₁ p₁) :
      inverseCompose z ≫ h.c.fst = z.snd ≫ h.s :=
    h.isLimit.fac (inverseComposeCone z) WalkingCospan.left
  have inverseCompose_snd (z : PullbackCone p₁ p₁) :
      inverseCompose z ≫ h.c.snd = z.fst :=
    h.isLimit.fac (inverseComposeCone z) WalkingCospan.right
  let resultCone (z : PullbackCone p₁ p₁) : PullbackCone p₂ p₁ :=
    PullbackCone.mk z.snd (inverseCompose z ≫ h.t) <| by
      rw [Category.assoc, h.transitivity₁, ← Category.assoc,
        inverseCompose_fst, Category.assoc, h.symmetry₁]
  let lift (z : PullbackCone p₁ p₁) : z.pt ⟶ h.c.pt :=
    h.isLimit.lift (resultCone z)
  have lift_fst (z : PullbackCone p₁ p₁) :
      lift z ≫ h.c.fst = z.snd :=
    h.isLimit.fac (resultCone z) WalkingCospan.left
  have lift_snd (z : PullbackCone p₁ p₁) :
      lift z ≫ h.c.snd = inverseCompose z ≫ h.t :=
    h.isLimit.fac (resultCone z) WalkingCospan.right
  refine PullbackCone.IsLimit.mk h.transitivity₁ lift ?_ lift_fst ?_
  · intro z
    apply h.toJointlyMono₂.right_cancellation
    · rw [Category.assoc, h.transitivity₁, ← Category.assoc, lift_fst]
      exact z.condition.symm
    · rw [Category.assoc, h.transitivity₂, ← Category.assoc, lift_snd,
        Category.assoc, h.transitivity₂, ← Category.assoc,
        inverseCompose_snd]
  · intro z m hm_comp hm_fst
    have hfst : m ≫ h.c.fst = lift z ≫ h.c.fst :=
      hm_fst.trans (lift_fst z).symm
    have hcomp : m ≫ h.t = lift z ≫ h.t :=
      hm_comp.trans (by
        apply h.toJointlyMono₂.right_cancellation
        · rw [Category.assoc, h.transitivity₁, ← Category.assoc, lift_fst]
          exact z.condition
        · rw [Category.assoc, h.transitivity₂, ← Category.assoc, lift_snd,
            Category.assoc, h.transitivity₂, ← Category.assoc,
            inverseCompose_snd])
    apply PullbackCone.IsLimit.hom_ext h.isLimit hfst
    apply h.toJointlyMono₂.right_cancellation
    · rw [Category.assoc, ← h.c.condition, ← Category.assoc, hfst,
        Category.assoc, h.c.condition]
      simp only [Category.assoc]
    · rw [Category.assoc, ← h.transitivity₂, ← Category.assoc, hcomp,
        Category.assoc, h.transitivity₂]
      simp only [Category.assoc]

end CategoryTheory.EquivalenceRelation
