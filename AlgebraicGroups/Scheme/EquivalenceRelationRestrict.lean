/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Category.EquivalenceRelation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

/-!
# Restricting an internal scheme equivalence relation

An invariant open of the object scheme has one common preimage under the two
relation maps. The two restricted maps on that common source again form an
internal equivalence relation.

The preimage equality alone permits the second leg to be transported by
`isoOfEq`; pullback lifts restrict reflexivity, symmetry and composition.
Neither affine nor finite-flat hypotheses nor a quotient are required.

## References

* Stacks Project, Lemma 39.23.3 (tag 03BI), for the motivating restriction
  to invariant constant-rank opens. The construction here applies to every
  invariant open of any scheme equivalence relation.
* Mathlib, `Mathlib.AlgebraicGeometry.Restrict` for `isoOfEq` and
  `isPullback_morphismRestrict`, `Mathlib.AlgebraicGeometry.Pullbacks` for
  limiting pullback lifts, and `Mathlib.CategoryTheory.EquivalenceRelation`
  for the internal relation structure.
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation.Restrict

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

/-- The second leg restricted to an invariant open, transported to the first
leg's preimage so both restricted legs have literally the same source. -/
def snd (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    (p₁ ⁻¹ᵁ U).toScheme ⟶ U :=
  (R.isoOfEq hU).hom ≫ p₂ ∣_ U

@[reassoc]
lemma snd_ι (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    snd U hU ≫ U.ι = (p₁ ⁻¹ᵁ U).ι ≫ p₂ := by
  simp [snd, Category.assoc]

/-- The reflexivity map restricted to an invariant open. -/
def reflexivity (h : EquivalenceRelation p₁ p₂) (U : X.Opens) :
    U.toScheme ⟶ (p₁ ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p₁ U).lift (𝟙 _) (U.ι ≫ h.r) (by simp)

@[reassoc]
lemma reflexivity_fst (h : EquivalenceRelation p₁ p₂) (U : X.Opens) :
    reflexivity h U ≫ p₁ ∣_ U = 𝟙 _ := by
  exact (isPullback_morphismRestrict p₁ U).lift_fst _ _ _

@[reassoc]
lemma reflexivity_snd (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    reflexivity h U ≫ snd U hU = 𝟙 _ := by
  rw [← cancel_mono U.ι]
  simp [Category.assoc, snd_ι, reflexivity]

/-- The symmetry map restricted to the common relation preimage. -/
def symmetry (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    (p₁ ⁻¹ᵁ U).toScheme ⟶ (p₁ ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p₁ U).lift (snd U hU)
    ((p₁ ⁻¹ᵁ U).ι ≫ h.s) (by
      rw [snd_ι, Category.assoc, h.symmetry₁])

@[reassoc]
lemma symmetry_fst (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    symmetry h U hU ≫ p₁ ∣_ U = snd U hU := by
  exact (isPullback_morphismRestrict p₁ U).lift_fst _ _ _

@[reassoc]
lemma symmetry_snd (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    symmetry h U hU ≫ snd U hU = p₁ ∣_ U := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, snd_ι, symmetry,
    (isPullback_morphismRestrict p₁ U).lift_snd_assoc]
  rw [h.symmetry₂, morphismRestrict_ι]

/-- The chosen pullback cone for composition of the restricted relation. -/
def compositionCone (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    PullbackCone (snd U hU) (p₁ ∣_ U) :=
  PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- The restricted composable-pair object maps to the original one. -/
def compositionConeToOriginal (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    (compositionCone U hU).pt ⟶ h.c.pt :=
  h.isLimit.lift (PullbackCone.mk
    ((compositionCone U hU).fst ≫ (p₁ ⁻¹ᵁ U).ι)
    ((compositionCone U hU).snd ≫ (p₁ ⁻¹ᵁ U).ι) (by
      simpa only [Category.assoc, ← snd_ι U hU,
        ← morphismRestrict_ι] using
          congrArg (fun k => k ≫ U.ι) (compositionCone U hU).condition))

@[reassoc]
lemma compositionConeToOriginal_fst (h : EquivalenceRelation p₁ p₂)
    (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    compositionConeToOriginal h U hU ≫ h.c.fst =
      (compositionCone U hU).fst ≫ (p₁ ⁻¹ᵁ U).ι := by
  exact h.isLimit.fac _ WalkingCospan.left

@[reassoc]
lemma compositionConeToOriginal_snd (h : EquivalenceRelation p₁ p₂)
    (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    compositionConeToOriginal h U hU ≫ h.c.snd =
      (compositionCone U hU).snd ≫ (p₁ ⁻¹ᵁ U).ι := by
  exact h.isLimit.fac _ WalkingCospan.right

/-- Composition for the restricted relation, obtained by composing upstairs
and lifting the result through the first-leg restriction square. -/
def transitivity (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    (compositionCone U hU).pt ⟶ (p₁ ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p₁ U).lift
    ((compositionCone U hU).fst ≫ p₁ ∣_ U)
    (compositionConeToOriginal h U hU ≫ h.t) (by
      calc
        ((compositionCone U hU).fst ≫ p₁ ∣_ U) ≫ U.ι =
            ((compositionCone U hU).fst ≫ (p₁ ⁻¹ᵁ U).ι) ≫ p₁ := by
              simp only [Category.assoc, morphismRestrict_ι]
        _ = (compositionConeToOriginal h U hU ≫ h.c.fst) ≫ p₁ := by
              rw [compositionConeToOriginal_fst]
        _ = (compositionConeToOriginal h U hU ≫ h.t) ≫ p₁ := by
              simp only [Category.assoc, h.transitivity₁])

@[reassoc]
lemma transitivity_ι (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    transitivity h U hU ≫ (p₁ ⁻¹ᵁ U).ι =
      compositionConeToOriginal h U hU ≫ h.t := by
  exact (isPullback_morphismRestrict p₁ U).lift_snd _ _ _

@[reassoc]
lemma transitivity_fst (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    transitivity h U hU ≫ p₁ ∣_ U =
      (compositionCone U hU).fst ≫ p₁ ∣_ U := by
  exact (isPullback_morphismRestrict p₁ U).lift_fst _ _ _

@[reassoc]
lemma transitivity_snd (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    transitivity h U hU ≫ snd U hU =
      (compositionCone U hU).snd ≫ snd U hU := by
  rw [← cancel_mono U.ι]
  calc
    (transitivity h U hU ≫ snd U hU) ≫ U.ι =
        (transitivity h U hU ≫ (p₁ ⁻¹ᵁ U).ι) ≫ p₂ := by
          simp only [Category.assoc, snd_ι]
    _ = (compositionConeToOriginal h U hU ≫ h.t) ≫ p₂ := by
          rw [transitivity_ι]
    _ = (compositionConeToOriginal h U hU ≫ h.c.snd) ≫ p₂ := by
          simp only [Category.assoc, h.transitivity₂]
    _ = ((compositionCone U hU).snd ≫ (p₁ ⁻¹ᵁ U).ι) ≫ p₂ := by
          rw [compositionConeToOriginal_snd]
    _ = ((compositionCone U hU).snd ≫ snd U hU) ≫ U.ι := by
          simp only [Category.assoc, snd_ι]

/-- Restriction to an invariant open preserves an internal scheme equivalence
relation. This generalizes the invariant constant-rank-open restriction used
in Stacks Project, Lemma 39.23.3 (tag 03BI): equality of the two leg
preimages suffices, without any rank, finiteness, flatness or quotient
assumption. -/
def equivalenceRelation (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    EquivalenceRelation (p₁ ∣_ U) (snd U hU) where
  right_cancellation Y f g hfst hsnd := by
    rw [← cancel_mono (p₁ ⁻¹ᵁ U).ι]
    apply h.toJointlyMono₂.right_cancellation
    · simpa only [Category.assoc, ← morphismRestrict_ι] using
        congrArg (fun k => k ≫ U.ι) hfst
    · simpa only [Category.assoc, ← snd_ι U hU] using
        congrArg (fun k => k ≫ U.ι) hsnd
  r := reflexivity h U
  reflexivity₁ := reflexivity_fst h U
  reflexivity₂ := reflexivity_snd h U hU
  s := symmetry h U hU
  symmetry₁ := symmetry_fst h U hU
  symmetry₂ := symmetry_snd h U hU
  c := compositionCone U hU
  isLimit := by
    simpa only [compositionCone] using
      (pullbackIsPullback (snd U hU) (p₁ ∣_ U))
  t := transitivity h U hU
  transitivity₁ := transitivity_fst h U hU
  transitivity₂ := transitivity_snd h U hU

end AlgebraicGeometry.EquivalenceRelation.Restrict
