/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Scheme.EquivalenceRelationRankAffine
public import AlgebraicGroups.Scheme.EquivalenceRelationRestrict

@[expose] public section

/-!
# Restriction to rank strata of an affine equivalence relation

This file restricts a finite locally free internal equivalence relation to one
of its invariant rank strata.  It also compares the scheme-theoretic rank with
the rank of the induced map on affine coordinate rings.
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁]

/-- The first restricted coordinate-ring map is finite. -/
lemma finite_appTop_morphismRestrict_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X] (r : ℕ) :
    (p₁ ∣_ finrankOpen (p₁ := p₁) r).appTop.hom.Finite := by
  let _ : IsAffine (finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_finrankOpen (p₁ := p₁) r
  exact (p₁ ∣_ finrankOpen (p₁ := p₁) r).finite_appTop

/-- The first restricted coordinate-ring map is flat. -/
lemma flat_appTop_morphismRestrict_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X] (r : ℕ) :
    (p₁ ∣_ finrankOpen (p₁ := p₁) r).appTop.hom.Flat := by
  let _ : IsAffine (finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  exact (p₁ ∣_ finrankOpen (p₁ := p₁) r).flat_appTop

/-- The first restricted coordinate-ring map is finitely presented. -/
lemma finitePresentation_appTop_morphismRestrict_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X] (r : ℕ) :
    (p₁ ∣_ finrankOpen (p₁ := p₁) r).appTop.hom.FinitePresentation := by
  let _ : IsAffine (finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  exact (p₁ ∣_ finrankOpen (p₁ := p₁) r).finitePresentation_appTop

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the first projection to its rank-`r` stratum makes its rank
literally constant `r`. -/
lemma finrank_morphismRestrict_finrankOpen
    [LocallyOfFinitePresentation p₁] (r : ℕ)
    (x : finrankOpen (p₁ := p₁) r) :
    (p₁ ∣_ finrankOpen (p₁ := p₁) r).finrank x = r := by
  rw [Scheme.Hom.finrank_of_isPullback
    (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r).ι
    (p₁ ∣_ finrankOpen (p₁ := p₁) r) p₁
    (finrankOpen (p₁ := p₁) r).ι
    (isPullback_morphismRestrict p₁ (finrankOpen (p₁ := p₁) r)).flip]
  exact x.property

/-- The second projection restricted to the invariant rank stratum, with its
source transported to the first projection's preimage. -/
def morphismRestrictSnd [LocallyOfFinitePresentation p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r).toScheme ⟶
      finrankOpen (p₁ := p₁) r :=
  Restrict.snd (finrankOpen (p₁ := p₁) r)
    (preimage_finrankOpen_eq h r)

/-- The restricted second projection recovers the original second projection
after composing with the open immersions. -/
@[reassoc]
lemma morphismRestrictSnd_ι [LocallyOfFinitePresentation p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    morphismRestrictSnd h r ≫ (finrankOpen (p₁ := p₁) r).ι =
      (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r).ι ≫ p₂ := by
  exact Restrict.snd_ι (finrankOpen (p₁ := p₁) r)
    (preimage_finrankOpen_eq h r)

/-- Every invariant rank stratum inherits the original internal equivalence
relation on its two restricted legs. -/
def equivalenceRelationFinrankOpen [LocallyOfFinitePresentation p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    CategoryTheory.EquivalenceRelation
      (p₁ ∣_ finrankOpen (p₁ := p₁) r) (morphismRestrictSnd h r) :=
  Restrict.equivalenceRelation h (finrankOpen (p₁ := p₁) r)
    (preimage_finrankOpen_eq h r)

/-- On affine schemes, scheme-theoretic rank agrees with the rank of the map
on global sections at the corresponding prime. -/
lemma finrank_eq_appTop_finrank {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsAffine Y] [IsAffine Z] [Flat f] [IsFinite f] (z : Z) :
    f.finrank z = f.appTop.hom.finrank (Z.isoSpec.hom z) := by
  let _ : Flat (Spec.map f.appTop) :=
    Flat.SpecMap_iff.mpr f.flat_appTop
  let _ : IsFinite (Spec.map f.appTop) :=
    (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
  calc
    f.finrank z = (f ≫ Z.isoSpec.hom).finrank (Z.isoSpec.hom z) := by
      exact Scheme.Hom.finrank_of_isPullback (fst := 𝟙 Y) (snd := f)
        (f := f ≫ Z.isoSpec.hom) (g := Z.isoSpec.hom)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) z
    _ = (Y.isoSpec.hom ≫ Spec.map f.appTop).finrank
        (Z.isoSpec.hom z) := by rw [Scheme.isoSpec_hom_naturality]
    _ = (Spec.map f.appTop).finrank (Z.isoSpec.hom z) := by
      rw [Scheme.Hom.finrank_comp_left_of_isIso]
    _ = f.appTop.hom.finrank (Z.isoSpec.hom z) := by
      rw [Scheme.Hom.finrank_SpecMap_eq_finrank
        f.finite_appTop f.flat_appTop]

/-- The restricted first projection has coordinate-ring rank `r` after
localization at every maximal ideal of the restricted target. -/
lemma appTop_localizedModule_finrank_morphismRestrict_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X] (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) :=
      (p₁ ∣_ U).appTop.hom.toAlgebra
    ∀ (J : Ideal Γ(U, ⊤)) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl Γ(V, ⊤)) = r := by
  dsimp only
  intro J hJ
  let U := finrankOpen (p₁ := p₁) r
  let V := p₁ ⁻¹ᵁ U
  let f := p₁ ∣_ U
  let _ : IsAffine U := isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine V :=
    isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  let _ : Flat f := by infer_instance
  let _ : IsFinite f := by infer_instance
  let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  let j : Spec Γ(U, ⊤) := ⟨J, inferInstance⟩
  let y : U := U.toScheme.isoSpec.inv j
  change Module.finrank (Localization J.primeCompl)
    (LocalizedModule J.primeCompl Γ(V, ⊤)) = r
  calc
    Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl Γ(V, ⊤)) =
        f.appTop.hom.finrank j := rfl
    _ = f.appTop.hom.finrank (U.toScheme.isoSpec.hom y) := by
      rw [show U.toScheme.isoSpec.hom y = j by
        change U.toScheme.isoSpec.hom (U.toScheme.isoSpec.inv j) = _
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl]
    _ = f.finrank y := (finrank_eq_appTop_finrank f y).symm
    _ = r := finrank_morphismRestrict_finrankOpen r y

end AlgebraicGeometry.EquivalenceRelation
