/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.RingTheory.Equalizer
public import AlgebraicGroups.Scheme.EquivalenceRelationRankAffine

@[expose] public section

/-!
# Equalizers on affine rank strata

For a finite flat internal equivalence relation over an affine scheme, the
restriction map from the global invariant-ring equalizer to the equalizer on
each locally finitely presented rank stratum is localization away from an
idempotent in the global equalizer.

This combines the affine rank-stratum localization interface with the generic
localization theorem for equalizers. It does not prove faithful flatness,
identify a tensor comparison, construct a quotient, or prove quotient
effectivity. This particular idempotent localization is not the arbitrary
base-change assertion for invariant rings in Stacks Project Lemma 39.23.5.

## References

* The Stacks Project, Lemma 39.23.3
  ([tag 03BI](https://stacks.math.columbia.edu/tag/03BI)), supplies the
  invariant rank pieces. Lemma 39.23.5
  ([tag 03BK](https://stacks.math.columbia.edu/tag/03BK)) concerns a distinct,
  more general base-change assertion.
* `AlgebraicGroups.Scheme.EquivalenceRelationRankAffine` supplies the
  rank-idempotent and common-preimage localization squares;
  `AlgebraicGroups.RingTheory.Equalizer` supplies the generic
  `AlgHom.equalizerMapOfCommuting_isLocalizationAway` interface.
-/

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]

/-- On every affine rank stratum of a finite flat equivalence relation, the
restriction map from the global equalizer of the two relation maps to the
stratum equalizer is localization away from an idempotent. The same idempotent
cuts out the stratum as a basic open of the target. This specializes generic
equalizer localization to the invariant rank pieces of Stacks Project
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI). -/
lemma exists_finrankOpen_equalizer_isLocalizationAway
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    let sU : Γ(X, U) →ₐ[ℤ] Γ(R, V) := (p₁.app U).hom.toIntAlgHom
    let tU : Γ(X, U) →ₐ[ℤ] Γ(R, V) :=
      (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom.toIntAlgHom
    let f : Γ(X, ⊤) →ₐ[ℤ] Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    let g : Γ(R, ⊤) →ₐ[ℤ] Γ(R, V) :=
      (R.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    ∃ e : AlgHom.equalizer s t, IsIdempotentElem e ∧
      X.basicOpen e.1 = U ∧
      let hs : g.comp s = sU.comp f := by
        ext x
        exact DFunLike.congr_fun (p₁.appTop_restriction_square U) x
      let ht : g.comp t = tU.comp f := by
        ext x
        exact DFunLike.congr_fun (p₂.appTop_restriction_square_of_eq U V
          (preimage_finrankOpen_eq h r)) x
      let φ := AlgHom.equalizerMapOfCommuting s t sU tU f g hs ht
      let _ : Algebra (AlgHom.equalizer s t) (AlgHom.equalizer sU tU) :=
        φ.toRingHom.toAlgebra
      IsLocalization.Away e (AlgHom.equalizer sU tU) := by
  dsimp only
  obtain ⟨e, he, hbasic, hAe, hRe, heq, hsRing, htRing⟩ :=
    exists_finrankOpen_localizations_and_squares h r
  let U := finrankOpen (p₁ := p₁) r
  let V := p₁ ⁻¹ᵁ U
  let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
    (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let _ : Algebra Γ(R, ⊤) Γ(R, V) :=
    (R.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let s := p₁.appTop.hom.toIntAlgHom
  let t := p₂.appTop.hom.toIntAlgHom
  let sU := (p₁.app U).hom.toIntAlgHom
  let tU := (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom.toIntAlgHom
  let f : Γ(X, ⊤) →ₐ[ℤ] Γ(X, U) :=
    (X.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
  let g : Γ(R, ⊤) →ₐ[ℤ] Γ(R, V) :=
    (R.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
  have hs : g.comp s = sU.comp f := by
    ext x
    exact DFunLike.congr_fun hsRing x
  have ht : g.comp t = tU.comp f := by
    ext x
    exact DFunLike.congr_fun htRing x
  let eE : AlgHom.equalizer s t := ⟨e, heq⟩
  have heE : IsIdempotentElem eE := by
    change eE * eE = eE
    apply Subtype.ext
    exact he.eq
  refine ⟨eE, heE, hbasic, ?_⟩
  let _ : IsLocalization.Away e Γ(X, U) := hAe
  let _ : IsLocalization.Away (s e) Γ(R, V) := hRe
  exact AlgHom.equalizerMapOfCommuting_isLocalizationAway
    s t sU tU f g rfl rfl hs ht eE heE

/-- The equalizer restriction to a rank stratum is localization away from any
idempotent in the global equalizer whose basic open is that stratum. -/
lemma finrankOpen_equalizer_isLocalizationAway_of_basicOpen_eq
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ)
    (e : AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
      p₂.appTop.hom.toIntAlgHom)
    (he : IsIdempotentElem e)
    (hbasic : X.basicOpen e.1 = finrankOpen (p₁ := p₁) r) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    let sU : Γ(X, U) →ₐ[ℤ] Γ(R, V) := (p₁.app U).hom.toIntAlgHom
    let tU : Γ(X, U) →ₐ[ℤ] Γ(R, V) :=
      (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom.toIntAlgHom
    let f : Γ(X, ⊤) →ₐ[ℤ] Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    let g : Γ(R, ⊤) →ₐ[ℤ] Γ(R, V) :=
      (R.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    let hs : g.comp s = sU.comp f := by
      ext x
      exact DFunLike.congr_fun (p₁.appTop_restriction_square U) x
    let ht : g.comp t = tU.comp f := by
      ext x
      exact DFunLike.congr_fun (p₂.appTop_restriction_square_of_eq U V
        (preimage_finrankOpen_eq h r)) x
    let φ := AlgHom.equalizerMapOfCommuting s t sU tU f g hs ht
    let _ : Algebra (AlgHom.equalizer s t) (AlgHom.equalizer sU tU) :=
      φ.toRingHom.toAlgebra
    IsLocalization.Away e (AlgHom.equalizer sU tU) := by
  dsimp only
  obtain ⟨e', he', hbasic', hloc⟩ :=
    exists_finrankOpen_equalizer_isLocalizationAway h r
  have heq : e' = e := by
    apply Subtype.ext
    apply Scheme.Opens.basicOpen_injOn_isIdempotentElem
      (he'.map (AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
        p₂.appTop.hom.toIntAlgHom).val)
      (he.map (AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
        p₂.appTop.hom.toIntAlgHom).val)
    exact hbasic'.trans hbasic.symm
  subst e'
  exact hloc

/-- On a compact affine target, the invariant idempotents cutting out the
nonempty rank strata lift to a complete orthogonal family in the global
equalizer. Together with
`finrankOpen_equalizer_isLocalizationAway_of_basicOpen_eq`, every member of
this one family gives the corresponding rank-stratum localization. -/
lemma exists_completeOrthogonalIdempotents_equalizer_finrankOpen
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    let I := Set.range p₁.finrank
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    ∃ e : I → AlgHom.equalizer s t,
      @CompleteOrthogonalIdempotents (AlgHom.equalizer s t) _ I
        (finrankRangeFintype (p₁ := p₁)) e ∧
        ∀ i, X.basicOpen (e i).1 = finrankOpen (p₁ := p₁) i.1 := by
  dsimp only
  let _ : Fintype (Set.range p₁.finrank) :=
    finrankRangeFintype (p₁ := p₁)
  obtain ⟨e, he, hbasic⟩ :=
    exists_completeOrthogonalIdempotents_finrankOpen h
  let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
  let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
  let eE : Set.range p₁.finrank → AlgHom.equalizer s t := fun i ↦
    ⟨e i, (hbasic i).2⟩
  have heE : CompleteOrthogonalIdempotents eE := by
    constructor
    · constructor
      · intro i
        apply Subtype.ext
        exact (he.idem i).eq
      · intro i j hij
        apply Subtype.ext
        exact he.ortho hij
    · apply Subtype.ext
      change (AlgHom.equalizer s t).val (∑ i, eE i) =
        (AlgHom.equalizer s t).val 1
      rw [map_sum, map_one]
      change ∑ i, e i = 1
      exact he.complete
  exact ⟨eE, heE, fun i ↦ (hbasic i).1⟩

end AlgebraicGeometry.EquivalenceRelation
