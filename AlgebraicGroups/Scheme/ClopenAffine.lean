/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Clopen subsets of affine schemes

This file realizes a clopen subset of an affine scheme as a basic open cut
out by an idempotent.  Its coordinate ring, and the coordinate ring of its
preimage under an affine morphism, are the corresponding away localizations.
It also records the natural restriction squares on global sections.
-/

public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

namespace Scheme.Opens

variable {X : Scheme.{u}} (U : X.Opens)

/-- The inclusion of an open subset whose carrier is closed is also a closed
immersion. -/
lemma isClosedImmersion_ι_of_isClosed (hU : IsClosed (U : Set X)) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by simpa using hU)

/-- A clopen subset of an affine scheme is affine. -/
lemma isAffineOpen_of_isClopen [IsAffine X] (hU : IsClopen (U : Set X)) :
    IsAffineOpen U := by
  let _ : IsClosedImmersion U.ι := U.isClosedImmersion_ι_of_isClosed hU.1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine U.ι).1

/-- Restriction of global sections to a clopen subset of an affine scheme is
surjective. -/
lemma appTop_surjective_of_isClopen [IsAffine X] (hU : IsClopen (U : Set X)) :
    Function.Surjective U.ι.appTop := by
  let _ : IsClosedImmersion U.ι := U.isClosedImmersion_ι_of_isClosed hU.1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine U.ι).2

/-- A clopen subset of an affine scheme is a basic open cut out by an
idempotent global section. -/
lemma exists_isIdempotent_basicOpen_eq [IsAffine X]
    (hU : IsClopen (U : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U := by
  let eX : X ≃ₜ PrimeSpectrum Γ(X, ⊤) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)
  let V : Clopens (PrimeSpectrum Γ(X, ⊤)) :=
    ⟨eX.symm ⁻¹' (U : Set X), hU.preimage eX.symm.continuous⟩
  let e := PrimeSpectrum.isIdempotentElemEquivClopens.symm V
  refine ⟨e.1, e.2, ?_⟩
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine,
    PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm]
  ext x
  change eX.symm (eX x) ∈ U ↔ x ∈ U
  simp

/-- On an affine scheme, an idempotent global section is determined by its
basic open. -/
lemma basicOpen_injOn_isIdempotentElem [IsAffine X] :
    {e : Γ(X, ⊤) | IsIdempotentElem e}.InjOn X.basicOpen := by
  intro e he f hf hef
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he hf
  have hef' := hef
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine,
    ← X.map_PrimeSpectrum_basicOpen_of_affine] at hef'
  apply Opens.ext
  apply Set.preimage_injective.mpr
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).surjective
  exact congr_arg (fun V : X.Opens ↦ (V : Set X)) hef'

/-- The coordinate ring of a clopen subset of an affine scheme is an away
localization at an idempotent cutting out that subset. -/
lemma exists_isIdempotent_isLocalization [IsAffine X]
    (hU : IsClopen (U : Set X)) :
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U ∧
      IsLocalization.Away e Γ(X, U) := by
  dsimp only
  obtain ⟨e, he, hUe⟩ := U.exists_isIdempotent_basicOpen_eq hU
  refine ⟨e, he, hUe, ?_⟩
  subst U
  exact isLocalization_away_of_isAffine e

end Scheme.Opens

namespace Scheme.Hom

/-- A clopen subset of an affine target and its preimage under an affine
morphism are simultaneously modeled by localization away from an idempotent
and its image. -/
lemma exists_isIdempotent_isLocalization_and_preimage
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffineHom f]
    (U : X.Opens) (hU : IsClopen (U : Set X)) :
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(Y, ⊤) Γ(Y, f ⁻¹ᵁ U) :=
      (Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U ∧
      IsLocalization.Away e Γ(X, U) ∧
      IsLocalization.Away (f.appTop e) Γ(Y, f ⁻¹ᵁ U) := by
  dsimp only
  let _ : IsAffine Y := isAffine_of_isAffineHom f
  obtain ⟨e, he, hbasic⟩ := U.exists_isIdempotent_basicOpen_eq hU
  refine ⟨e, he, hbasic, hbasic ▸ isLocalization_away_of_isAffine e, ?_⟩
  rw [← hbasic, Scheme.preimage_basicOpen_top]
  exact isLocalization_away_of_isAffine (f.appTop e)

/-- If two affine morphisms have the same preimage of a clopen basic open,
then they send its defining idempotent to the same global section. -/
lemma appTop_eq_of_preimage_basicOpen_eq
    {Y X : Scheme.{u}} (f g : Y ⟶ X) [IsAffine Y]
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e)
    (hpre : f ⁻¹ᵁ X.basicOpen e = g ⁻¹ᵁ X.basicOpen e) :
    f.appTop e = g.appTop e := by
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top] at hpre
  change f.appTop.hom e = g.appTop.hom e
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem
      (he.map f.appTop.hom) (he.map g.appTop.hom)
  have hpre' := hpre
  rw [← Y.map_PrimeSpectrum_basicOpen_of_affine,
    ← Y.map_PrimeSpectrum_basicOpen_of_affine] at hpre'
  apply Opens.ext
  apply Set.preimage_injective.mpr
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso Y.isoSpec)).surjective
  exact congr_arg (fun V : Y.Opens ↦ (V : Set Y)) hpre'

/-- Restriction to an open and its preimage commutes with the global
coordinate-ring map. -/
lemma appTop_restriction_square
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(Y, ⊤) Γ(Y, f ⁻¹ᵁ U) :=
      (Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    (algebraMap Γ(Y, ⊤) Γ(Y, f ⁻¹ᵁ U)).comp f.appTop.hom =
      (f.app U).hom.comp (algebraMap Γ(X, ⊤) Γ(X, U)) := by
  dsimp only
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  exact congr_arg CommRingCat.Hom.hom
    (f.naturality (homOfLE le_top).op).symm

/-- Variant of `Scheme.Hom.appTop_restriction_square` with a chosen open
identified with the preimage. -/
lemma appTop_restriction_square_of_eq
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (hV : V = f ⁻¹ᵁ U) :
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(Y, ⊤) Γ(Y, V) :=
      (Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    (algebraMap Γ(Y, ⊤) Γ(Y, V)).comp f.appTop.hom =
      (f.appLE U V hV.le).hom.comp (algebraMap Γ(X, ⊤) Γ(X, U)) := by
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using f.appTop_restriction_square U

end Scheme.Hom

end AlgebraicGeometry
