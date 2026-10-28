/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.RingTheory.Invariant.EquivalenceRelation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import AlgebraicGroups.LinearAlgebra.FiniteProjective.Charpoly
public import AlgebraicGroups.Scheme.AffineEquivalenceRelation
public import AlgebraicGroups.Scheme.EquivalenceRelationRankEqualizer
public import AlgebraicGroups.Scheme.EquivalenceRelationRankRestrict

@[expose] public section

/-!
# Integrality of affine finite locally free equivalence relations

The canonical characteristic polynomial on each constant-rank stratum has
invariant coefficients.  Clopen localization lifts the resulting equations,
and the complete family of invariant rank idempotents patches them to prove
that the affine object ring is integral over the equalizer of the two relation
maps.

The rank partition is finite on the compact affine target. On each piece,
the restricted finite projective coordinate module has rank equal to that
piece's index; its monic characteristic polynomial transports through the
open-scheme isomorphisms. Supported equations then patch across the complete
family of rank idempotents. Although this family is orthogonal, the generic
polynomial patcher uses only idempotence and that the idempotents sum to one.
No global basis, faithful flatness of the map to the invariant spectrum,
tensor comparison or effectivity is asserted.

## References

* The Stacks Project, Lemmas 39.23.3 and 39.23.4
  ([tags 03BI](https://stacks.math.columbia.edu/tag/03BI) and
  [03BJ](https://stacks.math.columbia.edu/tag/03BJ)), give the invariant
  finite locally free rank decomposition and integrality over the invariant
  ring; Lemma 39.23.2
  ([tag 03BH](https://stacks.math.columbia.edu/tag/03BH)) gives the
  coefficient-invariance step.
* `AlgebraicGroups.Scheme.AffineEquivalenceRelationIntegrality` supplies
  fixed-rank coefficient invariance;
  `AlgebraicGroups.Scheme.EquivalenceRelationRankRestrict` and
  `AlgebraicGroups.Scheme.EquivalenceRelationRankEqualizer` supply the
  restricted relation and invariant idempotents;
  `AlgebraicGroups.RingTheory.Equalizer` supplies supported-equation lifting
  and the general idempotent polynomial patcher.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

open AlgebraicGeometry

universe w

/-- Affine coordinates preserve an internal scheme equivalence relation. -/
def appTop {R X : Scheme.{w}} {p₁ p₂ : R ⟶ X}
    [IsAffine R] [IsAffine X] (h : EquivalenceRelation p₁ p₂) :
    EquivalenceRelation (Spec.map p₁.appTop) (Spec.map p₂.appTop) := by
  have hp₁ : R.isoSpec.inv ≫ p₁ ≫ X.isoSpec.hom = Spec.map p₁.appTop := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hp₂ : R.isoSpec.inv ≫ p₂ ≫ X.isoSpec.hom = Spec.map p₂.appTop := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Iso.symm_hom, hp₁, hp₂] using
    CategoryTheory.EquivalenceRelation.transport h R.isoSpec.symm X.isoSpec

open Module.FiniteProjective
open AlgebraicGeometry.AffineEquivalenceRelation

/-- The two coordinate maps on a restricted rank stratum retain the internal
equivalence relation after passing to affine `Spec` coordinates. -/
def appTopFinrankOpen {R X : Scheme.{w}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]
    (h : EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    EquivalenceRelation
      (Spec.map (p₁ ∣_ U).appTop)
      (Spec.map (morphismRestrictSnd h r).appTop) := by
  dsimp only
  let _ : IsAffine (finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  exact appTop (equivalenceRelationFinrankOpen h r)

/-- The canonical fixed-rank characteristic polynomial on a restricted rank
stratum has invariant coefficients in its literal affine coordinate rings. -/
lemma projectiveCharpolyRev_reflect_coeff_invariant_finrankOpen
    {R X : Scheme.{w}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]
    (h : EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let s : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) :=
      (p₁ ∣_ U).appTop.hom.toIntAlgHom
    let t : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) :=
      (morphismRestrictSnd h r).appTop.hom.toIntAlgHom
    let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) := s.toRingHom.toAlgebra
    let _ : Module.Finite Γ(U, ⊤) Γ(V, ⊤) :=
      finite_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
    let _ : Module.Flat Γ(U, ⊤) Γ(V, ⊤) :=
      flat_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
    let _ : Algebra.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
      finitePresentation_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
    let _ : Module.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
      (Module.FinitePresentation.iff_finitePresentation_of_finite
        Γ(U, ⊤) Γ(V, ⊤)).mpr
        (by infer_instance)
    let _ : Module.Projective Γ(U, ⊤) Γ(V, ⊤) :=
      Module.Flat.projective_of_finitePresentation
    ∀ (x : Γ(U, ⊤)) (k : ℕ),
      s (((LinearMap.projectiveCharpolyRev
        (Algebra.lmul Γ(U, ⊤) Γ(V, ⊤) (t x))).reflect r).coeff k) =
      t (((LinearMap.projectiveCharpolyRev
        (Algebra.lmul Γ(U, ⊤) Γ(V, ⊤) (t x))).reflect r).coeff k) := by
  dsimp only
  let U := finrankOpen (p₁ := p₁) r
  let V := p₁ ⁻¹ᵁ U
  let f := p₁ ∣_ U
  let g := morphismRestrictSnd h r
  let s : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) := f.appTop.hom.toIntAlgHom
  let t : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) := g.appTop.hom.toIntAlgHom
  let _ : IsAffine U := isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine V := isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) := s.toRingHom.toAlgebra
  let _ : Module.Finite Γ(U, ⊤) Γ(V, ⊤) :=
    finite_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Module.Flat Γ(U, ⊤) Γ(V, ⊤) :=
    flat_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Algebra.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
    finitePresentation_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Module.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite
      Γ(U, ⊤) Γ(V, ⊤)).mpr
      (by infer_instance)
  let _ : Module.Projective Γ(U, ⊤) Γ(V, ⊤) :=
    Module.Flat.projective_of_finitePresentation
  let sr := s.toRingHom
  let tr := t.toRingHom
  have hrel : EquivalenceRelation (Spec.map (CommRingCat.ofHom sr))
      (Spec.map (CommRingCat.ofHom tr)) := appTopFinrankOpen h r
  have hSpec : sr.IsSpecEquivRel tr := by
    have hi {U V : Type w} [CommRing U] [CommRing V] :
        Function.Injective (fun f : U →+* V => Spec.map (CommRingCat.ofHom f)) := by
      intro f g he
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T _ x y hs ht
      apply hi
      apply hrel.right_cancellation
      · simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(U, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) hs
      · simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(U, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) ht
    · intro T _ x
      refine ⟨(Spec.preimage (Spec.map (CommRingCat.ofHom x) ≫ hrel.r)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
        simp [Category.assoc, hrel.reflexivity₁, hrel.reflexivity₂]
    · intro T _ x
      refine ⟨(Spec.preimage (Spec.map (CommRingCat.ofHom x) ≫ hrel.s)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
        simp [Category.assoc, hrel.symmetry₁, hrel.symmetry₂]
    · intro T _ x y he
      have hc : Spec.map (CommRingCat.ofHom x) ≫ Spec.map (CommRingCat.ofHom tr) =
          Spec.map (CommRingCat.ofHom y) ≫ Spec.map (CommRingCat.ofHom sr) := by
        simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(U, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) he
      let c := PullbackCone.mk (Spec.map (CommRingCat.ofHom x))
        (Spec.map (CommRingCat.ofHom y)) hc
      refine ⟨(Spec.preimage (hrel.isLimit.lift c ≫ hrel.t)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
      · rw [Category.assoc, hrel.transitivity₁, ← Category.assoc]
        rw [hrel.isLimit.fac c WalkingCospan.left]
        rfl
      · rw [Category.assoc, hrel.transitivity₂, ← Category.assoc]
        rw [hrel.isLimit.fac c WalkingCospan.right]
        rfl
  intro x k
  rw [Polynomial.coeff_reflect]
  exact hSpec.coeff_projectiveCharpolyRev_mem_eqLocus x _

/-- A monic equation on one invariant rank stratum lifts to an ambient monic
equation whose coefficients and value satisfy the equalizer conditions after
multiplication by the idempotent cutting out that stratum. -/
lemma exists_monic_lift_finrankOpen_with_supported_equalities
    {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁]
    [IsAffine X] (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(R, ⊤) Γ(R, V) :=
      (R.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∀ (q : Γ(X, U)[X]), q.Monic →
      (∀ k, (p₁.app U) (q.coeff k) =
        p₂.appLE U V (preimage_finrankOpen_eq h r).le (q.coeff k)) →
      ∀ x : Γ(X, ⊤), q.eval (algebraMap Γ(X, ⊤) Γ(X, U) x) = 0 →
      ∃ e : Γ(X, ⊤), ∃ p : Γ(X, ⊤)[X],
        IsIdempotentElem e ∧ X.basicOpen e = U ∧ p.Monic ∧
        p.map (algebraMap Γ(X, ⊤) Γ(X, U)) = q ∧
        (∀ k, p₁.appTop (e * p.coeff k) =
          p₂.appTop (e * p.coeff k)) ∧ e * p.eval x = 0 := by
  dsimp only
  intro q hqmonic hqcoeff x hqeval
  let U := finrankOpen (p₁ := p₁) r
  let V := p₁ ⁻¹ᵁ U
  let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
    (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let _ : Algebra Γ(R, ⊤) Γ(R, V) :=
    (R.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  obtain ⟨e, he, hbasic, hAe, hBe, hst, hs, ht⟩ :=
    exists_finrankOpen_localizations_and_squares h r
  let _ : IsLocalization.Away e Γ(X, U) := hAe
  let _ : IsLocalization.Away (p₁.appTop e) Γ(R, V) := hBe
  obtain ⟨p, hpmonic, hpmap, hpcoeff, hpeval⟩ :=
    IsLocalization.Away.exists_monic_lift_with_supported_equalities
      p₁.appTop.hom p₂.appTop.hom (p₁.app U).hom
      (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom
      e he hst hs ht q hqmonic hqcoeff x hqeval
  exact ⟨e, p, he, hbasic, hpmonic, hpmap, hpcoeff, hpeval⟩

/-- The canonical characteristic polynomial on one rank stratum transports
through the open-scheme `topIso` and lifts to supported ambient patching data
for the specified idempotent cutting out that stratum.
-/
lemma exists_monic_lift_finrankOpen_charpoly
    {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁]
    [IsAffine X] (h : EquivalenceRelation p₁ p₂) (r : ℕ)
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e)
    (hbasic : X.basicOpen e = finrankOpen (p₁ := p₁) r)
    (x : Γ(X, ⊤)) :
    ∃ p : Γ(X, ⊤)[X], p.Monic ∧
      (∀ k, p₁.appTop (e * p.coeff k) =
        p₂.appTop (e * p.coeff k)) ∧ e * p.eval x = 0 := by
  let U := finrankOpen (p₁ := p₁) r
  let V := p₁ ⁻¹ᵁ U
  let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
    (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let _ : Algebra Γ(R, ⊤) Γ(R, V) :=
    (R.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let f := p₁ ∣_ U
  let g := morphismRestrictSnd h r
  let s : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) := f.appTop.hom.toIntAlgHom
  let t : Γ(U, ⊤) →ₐ[ℤ] Γ(V, ⊤) := g.appTop.hom.toIntAlgHom
  let _ : IsAffine U := isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine V := isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) := s.toRingHom.toAlgebra
  let _ : Module.Finite Γ(U, ⊤) Γ(V, ⊤) :=
    finite_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Module.Flat Γ(U, ⊤) Γ(V, ⊤) :=
    flat_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Algebra.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
    finitePresentation_appTop_morphismRestrict_finrankOpen (p₁ := p₁) r
  let _ : Module.FinitePresentation Γ(U, ⊤) Γ(V, ⊤) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite
      Γ(U, ⊤) Γ(V, ⊤)).mpr (by infer_instance)
  let _ : Module.Projective Γ(U, ⊤) Γ(V, ⊤) :=
    Module.Flat.projective_of_finitePresentation
  let hrank :=
    appTop_localizedModule_finrank_morphismRestrict_finrankOpen
      (p₁ := p₁) r
  let xU : Γ(U, ⊤) := U.topIso.inv
    (algebraMap Γ(X, ⊤) Γ(X, U) x)
  let q : Γ(U, ⊤)[X] := (LinearMap.projectiveCharpolyRev
    (Algebra.lmul Γ(U, ⊤) Γ(V, ⊤) (t xU))).reflect r
  have hqmonic : q.Monic :=
    projectiveCharpolyRev_reflect_monic_of_local_finrank
      (Algebra.lmul Γ(U, ⊤) Γ(V, ⊤) (t xU)) hrank
  have hqcoeff : ∀ k, s (q.coeff k) = t (q.coeff k) := by
    exact projectiveCharpolyRev_reflect_coeff_invariant_finrankOpen h r xU
  have hs : IsScalarTower.toAlgHom ℤ Γ(U, ⊤) Γ(V, ⊤) = s := rfl
  have hrel : EquivalenceRelation (specMap s) (specMap t) := by
    change EquivalenceRelation (Spec.map f.appTop) (Spec.map g.appTop)
    exact appTopFinrankOpen h r
  have ht : Function.Injective t :=
    (maps_injective_of_equivalenceRelation s t hrel).2
  have hqmap : q.map s.toRingHom = q.map t.toRingHom := by
    ext k
    simp only [Polynomial.coeff_map]
    change s (q.coeff k) = t (q.coeff k)
    exact hqcoeff k
  have hqeval : q.eval xU = 0 := by
    apply ht
    calc
      t (q.eval xU) = (q.map t.toRingHom).eval (t xU) := by
        exact (Polynomial.eval_map_apply (p := q)
          (f := t.toRingHom) xU).symm
      _ = (q.map s.toRingHom).eval (t xU) := by rw [hqmap]
      _ = 0 := by
        have hsRing : s.toRingHom = algebraMap Γ(U, ⊤) Γ(V, ⊤) := rfl
        rw [hsRing, Polynomial.eval_map_algebraMap]
        apply Algebra.lmul_injective (R := Γ(U, ⊤))
        simpa [← Polynomial.aeval_algHom_apply, q] using
          (projectiveCharpolyRev_reflect_aeval_eq_zero_of_local_finrank
            (Algebra.lmul Γ(U, ⊤) Γ(V, ⊤) (t xU)) hrank)
      _ = t 0 := (map_zero t).symm
  let qA : Γ(X, U)[X] := q.map U.topIso.hom.hom
  have hqAmonic : qA.Monic := hqmonic.map U.topIso.hom.hom
  have hf : f = p₁.resLE U V le_rfl := by
    simpa [f, U, V] using
      (p₁.resLE_eq_morphismRestrict (U := U)).symm
  have hg : g = p₂.resLE U V (preimage_finrankOpen_eq h r).le := by
    rw [← cancel_mono U.ι]
    simpa [g, U, V] using morphismRestrictSnd_ι h r
  have hfapp : (p₁.resLE U V le_rfl).appTop =
      U.topIso.hom ≫ p₁.app U ≫ V.topIso.inv := by
    change (p₁.resLE U V le_rfl).app ⊤ = _
    rw [Scheme.Hom.resLE_app_top, p₁.appLE_eq_app]
  have hgapp :
      (p₂.resLE U V (preimage_finrankOpen_eq h r).le).appTop =
        U.topIso.hom ≫
          p₂.appLE U V (preimage_finrankOpen_eq h r).le ≫
            V.topIso.inv := by
    change (p₂.resLE U V (preimage_finrankOpen_eq h r).le).app ⊤ = _
    rw [Scheme.Hom.resLE_app_top]
  have hqAcoeff : ∀ k,
      (p₁.app U) (qA.coeff k) =
        p₂.appLE U V (preimage_finrankOpen_eq h r).le (qA.coeff k) := by
    intro k
    have hk := hqcoeff k
    change f.appTop.hom (q.coeff k) = g.appTop.hom (q.coeff k) at hk
    rw [hf, hg] at hk
    rw [hfapp, hgapp] at hk
    have hk' := congr_arg V.topIso.hom.hom hk
    simpa only [qA, Polynomial.coeff_map, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply] using hk'
  have hqAeval : qA.eval (algebraMap Γ(X, ⊤) Γ(X, U) x) = 0 := by
    have hxU : U.topIso.hom.hom xU =
        algebraMap Γ(X, ⊤) Γ(X, U) x := by
      simpa only [xU] using Iso.inv_hom_id_apply U.topIso
        (algebraMap Γ(X, ⊤) Γ(X, U) x)
    rw [← hxU]
    change (q.map U.topIso.hom.hom).eval (U.topIso.hom.hom xU) = 0
    rw [Polynomial.eval_map_apply, hqeval, map_zero]
  obtain ⟨e', p, he', hbasic', hpmonic, -, hpcoeff, hpeval⟩ :=
    exists_monic_lift_finrankOpen_with_supported_equalities h r
      qA hqAmonic hqAcoeff x hqAeval
  have heq : e' = e := by
    apply Scheme.Opens.basicOpen_injOn_isIdempotentElem he' he
    exact hbasic'.trans hbasic.symm
  subst e'
  exact ⟨p, hpmonic, hpcoeff, hpeval⟩

/-- The object ring of an affine finite locally free internal equivalence
relation is integral over the equalizer of its two coordinate maps. This
formalizes the integrality conclusion and rank-piece argument of Stacks
Project [Lemma 39.23.4, tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ),
with rank strata as in
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI).
-/
lemma isIntegral_appTop_equalizer_of_equivalenceRelation
    {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁]
    [IsAffine X]
    (h : EquivalenceRelation p₁ p₂) (x : Γ(X, ⊤)) :
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    _root_.IsIntegral (AlgHom.equalizer s t) x := by
  dsimp only
  let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
  let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
  let _ : IsAffine R := isAffine_of_isAffineHom p₁
  let _ : Algebra Γ(X, ⊤) Γ(R, ⊤) := s.toRingHom.toAlgebra
  let _ : Module.Finite Γ(X, ⊤) Γ(R, ⊤) := p₁.finite_appTop
  let _ : Module.Flat Γ(X, ⊤) Γ(R, ⊤) := p₁.flat_appTop
  let _ : Algebra.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) := p₁.finitePresentation_appTop
  let _ : Module.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite Γ(X, ⊤) Γ(R, ⊤)).mpr
      (by infer_instance)
  let _ : Module.Projective Γ(X, ⊤) Γ(R, ⊤) :=
    Module.Flat.projective_of_finitePresentation
  let sr := s.toRingHom
  let tr := t.toRingHom
  have hrel : EquivalenceRelation (Spec.map (CommRingCat.ofHom sr))
      (Spec.map (CommRingCat.ofHom tr)) := appTop h
  have hSpec : sr.IsSpecEquivRel tr := by
    have hi {U V : Type u} [CommRing U] [CommRing V] :
        Function.Injective (fun f : U →+* V => Spec.map (CommRingCat.ofHom f)) := by
      intro f g he
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T _ x y hs ht
      apply hi
      apply hrel.right_cancellation
      · simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(X, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) hs
      · simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(X, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) ht
    · intro T _ x
      refine ⟨(Spec.preimage (Spec.map (CommRingCat.ofHom x) ≫ hrel.r)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
        simp [Category.assoc, hrel.reflexivity₁, hrel.reflexivity₂]
    · intro T _ x
      refine ⟨(Spec.preimage (Spec.map (CommRingCat.ofHom x) ≫ hrel.s)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
        simp [Category.assoc, hrel.symmetry₁, hrel.symmetry₂]
    · intro T _ x y he
      have hc : Spec.map (CommRingCat.ofHom x) ≫ Spec.map (CommRingCat.ofHom tr) =
          Spec.map (CommRingCat.ofHom y) ≫ Spec.map (CommRingCat.ofHom sr) := by
        simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
          (fun f : Γ(X, ⊤) →+* T => Spec.map (CommRingCat.ofHom f)) he
      let c := PullbackCone.mk (Spec.map (CommRingCat.ofHom x))
        (Spec.map (CommRingCat.ofHom y)) hc
      refine ⟨(Spec.preimage (hrel.isLimit.lift c ≫ hrel.t)).hom, ?_, ?_⟩
      all_goals
        apply hi
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_hom]
      · rw [Category.assoc, hrel.transitivity₁, ← Category.assoc]
        rw [hrel.isLimit.fac c WalkingCospan.left]
        rfl
      · rw [Category.assoc, hrel.transitivity₂, ← Category.assoc]
        rw [hrel.isLimit.fac c WalkingCospan.right]
        rfl
  change _root_.IsIntegral ((algebraMap Γ(X, ⊤) Γ(R, ⊤)).eqLocus tr) x
  exact hSpec.isIntegral.1 x

/-- Algebra-level form of
`isIntegral_appTop_equalizer_of_equivalenceRelation`: the full coordinate ring
is integral over the invariant equalizer, as in Stacks Project
[Lemma 39.23.4, tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ). -/
theorem algebraIsIntegral_appTop_equalizer_of_equivalenceRelation
    {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁]
    [IsAffine X]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    Algebra.IsIntegral (AlgHom.equalizer s t) Γ(X, ⊤) := by
  dsimp only
  constructor
  intro x
  exact isIntegral_appTop_equalizer_of_equivalenceRelation h x

end AlgebraicGeometry.EquivalenceRelation
