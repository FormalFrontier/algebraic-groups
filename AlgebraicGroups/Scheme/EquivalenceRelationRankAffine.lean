/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Scheme.ClopenAffine
public import AlgebraicGroups.Scheme.EquivalenceRelationRank
public import Mathlib.RingTheory.Idempotents

@[expose] public section

/-!
# Affine rank strata of finite flat equivalence relations

For a finite flat internal equivalence relation over an affine scheme, every
locally finitely presented rank stratum is an affine clopen. One idempotent
simultaneously presents its coordinate ring and the coordinate ring of its
common relation preimage as away localizations. The two relation maps agree on
that idempotent, and both global-section restriction squares commute.

This is localization infrastructure for rank-stratum descent. It does not
identify localized equalizers or prove quotient effectivity.

The rank pieces come from the invariant decomposition of finite locally free
groupoids. For affine targets, clopen opens have unique idempotent defining
elements; that uniqueness, rather than equality of arbitrary basic-open
generators, makes the two images of a rank idempotent agree.

## References

* The Stacks Project, Lemma 39.23.3
  ([tag 03BI](https://stacks.math.columbia.edu/tag/03BI)), supplies the
  invariant rank-decomposition antecedent.
* `AlgebraicGroups.Scheme.ClopenAffine` supplies idempotent models of
  clopen affine opens, their finite-morphism preimages, and restriction
  squares. Mathlib, `Mathlib.RingTheory.Idempotents`, supplies the complete
  orthogonal-idempotent API.
-/

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁]

/-- Over an affine target, every locally finitely presented rank stratum is
affine. -/
lemma isAffineOpen_finrankOpen [LocallyOfFinitePresentation p₁] [IsAffine X]
    (r : ℕ) : IsAffineOpen (finrankOpen (p₁ := p₁) r) := by
  apply (finrankOpen (p₁ := p₁) r).isAffineOpen_of_isClopen
  change IsClopen {x : X | p₁.finrank x = r}
  exact isClopen_finrank_fiber (p₁ := p₁) r

/-- Restriction from an affine target to a rank stratum is surjective on
global sections. -/
lemma appTop_surjective_finrankOpen [LocallyOfFinitePresentation p₁]
    [IsAffine X] (r : ℕ) :
    Function.Surjective (finrankOpen (p₁ := p₁) r).ι.appTop := by
  apply (finrankOpen (p₁ := p₁) r).appTop_surjective_of_isClopen
  change IsClopen {x : X | p₁.finrank x = r}
  exact isClopen_finrank_fiber (p₁ := p₁) r

/-- The coordinate ring of an affine rank stratum is localization away from
an idempotent cutting out exactly that stratum. -/
lemma exists_isIdempotent_isLocalization_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X] (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U ∧
      IsLocalization.Away e Γ(X, U) := by
  dsimp only
  apply (finrankOpen (p₁ := p₁) r).exists_isIdempotent_isLocalization
  change IsClopen {x : X | p₁.finrank x = r}
  exact isClopen_finrank_fiber (p₁ := p₁) r

/-- The common preimage of an affine rank stratum under the first projection
is affine. -/
lemma isAffineOpen_preimage_finrankOpen [LocallyOfFinitePresentation p₁]
    [IsAffine X] (r : ℕ) :
    IsAffineOpen (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
  (isAffineOpen_finrankOpen (p₁ := p₁) r).preimage p₁

/-- On an invariant affine rank stratum, one idempotent simultaneously models
the target restriction and its common relation preimage. Its images under the
two relation maps agree, and both global-section restriction squares commute.
Idempotence makes equality of the two preimage basic opens imply equality of
the idempotent images.
-/
lemma exists_finrankOpen_localizations_and_squares
    [LocallyOfFinitePresentation p₁] [IsAffine X]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(R, ⊤) Γ(R, V) :=
      (R.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      X.basicOpen e = U ∧ IsLocalization.Away e Γ(X, U) ∧
      IsLocalization.Away (p₁.appTop e) Γ(R, V) ∧
      p₁.appTop e = p₂.appTop e ∧
      (algebraMap Γ(R, ⊤) Γ(R, V)).comp p₁.appTop.hom =
        (p₁.app U).hom.comp (algebraMap Γ(X, ⊤) Γ(X, U)) ∧
      (algebraMap Γ(R, ⊤) Γ(R, V)).comp p₂.appTop.hom =
        (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom.comp
          (algebraMap Γ(X, ⊤) Γ(X, U)) := by
  dsimp only
  let _ : IsAffine R := isAffine_of_isAffineHom p₁
  let U := finrankOpen (p₁ := p₁) r
  have hU : IsClopen (U : Set X) := by
    change IsClopen {x : X | p₁.finrank x = r}
    exact isClopen_finrank_fiber (p₁ := p₁) r
  obtain ⟨e, he, hbasic, hAe, hRe⟩ :=
    p₁.exists_isIdempotent_isLocalization_and_preimage U hU
  refine ⟨e, he, hbasic, hAe, hRe, ?_, ?_, ?_⟩
  · apply Scheme.Hom.appTop_eq_of_preimage_basicOpen_eq p₁ p₂ e he
    rw [hbasic]
    exact preimage_finrankOpen_eq h r
  · exact p₁.appTop_restriction_square U
  · exact p₂.appTop_restriction_square_of_eq U (p₁ ⁻¹ᵁ U)
      (preimage_finrankOpen_eq h r)

/-- On a compact affine target, the finitely many nonempty rank strata are cut
out by a complete orthogonal family of invariant idempotents, refining the
rank decomposition of Stacks Project
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI). -/
lemma exists_completeOrthogonalIdempotents_finrankOpen
    [LocallyOfFinitePresentation p₁] [IsAffine X]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    let I := Set.range p₁.finrank
    ∃ e : I → Γ(X, ⊤),
      @CompleteOrthogonalIdempotents Γ(X, ⊤) _ I
        (finrankRangeFintype (p₁ := p₁)) e ∧
      ∀ i, X.basicOpen (e i) = finrankOpen (p₁ := p₁) i.1 ∧
        p₁.appTop (e i) = p₂.appTop (e i) := by
  dsimp only
  let _ : Fintype (Set.range p₁.finrank) :=
    finrankRangeFintype (p₁ := p₁)
  let _ : IsAffine R := isAffine_of_isAffineHom p₁
  choose e he hbasic using fun i : Set.range p₁.finrank ↦
    (finrankOpen (p₁ := p₁) i.1).exists_isIdempotent_basicOpen_eq
      (by
        change IsClopen {x : X | p₁.finrank x = i.1}
        exact isClopen_finrank_fiber (p₁ := p₁) i.1)
  have hortho : Pairwise (e · * e · = 0) := by
    intro i j hij
    apply Scheme.Opens.basicOpen_injOn_isIdempotentElem
        ((he i).mul (he j)) IsIdempotentElem.zero
    rw [Scheme.basicOpen_mul, hbasic i, hbasic j, Scheme.basicOpen_zero]
    apply Opens.ext
    ext x
    constructor
    · intro hx
      have hi : p₁.finrank x = i.1 := mem_finrankOpen (p₁ := p₁) i.1 x |>.mp hx.1
      have hj : p₁.finrank x = j.1 := mem_finrankOpen (p₁ := p₁) j.1 x |>.mp hx.2
      exact (hij (Subtype.ext (hi.symm.trans hj))).elim
    · intro hx
      exact hx.elim
  let ho : OrthogonalIdempotents e := ⟨he, hortho⟩
  have hcover : ⨆ i : Set.range p₁.finrank,
      finrankOpen (p₁ := p₁) i.1 = ⊤ := by
    apply le_antisymm le_top
    intro x _
    let i : Set.range p₁.finrank := ⟨p₁.finrank x, ⟨x, rfl⟩⟩
    exact (le_iSup (fun i : Set.range p₁.finrank ↦
      finrankOpen (p₁ := p₁) i.1) i) (mem_finrankOpen (p₁ := p₁) i.1 x |>.mpr rfl)
  have hsum_basicOpen : X.basicOpen (∑ i, e i) = ⊤ := by
    apply le_antisymm le_top
    calc
      ⊤ = ⨆ i : Set.range p₁.finrank,
          finrankOpen (p₁ := p₁) i.1 := hcover.symm
      _ ≤ X.basicOpen (∑ i, e i) := iSup_le fun i ↦ by
        rw [← hbasic i]
        have hi : e i * ∑ j, e j = e i := by
          simpa using ho.mul_sum_of_mem (s := Finset.univ) (Finset.mem_univ i)
        rw [← hi, Scheme.basicOpen_mul]
        exact inf_le_right
  have hsum_idem : IsIdempotentElem (∑ i, e i) := by
    simpa using ho.isIdempotentElem_sum (s := Finset.univ)
  have hcomplete : ∑ i, e i = 1 := by
    apply Scheme.Opens.basicOpen_injOn_isIdempotentElem hsum_idem IsIdempotentElem.one
    simpa using hsum_basicOpen
  refine ⟨e, ⟨ho, hcomplete⟩, fun i ↦ ⟨hbasic i, ?_⟩⟩
  apply Scheme.Hom.appTop_eq_of_preimage_basicOpen_eq p₁ p₂ (e i) (he i)
  rw [hbasic i]
  exact preimage_finrankOpen_eq h i.1

end AlgebraicGeometry.EquivalenceRelation
