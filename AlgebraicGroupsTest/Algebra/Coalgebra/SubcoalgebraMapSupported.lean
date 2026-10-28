/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finsupp
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Map
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# A supported subcoalgebra and its collapsed carrier

For every field `K`, the diagonal coalgebra on `AddMonoidAlgebra K ℕ` has a nonzero
proper subcoalgebra supported on `{0, 1}`. Its carrier is the span of the two coordinate
vectors, so it is finitely generated and its subtype is module-finite. The ambient module
is not module-finite: its standard basis is indexed by `ℕ`.

The additive monoid homomorphism `0 : ℕ →+ ℕ` induces a coalgebra homomorphism that sends
both coordinate vectors to the vector at `0`. The submodule image of the supported
subcoalgebra is exactly the span of this single vector, again nonzero, proper and
module-finite. In particular, injectivity of the homomorphism is not needed for this
carrier calculation, and the field may be finite or have positive characteristic.

The subcoalgebras are constructed with `Subcoalgebra.ofSubmodule` and the group-like-span closure
lemma. Their coalgebras and inclusions are the restricted structures supplied by
`Subcoalgebra`. The coordinate vectors are group-like for these structures, by factoring
the scalar-source coalgebra homomorphisms through the inclusions. The image calculation
uses `Submodule.map_span` and does not require a subcoalgebra image construction. A companion
result identifies the subcoalgebra image by its carrier projection and gives the finite,
proper and nonzero properties of this image.

## References

* Mathlib's `AddMonoidAlgebra.supported`, `supported_eq_span_single`,
  `single_mem_span_single` and `basis` in `Mathlib.Algebra.MonoidAlgebra.Module`.
* Mathlib's diagonal coalgebra and `mapDomainBialgHom` in
  `Mathlib.RingTheory.Coalgebra.MonoidAlgebra` and
  `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`.
* `AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan` for tensor-square image closure,
  `GroupLikeHom` for scalar-source homomorphisms, and `Subcoalgebra.Hom` for the
  restricted coalgebra and inclusion. `Subcoalgebra.Map` supplies the image construction
  and its carrier projection used in the image-carrier result.
* Mathlib's `Submodule.map_span`, `Submodule.FG.map`, `Submodule.fg_span`,
  `Module.Finite.iff_fg` and `Module.not_finite_of_infinite_basis` for the carrier and
  finiteness calculations.
-/

@[expose] public section

open TauCeti


noncomputable section

universe u

namespace Coalgebra

variable (K : Type u) [Field K]

/-- The diagonal subcoalgebra whose coefficients are supported on `s`. -/
private abbrev supportedSubcoalgebra (s : Set ℕ) :
    Subcoalgebra K (AddMonoidAlgebra K ℕ) :=
  Subcoalgebra.ofSubmodule (AddMonoidAlgebra.supported K K s) <| by
    let D := Subcoalgebra.groupLikeSetSpan ((fun i : ℕ =>
      (⟨AddMonoidAlgebra.single i 1,
        AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) i⟩ :
          GroupLike K (AddMonoidAlgebra K ℕ))) '' s)
    have hD : D.toSubmodule = AddMonoidAlgebra.supported K K s := by
      rw [Subcoalgebra.groupLikeSetSpan_toSubmodule,
        AddMonoidAlgebra.supported_eq_span_single, Set.image_image]
    intro c hc
    have hcD : c ∈ D := by
      rw [← Subcoalgebra.mem_toSubmodule, hD]
      exact hc
    have hd := D.comul_mem hcD
    change Coalgebra.comul c ∈ LinearMap.range
      (_root_.TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype) at hd
    exact (congrArg (fun U : Submodule K (AddMonoidAlgebra K ℕ) =>
      Coalgebra.comul (R := K) c ∈
        LinearMap.range (_root_.TensorProduct.map U.subtype U.subtype)) hD).mp hd

private lemma supportedSubcoalgebra_toSubmodule (s : Set ℕ) :
    (supportedSubcoalgebra K s).toSubmodule = AddMonoidAlgebra.supported K K s :=
  rfl

private lemma supportedSubcoalgebra_span (s : Set ℕ) :
    (supportedSubcoalgebra K s).toSubmodule =
      Submodule.span K ((fun i : ℕ ↦ AddMonoidAlgebra.single i (1 : K)) '' s) := by
  rw [supportedSubcoalgebra_toSubmodule, AddMonoidAlgebra.supported_eq_span_single]

private lemma single_one_mem_supportedSubcoalgebra_iff (s : Set ℕ) (i : ℕ) :
    AddMonoidAlgebra.single i (1 : K) ∈ supportedSubcoalgebra K s ↔ i ∈ s := by
  change AddMonoidAlgebra.single i (1 : K) ∈ AddMonoidAlgebra.supported K K s ↔ i ∈ s
  rw [AddMonoidAlgebra.supported_eq_span_single]
  exact AddMonoidAlgebra.single_mem_span_single

private lemma supportedSubcoalgebra_ne_bot (s : Set ℕ) {i : ℕ} (hi : i ∈ s) :
    (supportedSubcoalgebra K s).toSubmodule ≠ ⊥ := by
  intro h
  have hm : AddMonoidAlgebra.single i (1 : K) ∈
      (supportedSubcoalgebra K s).toSubmodule :=
    (single_one_mem_supportedSubcoalgebra_iff K s i).mpr hi
  rw [h, Submodule.mem_bot] at hm
  exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) i).ne_zero hm

private lemma supportedSubcoalgebra_ne_top (s : Set ℕ) {i : ℕ} (hi : i ∉ s) :
    (supportedSubcoalgebra K s).toSubmodule ≠ ⊤ := by
  intro h
  apply hi
  apply (single_one_mem_supportedSubcoalgebra_iff K s i).mp
  change AddMonoidAlgebra.single i (1 : K) ∈ (supportedSubcoalgebra K s).toSubmodule
  rw [h]
  exact Submodule.mem_top

private lemma supportedSubcoalgebra_fg (s : Set ℕ) (hs : s.Finite) :
    (supportedSubcoalgebra K s).toSubmodule.FG := by
  rw [supportedSubcoalgebra_span]
  exact Submodule.fg_span (hs.image fun i : ℕ ↦ AddMonoidAlgebra.single i (1 : K))

/-- A coordinate vector viewed in the supported subcoalgebra. -/
private abbrev supportedVector (s : Set ℕ) (i : ℕ) (hi : i ∈ s) :
    (supportedSubcoalgebra K s).toSubmodule :=
  ⟨AddMonoidAlgebra.single i (1 : K),
    (single_one_mem_supportedSubcoalgebra_iff K s i).mpr hi⟩

private lemma supportedVector_isGroupLike (s : Set ℕ) (i : ℕ) (hi : i ∈ s) :
    IsGroupLikeElem K (supportedVector K s i hi) := by
  let g : GroupLike K (AddMonoidAlgebra K ℕ) :=
    ⟨AddMonoidAlgebra.single i (1 : K),
      AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) i⟩
  have hg (r : K) : GroupLike.coalgHomEquiv g r ∈ supportedSubcoalgebra K s := by
    change r • (g : AddMonoidAlgebra K ℕ) ∈ (supportedSubcoalgebra K s).toSubmodule
    simpa only [g] using
      (supportedSubcoalgebra K s).toSubmodule.smul_mem r
        ((single_one_mem_supportedSubcoalgebra_iff K s i).mpr hi)
  let f := (GroupLike.coalgHomEquiv g).codRestrict (supportedSubcoalgebra K s) hg
  have hf : f 1 = supportedVector K s i hi := by
    apply Subtype.ext
    exact (CoalgHom.coe_codRestrict (GroupLike.coalgHomEquiv g)
      (supportedSubcoalgebra K s) hg 1).trans
        (by simp [GroupLike.coalgHomEquiv_apply, g])
  have h := ((isGroupLikeElem_self (R := K) (r := (1 : K))).mpr rfl).map f
  rwa [hf] at h

/-- The coalgebra homomorphism induced by the zero additive endomorphism of `ℕ`. -/
private abbrev collapse : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
  (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom

private lemma collapse_single (i : ℕ) (r : K) :
    collapse K (AddMonoidAlgebra.single i r) = AddMonoidAlgebra.single 0 r := by
  change AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)
    (AddMonoidAlgebra.single i r) = AddMonoidAlgebra.single 0 r
  rw [AddMonoidAlgebra.mapDomainBialgHom_single]
  rfl

private lemma collapse_map_supported_pair :
    Submodule.map (collapse K).toLinearMap
        (supportedSubcoalgebra K ({0, 1} : Set ℕ)).toSubmodule =
      (supportedSubcoalgebra K ({0} : Set ℕ)).toSubmodule := by
  rw [supportedSubcoalgebra_span, supportedSubcoalgebra_span,
    Set.image_pair, Set.image_singleton, Submodule.map_span, Set.image_pair]
  change Submodule.span K
      ({collapse K (AddMonoidAlgebra.single 0 (1 : K)),
        collapse K (AddMonoidAlgebra.single 1 (1 : K))} : Set (AddMonoidAlgebra K ℕ)) =
    Submodule.span K ({AddMonoidAlgebra.single 0 (1 : K)} : Set (AddMonoidAlgebra K ℕ))
  simp only [collapse_single, Set.pair_eq_singleton]

/-- In the diagonal coalgebra on the additive monoid algebra of `ℕ` over any field, the
subcoalgebra supported on `{0, 1}` is nonzero, proper and module-finite, although the
ambient module is not module-finite. Its coordinate vectors are group-like for the
restricted coalgebra, and collapse along the zero additive endomorphism has carrier
exactly the nonzero proper module-finite span of the vector at `0`. -/
theorem exists_finite_proper_subcoalgebra_addMonoidAlgebra_nat_map_zero :
    let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    ∃ D : Subcoalgebra K (AddMonoidAlgebra K ℕ),
      D.toSubmodule = AddMonoidAlgebra.supported K K ({0, 1} : Set ℕ) ∧
      D.toSubmodule = Submodule.span K
        ({AddMonoidAlgebra.single 0 (1 : K), AddMonoidAlgebra.single 1 (1 : K)} :
          Set (AddMonoidAlgebra K ℕ)) ∧
      D.toSubmodule ≠ ⊥ ∧ D.toSubmodule ≠ ⊤ ∧ D.toSubmodule.FG ∧
      Module.Finite K D.toSubmodule ∧ ¬ Module.Finite K (AddMonoidAlgebra K ℕ) ∧
      (∃ x₀ x₁ : D.toSubmodule,
        D.subtype x₀ = AddMonoidAlgebra.single 0 (1 : K) ∧
        D.subtype x₁ = AddMonoidAlgebra.single 1 (1 : K) ∧
        IsGroupLikeElem K x₀ ∧ IsGroupLikeElem K x₁) ∧
      (let I := Submodule.map f.toLinearMap D.toSubmodule;
        I = Submodule.span K
          ({AddMonoidAlgebra.single 0 (1 : K)} : Set (AddMonoidAlgebra K ℕ)) ∧
        I ≠ ⊥ ∧ I ≠ ⊤ ∧ I.FG ∧ Module.Finite K I ∧
        f (AddMonoidAlgebra.single 0 (1 : K)) = AddMonoidAlgebra.single 0 (1 : K) ∧
        f (AddMonoidAlgebra.single 1 (1 : K)) = AddMonoidAlgebra.single 0 (1 : K)) := by
  let D := supportedSubcoalgebra K ({0, 1} : Set ℕ)
  have hDfg : D.toSubmodule.FG := supportedSubcoalgebra_fg K _ (by simp)
  have hDspan : D.toSubmodule = Submodule.span K
      ({AddMonoidAlgebra.single 0 (1 : K), AddMonoidAlgebra.single 1 (1 : K)} :
        Set (AddMonoidAlgebra K ℕ)) := by
    simpa only [Set.image_pair] using supportedSubcoalgebra_span K ({0, 1} : Set ℕ)
  refine ⟨D, supportedSubcoalgebra_toSubmodule K _, hDspan,
    supportedSubcoalgebra_ne_bot K _ (i := 0) (by simp),
    supportedSubcoalgebra_ne_top K _ (i := 2) (by simp), hDfg,
    Module.Finite.iff_fg.mpr hDfg,
    Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℕ K), ?_, ?_⟩
  · exact ⟨supportedVector K _ 0 (by simp), supportedVector K _ 1 (by simp), rfl, rfl,
      supportedVector_isGroupLike K _ 0 (by simp),
      supportedVector_isGroupLike K _ 1 (by simp)⟩
  · have hIfg : (Submodule.map (collapse K).toLinearMap D.toSubmodule).FG :=
      hDfg.map (collapse K).toLinearMap
    have hIspan : (Submodule.map (collapse K).toLinearMap D.toSubmodule) =
        Submodule.span K
          ({AddMonoidAlgebra.single 0 (1 : K)} : Set (AddMonoidAlgebra K ℕ)) := by
      rw [collapse_map_supported_pair, supportedSubcoalgebra_span, Set.image_singleton]
    refine ⟨hIspan, ?_, ?_, hIfg, Module.Finite.iff_fg.mpr hIfg,
      collapse_single K 0 1, collapse_single K 1 1⟩
    · rw [collapse_map_supported_pair]
      exact supportedSubcoalgebra_ne_bot K _ (i := 0) (by simp)
    · rw [collapse_map_supported_pair]
      exact supportedSubcoalgebra_ne_top K _ (i := 1) (by simp)

/-- Collapse of the supported two-coordinate subcoalgebra has image carrier equal to the
span of the coordinate vector at zero. Both the source and image are nonzero, proper and
module-finite. The carrier calculation uses the subcoalgebra image carrier projection and
the submodule image calculation; the image's nonzeroness follows from zero reflection. -/
theorem exists_finite_proper_subcoalgebra_addMonoidAlgebra_nat_image_zero :
    let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    ∃ D : Subcoalgebra K (AddMonoidAlgebra K ℕ),
      D.toSubmodule = AddMonoidAlgebra.supported K K ({0, 1} : Set ℕ) ∧
      D.toSubmodule ≠ ⊥ ∧ D.toSubmodule ≠ ⊤ ∧ D.toSubmodule.FG ∧ Module.Finite K D.toSubmodule ∧
      (Subcoalgebra.map f D).toSubmodule = Submodule.span K
        ({AddMonoidAlgebra.single 0 (1 : K)} : Set (AddMonoidAlgebra K ℕ)) ∧
      (Subcoalgebra.map f D).toSubmodule ≠ ⊥ ∧
      (Subcoalgebra.map f D).toSubmodule ≠ ⊤ ∧
      (Subcoalgebra.map f D).toSubmodule.FG ∧ Module.Finite K (Subcoalgebra.map f D).toSubmodule
          := by
  obtain ⟨D, hDsupport, _hDspan, hDbot, hDtop, hDfg, hDfinite, _hinfinite, _hvectors, hI⟩ :=
    exists_finite_proper_subcoalgebra_addMonoidAlgebra_nat_map_zero K
  rcases hI with ⟨hIspan, _hIbot, hItop, hIfg, _hIfinite, _hzero, _hone⟩
  have hmapfg : (Subcoalgebra.map (collapse K) D).toSubmodule.FG := by
    simpa only [Subcoalgebra.map_toSubmodule] using hIfg
  refine ⟨D, hDsupport, hDbot, hDtop, hDfg, hDfinite, ?_, ?_, ?_, hmapfg,
    Module.Finite.iff_fg.mpr hmapfg⟩
  · simpa only [Subcoalgebra.map_toSubmodule] using hIspan
  · exact fun h => hDbot ((Subcoalgebra.map_toSubmodule_eq_bot_iff (collapse K) D).mp h)
  · simpa only [Subcoalgebra.map_toSubmodule] using hItop

end Coalgebra
