/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Map
public import AlgebraicGroupsTest.Algebra.Coalgebra.MonoidAlgebraCollapse
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# A finitely generated image of an infinitely generated subcoalgebra

The whole diagonal coalgebra on `AddMonoidAlgebra K ℕ` is a subcoalgebra whose underlying
submodule is top. Its canonical restricted coalgebra has group-like coordinate vectors.
Collapse along the zero additive endomorphism of `ℕ` maps this subcoalgebra onto the
nonzero proper line spanned by the coordinate vector at zero. The image carrier is finitely
generated, but the source carrier is not: its basis is indexed by the infinite type `ℕ`.

Thus finite generation of the image does not imply finite generation of the source without
injectivity on the source subcoalgebra. The collapse is not injective on this carrier, nor
is its composite with the canonical inclusion injective. The construction works over every
field, and is also instantiated over `ℚ`. No finite-dimensional ambient module is assumed.
Top and bottom in the statements refer only to submodules, not to subcoalgebras.

## References

The diagonal coalgebra, index-collapse homomorphism, and its range and kernel calculations
are supplied by Mathlib and `AlgebraicGroupsTest.Algebra.Coalgebra.MonoidAlgebraCollapse`.
The full carrier uses `Subcoalgebra.ofSubmodule`, the group-like-span closure theorem in
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan`, and `Module.Basis.span_eq`.
The restricted coalgebra, inclusion, and codomain restriction are those of
`Subcoalgebra.Hom`; the image and its carrier projection are those of `Subcoalgebra.Map`.
Non-finite generation uses Mathlib's `Module.not_finite_of_infinite_basis` and
`Module.finite_def`; subtype finiteness uses `Module.Finite.iff_fg`.
-/

@[expose] public section

open TauCeti


noncomputable section

universe u

open scoped TensorProduct

namespace Coalgebra

variable (K : Type u) [Field K]

/-- The full diagonal coalgebra, packaged using its underlying top submodule. -/
private abbrev wholeSubcoalgebra : Subcoalgebra K (AddMonoidAlgebra K ℕ) :=
  ⊤

private lemma wholeSubcoalgebra_toSubmodule :
    (wholeSubcoalgebra K).toSubmodule = ⊤ :=
  Subcoalgebra.top_toSubmodule

private lemma mem_wholeSubcoalgebra (x : AddMonoidAlgebra K ℕ) :
    x ∈ wholeSubcoalgebra K := by
  exact Subcoalgebra.mem_top _

/-- Identity with its codomain restricted to the full carrier. -/
private abbrev wholeLift : AddMonoidAlgebra K ℕ →ₗc[K] (wholeSubcoalgebra K).toSubmodule :=
  (CoalgHom.id K (AddMonoidAlgebra K ℕ)).codRestrict (wholeSubcoalgebra K)
    (fun x => mem_wholeSubcoalgebra K x)

private lemma subtype_wholeLift (x : AddMonoidAlgebra K ℕ) :
    (wholeSubcoalgebra K).subtype (wholeLift K x) = x :=
  rfl

private lemma wholeLift_basis_isGroupLike (i : ℕ) :
    IsGroupLikeElem K (wholeLift K (AddMonoidAlgebra.basis ℕ K i)) := by
  have hi : IsGroupLikeElem K (AddMonoidAlgebra.basis ℕ K i) := by
    rw [AddMonoidAlgebra.basis_apply]
    exact AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) i
  exact hi.map (wholeLift K)

private lemma wholeSubcoalgebra_not_fg : ¬ (wholeSubcoalgebra K).toSubmodule.FG := by
  rw [wholeSubcoalgebra_toSubmodule]
  intro hfg
  exact Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℕ K)
    (Module.finite_def.mpr hfg)

private lemma wholeSubcoalgebra_not_finite : ¬ Module.Finite K (wholeSubcoalgebra K) := by
  intro hfinite
  exact wholeSubcoalgebra_not_fg K (Module.Finite.iff_fg.mp hfinite)

/-- The whole diagonal subcoalgebra on `ℕ` has non-finitely-generated carrier, whereas
its collapse image is the nonzero proper finitely generated coordinate line. Its
coordinate vectors are group-like for the canonical restricted coalgebra. The collapse
fails injectivity both on the carrier and after composition with the inclusion. -/
theorem exists_non_fg_subcoalgebra_with_fg_collapse_image :
    let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    ∃ D : Subcoalgebra K (AddMonoidAlgebra K ℕ),
      D.toSubmodule = ⊤ ∧
      (∀ i : ℕ, ∃ x : D.toSubmodule,
        D.subtype x = AddMonoidAlgebra.basis ℕ K i ∧
        counit (R := K) x = 1 ∧ comul (R := K) x = x ⊗ₜ[K] x ∧
        f (D.subtype x) = AddMonoidAlgebra.basis ℕ K 0) ∧
      ¬ D.toSubmodule.FG ∧ ¬ Module.Finite K D.toSubmodule ∧
      (Subcoalgebra.map f D).toSubmodule = Submodule.span K
        ({AddMonoidAlgebra.basis ℕ K 0} : Set (AddMonoidAlgebra K ℕ)) ∧
      (Subcoalgebra.map f D).toSubmodule ≠ ⊥ ∧
      (Subcoalgebra.map f D).toSubmodule ≠ ⊤ ∧
      (Subcoalgebra.map f D).toSubmodule.FG ∧
      Module.Finite K (Subcoalgebra.map f D).toSubmodule ∧
      ¬ Set.InjOn f (D : Set (AddMonoidAlgebra K ℕ)) ∧
      ¬ Function.Injective (f.comp D.subtype) := by
  let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
    (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
  obtain ⟨_hsingle, hbasis, _hvector, _hzero, _hker, hnotinj⟩ :=
    AddMonoidAlgebra.mapDomainBialgHom_zero_basis_and_kernel K
  obtain ⟨hspan, hbot, htop, _hmem, _hnotmem, hfg, _hfinite, _hinfinite⟩ :=
    AddMonoidAlgebra.mapDomainBialgHom_zero_range_finite K
  have hcarrier : (Subcoalgebra.map f (wholeSubcoalgebra K)).toSubmodule =
      LinearMap.range f.toLinearMap := by
    rw [Subcoalgebra.map_toSubmodule, wholeSubcoalgebra_toSubmodule, Submodule.map_top]
  have himagefg : (Subcoalgebra.map f (wholeSubcoalgebra K)).toSubmodule.FG := by
    rw [hcarrier]
    exact hfg
  refine ⟨wholeSubcoalgebra K, wholeSubcoalgebra_toSubmodule K, ?_,
    wholeSubcoalgebra_not_fg K, wholeSubcoalgebra_not_finite K,
    hcarrier.trans hspan, ?_, ?_, himagefg, Module.Finite.iff_fg.mpr himagefg, ?_, ?_⟩
  · intro i
    have hi := wholeLift_basis_isGroupLike K i
    refine ⟨wholeLift K (AddMonoidAlgebra.basis ℕ K i), subtype_wholeLift K _,
      hi.counit_eq_one, hi.comul_eq_tmul_self, ?_⟩
    rw [subtype_wholeLift]
    exact (hbasis i).2.2
  · rw [hcarrier]
    exact hbot
  · rw [hcarrier]
    exact htop
  · intro hinj
    apply hnotinj
    intro x y hxy
    exact hinj (mem_wholeSubcoalgebra K x) (mem_wholeSubcoalgebra K y) hxy
  · intro hinj
    apply hnotinj
    intro x y hxy
    have hlift : wholeLift K x = wholeLift K y := by
      apply hinj
      simpa only [CoalgHom.coe_comp, Function.comp_apply, subtype_wholeLift] using hxy
    have hcoe := congrArg (fun z : wholeSubcoalgebra K =>
      (wholeSubcoalgebra K).subtype z) hlift
    simpa only [subtype_wholeLift] using hcoe

-- The full carrier and the rank-one collapse image occur over the rational field.
example :
    let f : AddMonoidAlgebra ℚ ℕ →ₗc[ℚ] AddMonoidAlgebra ℚ ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom ℚ (0 : ℕ →+ ℕ)).toCoalgHom
    ∃ D : Subcoalgebra ℚ (AddMonoidAlgebra ℚ ℕ),
      D.toSubmodule = ⊤ ∧ ¬ D.toSubmodule.FG ∧
      (Subcoalgebra.map f D).toSubmodule = Submodule.span ℚ
        ({AddMonoidAlgebra.basis ℕ ℚ 0} : Set (AddMonoidAlgebra ℚ ℕ)) ∧
      (Subcoalgebra.map f D).toSubmodule ≠ ⊥ ∧
      (Subcoalgebra.map f D).toSubmodule.FG ∧
      ¬ Set.InjOn f (D : Set (AddMonoidAlgebra ℚ ℕ)) := by
  obtain ⟨D, hD, _hvectors, hnotfg, _hnotfinite, hspan, hbot, _htop, hfg,
    _hfinite, hnotinj, _hnotcompinj⟩ :=
    exists_non_fg_subcoalgebra_with_fg_collapse_image ℚ
  exact ⟨D, hD, hnotfg, hspan, hbot, hfg, hnotinj⟩

end Coalgebra
