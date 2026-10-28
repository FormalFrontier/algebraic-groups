/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroupsTest.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Right comodules with proper finite support and change of coalgebra

The scalar coalgebra `ℕ` coacts on `ℕ →₀ ZMod 2` by `m ↦ m ⊗ 1`.
The ambient module is infinite, not module-finite, not projective and not free.
Its submodule supported on `{0, 1}` is specified, proper, nonzero and finitely
generated. Its subtype coact is the inverse right unitor directly.
Coaction cancellation separates a supported coordinate vector from one outside
this submodule, and zero reflection preserves the nonzero torsion vector.

The projective ideal `(3)` in `ZMod 6` coacts on its countable direct sum by
`m ↦ m ⊗ e₃`. Here the counit of `e₃` is three, not one: counitality follows
from `3 • m = m`, not from a group-like element or a surjective counit.
Again the submodule supported on `{0, 1}` is proper, nonzero and finitely generated,
with a directly constructed subtype coact. The projectivity, nonfreeness and
proper counit image reuse the existing idempotent-ideal and split-tensor examples.
Neither direct subtype coact uses the general induced-subtype construction.

The boundary clients include empty and zero finite subsets, zero ambient modules,
trivial scalars, and independent universes. In the scalar and ideal examples,
the subtype coacts are specified directly; finite generation and properness
follow from the supported submodules. Separate clients apply the finite-containment
theorem to finite subsets of these comodules.

The regular coalgebra `MonoidAlgebra ℕ ℕ` has an infinite basis over the genuine
semiring `ℕ`. Its stock counit identifies two distinct nonzero basis points.
Changing the regular coact along this counit gives the existing scalar
coact, retaining the module factor: each basis point maps to itself tensored
with one. The changed coact still separates those points, and the counit
itself is colinear from the changed regular source to the regular scalar target.

## References

Mathlib supplies Finsupp, supported submodules, scalar and monoid-algebra
coalgebras, and the standard monoid-algebra basis. The idempotent-ideal coalgebra
and split-tensor examples supply the ideal model.
-/

@[expose] public section

open TauCeti


universe u v w

open scoped TensorProduct

open TauCeti (Comodule)


namespace ComoduleExamples

private theorem twoSupported_fg {R A : Type*} [Semiring R] [AddCommMonoid A]
    [Module R A] [Finite A] : (Finsupp.supported A R ({0, 1} : Set ℕ)).FG := by
  classical
  let : Fintype ({0, 1} : Set ℕ) := ((Set.finite_singleton 1).insert 0).fintype
  let : Fintype A := Fintype.ofFinite A
  let : Finite (Finsupp.supported A R ({0, 1} : Set ℕ)) :=
    Finite.of_injective (Finsupp.supportedEquivFinsupp (R := R) ({0, 1} : Set ℕ))
      (Finsupp.supportedEquivFinsupp (R := R) ({0, 1} : Set ℕ)).injective
  exact Module.Finite.iff_fg.mp inferInstance

private theorem twoSupported_nonzero_proper {R A : Type*} [Semiring R] [AddCommMonoid A]
    [Module R A] (a : A) (ha : a ≠ 0) :
    Finsupp.supported A R ({0, 1} : Set ℕ) ≠ ⊥ ∧
      Finsupp.supported A R ({0, 1} : Set ℕ) ≠ ⊤ := by
  have hzero : Finsupp.single 0 a ∈ Finsupp.supported A R ({0, 1} : Set ℕ) :=
    Finsupp.single_mem_supported R a (by simp)
  refine ⟨?_, ?_⟩
  · intro h
    have hz : (Finsupp.single 0 a : ℕ →₀ A) = 0 := (Submodule.mem_bot R).mp (h ▸ hzero)
    exact ha (by simpa using congrArg (fun f : ℕ →₀ A ↦ f 0) hz)
  · intro h
    have htwo : Finsupp.single 2 a ∈ Finsupp.supported A R ({0, 1} : Set ℕ) := by
      rw [h]
      exact Submodule.mem_top
    have hz := (Finsupp.mem_supported' R _).mp htwo 2 (by simp)
    exact ha (by simpa using hz)

/-- The countable characteristic-two ambient module, with its ordinary natural module structure. -/
abbrev TorsionAmbient := ℕ →₀ ZMod 2

/-- The scalar right coact on the countable torsion module. -/
@[instance_reducible] noncomputable def torsionComodule : Comodule ℕ ℕ TorsionAmbient :=
  Comodule.trivial (R := ℕ) («C» := ℕ) (M := TorsionAmbient)

attribute [local instance] torsionComodule

@[simp] theorem torsionComodule_coact (m : TorsionAmbient) :
    torsionComodule.coact m = m ⊗ₜ[ℕ] 1 := rfl

/-- The specified scalar subcomodule with support contained in `{0, 1}`. -/
noncomputable def torsionSupported : Subcomodule ℕ ℕ TorsionAmbient where
  carrier := Finsupp.supported (ZMod 2) ℕ ({0, 1} : Set ℕ)
  coact_mem' := by
    intro m hm
    exact ⟨(⟨m, hm⟩ : Finsupp.supported (ZMod 2) ℕ ({0, 1} : Set ℕ)) ⊗ₜ[ℕ] 1, rfl⟩

@[simp] theorem mem_torsionSupported (m : TorsionAmbient) :
    m ∈ torsionSupported ↔ ∀ n ∉ ({0, 1} : Set ℕ), m n = 0 :=
  Finsupp.mem_supported' ℕ m

/-- Both specified coordinate vectors lie in the scalar subcomodule. -/
theorem torsionSupported_contains_coordinates :
    Finsupp.single 0 (1 : ZMod 2) ∈ torsionSupported ∧
      Finsupp.single 1 (1 : ZMod 2) ∈ torsionSupported := by
  constructor <;> exact Finsupp.single_mem_supported ℕ _ (by simp)

/-- This witness is finitely generated, nonzero and proper without using finite containment. -/
theorem torsionSupported_fg_nonzero_proper :
    torsionSupported.toSubmodule.FG ∧ torsionSupported.toSubmodule ≠ ⊥ ∧
      torsionSupported.toSubmodule ≠ ⊤ :=
  ⟨twoSupported_fg, twoSupported_nonzero_proper (1 : ZMod 2) one_ne_zero⟩

/-- The scalar subtype coact is constructed directly by the right unitor. -/
@[instance_reducible] noncomputable def torsionSupportedComodule : Comodule ℕ ℕ
    torsionSupported.toSubmodule :=
  Comodule.trivial (R := ℕ) («C» := ℕ) (M := torsionSupported.toSubmodule)

@[simp] theorem torsionSupportedComodule_coact (m : torsionSupported.toSubmodule) :
    torsionSupportedComodule.coact m = m ⊗ₜ[ℕ] 1 := rfl

/-- Inclusion of the directly constructed scalar subtype comodule is colinear. -/
theorem torsionSupported_subtype_colinear :
    torsionSupported.toSubmodule.subtype.rTensor ℕ ∘ₗ torsionSupportedComodule.coact =
      torsionComodule.coact ∘ₗ torsionSupported.toSubmodule.subtype :=
  by ext m; simp

/-- The torsion ambient carrier is infinite. -/
theorem torsionAmbient_infinite : Infinite TorsionAmbient := inferInstance

/-- Finite supports obstruct finite generation of the whole countable torsion module. -/
theorem torsionAmbient_not_finite : ¬ Module.Finite ℕ TorsionAmbient := by
  classical
  intro h
  rw [Module.finite_def, Submodule.fg_def] at h
  obtain ⟨S, hS, hspan⟩ := h
  have hfinite : (⋃ x ∈ S, (x.support : Set ℕ)).Finite :=
    hS.biUnion (fun x _ ↦ x.support.finite_toSet)
  obtain ⟨n, hn⟩ := hfinite.exists_notMem
  have hsingle : Finsupp.single n (1 : ZMod 2) ∈ Submodule.span ℕ S := by
    rw [hspan]
    exact Submodule.mem_top
  have hsupported := Finsupp.span_le_supported_biUnion_support (R := ℕ) S hsingle
  have hz := (Finsupp.mem_supported' ℕ _).mp hsupported n hn
  simp at hz

/-- The first coordinate vector in the torsion ambient is nonzero. -/
theorem torsionVector_ne_zero : (Finsupp.single 0 (1 : ZMod 2) : TorsionAmbient) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
    (by simpa using congrArg (fun f : TorsionAmbient ↦ f 0) h)

/-- Coaction cancellation distinguishes a supported coordinate from one outside the support. -/
theorem torsionSupported_coact_ne_outside :
    torsionComodule.coact (Finsupp.single 0 (1 : ZMod 2)) ≠
      torsionComodule.coact (Finsupp.single 2 (1 : ZMod 2)) := by
  intro h
  have hm : Finsupp.single 2 (1 : ZMod 2) ∈ torsionSupported :=
    (torsionComodule.coact_inj.mp h) ▸ torsionSupported_contains_coordinates.1
  have hz := (mem_torsionSupported _).mp hm 2 (by simp)
  simp at hz

/-- The coact does not kill the nonzero characteristic-two coordinate vector. -/
theorem torsionVector_coact_ne_zero :
    torsionComodule.coact (Finsupp.single 0 (1 : ZMod 2)) ≠ 0 := by
  intro h
  exact torsionVector_ne_zero (torsionComodule.coact_eq_zero.mp h)

/-- The coact on the countable torsion module is not the zero linear map. -/
theorem torsionComodule_coact_ne_zero : torsionComodule.coact ≠ 0 := by
  intro h
  let := torsionComodule.coact_eq_zero_iff.mp h
  exact torsionVector_ne_zero (Subsingleton.elim _ _)

/-- Doubling the specified nonzero torsion vector gives zero. -/
theorem two_smul_torsionVector :
    (2 : ℕ) • (Finsupp.single 0 (1 : ZMod 2) : TorsionAmbient) = 0 := by
  rw [two_smul]
  exact ZModModule.add_self _

/-- A section of the natural-valued free cover would send every doubled-zero
vector to zero, contradicting recovery of a nonzero coordinate vector. -/
theorem torsionAmbient_not_projective : ¬ Module.Projective ℕ TorsionAmbient := by
  intro h
  obtain ⟨sigma, hsigma⟩ := h.out
  have hzero (m : TorsionAmbient) : sigma m = 0 := by
    ext i
    have hdouble : sigma m + sigma m = 0 := by
      rw [← map_add, ZModModule.add_self, map_zero]
    have hi := congrArg (fun f : TorsionAmbient →₀ ℕ ↦ f i) hdouble
    change sigma m i + sigma m i = 0 at hi
    exact le_antisymm ((Nat.le_add_right _ _).trans_eq hi) (Nat.zero_le _)
  have hrecover := hsigma (Finsupp.single 0 (1 : ZMod 2))
  rw [hzero, map_zero] at hrecover
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1)
    (by simpa using congrArg (fun f : TorsionAmbient ↦ f 0) hrecover)

/-- Freeness would imply projectivity, so the countable torsion module is not free. -/
theorem torsionAmbient_not_free : ¬ Module.Free ℕ TorsionAmbient := by
  intro h
  let : Module.Free ℕ TorsionAmbient := h
  exact torsionAmbient_not_projective inferInstance

/-- The scalar coalgebra in the torsion model is projective by freeness over itself. -/
theorem torsion_coalgebra_projective : Module.Projective ℕ ℕ := inferInstance

/-- The proper idempotent ideal used as the right coacting coalgebra. -/
abbrev ThreeIdeal := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))

/-- The specified generator of the idempotent ideal. -/
def threeGenerator : ThreeIdeal := Ideal.spanSingletonGenerator (3 : ZMod 6)

attribute [local instance] CoalgebraExamples.zmodSixIdealCoalgebra

noncomputable local instance threeIdealProjective : Module.Projective (ZMod 6) ThreeIdeal :=
  CoalgebraExamples.zmod_six_ideal_projective_not_free.1

theorem threeGenerator_counit : Coalgebra.counit (R := ZMod 6) threeGenerator = 3 := rfl

private theorem threeGenerator_ne_zero : threeGenerator ≠ 0 := by
  intro h
  have hcoe := congrArg (fun d : ThreeIdeal ↦ (d : ZMod 6)) h
  exact (by decide : (3 : ZMod 6) ≠ 0) (by simpa [threeGenerator] using hcoe)

noncomputable local instance threeIdealNontrivial : Nontrivial ThreeIdeal :=
  ⟨⟨threeGenerator, 0, threeGenerator_ne_zero⟩⟩

/-- The countable direct sum of the ideal, not its self-coalgebra coact. -/
abbrev IdealAmbient := ℕ →₀ ThreeIdeal

/-- Three acts as the identity on the countable direct sum of the idempotent ideal. -/
theorem three_smul (m : IdealAmbient) : (3 : ZMod 6) • m = m := by
  apply Finsupp.ext
  intro n
  rw [Finsupp.smul_apply]
  exact CoalgebraExamples.zmod_six_three_idempotent.smul_span_singleton (m n)

/-- The ideal generator has diagonal comultiplication for its idempotent-ideal coalgebra. -/
theorem threeGenerator_comul : Coalgebra.comul (R := ZMod 6) threeGenerator =
    threeGenerator ⊗ₜ[ZMod 6] threeGenerator :=
  CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan_comul_generator

/-- The constant-tensor coact of the finite ideal on its infinite direct sum. -/
@[instance_reducible] noncomputable def idealComodule : Comodule (ZMod 6) ThreeIdeal IdealAmbient :=
  Comodule.ofTensor threeGenerator threeGenerator_comul (by
    intro m
    rw [threeGenerator_counit]
    exact three_smul m)

attribute [local instance] idealComodule

@[simp] theorem idealComodule_coact (m : IdealAmbient) :
    idealComodule.coact m = m ⊗ₜ[ZMod 6] threeGenerator := rfl

/-- The subtype coact is given directly by `u ↦ u ⊗ e₃`, with closed constant-tensor laws. -/
@[instance_reducible] noncomputable def idealSupportedComodule : Comodule (ZMod 6) ThreeIdeal
    (Finsupp.supported ThreeIdeal (ZMod 6) ({0, 1} : Set ℕ)) :=
  Comodule.ofTensor threeGenerator threeGenerator_comul (by
    intro m
    rw [threeGenerator_counit]
    apply Subtype.ext
    exact three_smul (m : IdealAmbient))

/-- The supported `{0, 1}` submodule with its specified subtype coact over the finite ideal. -/
noncomputable def idealSupported : Subcomodule (ZMod 6) ThreeIdeal IdealAmbient where
  carrier := Finsupp.supported ThreeIdeal (ZMod 6) ({0, 1} : Set ℕ)
  coact_mem' := by
    intro m hm
    exact ⟨(⟨m, hm⟩ : Finsupp.supported ThreeIdeal (ZMod 6) ({0, 1} : Set ℕ))
      ⊗ₜ[ZMod 6] threeGenerator, rfl⟩

@[simp] theorem mem_idealSupported (m : IdealAmbient) :
    m ∈ idealSupported ↔ ∀ n ∉ ({0, 1} : Set ℕ), m n = 0 :=
  Finsupp.mem_supported' (ZMod 6) m

/-- Both specified generator coordinates lie in the ideal subcomodule. -/
theorem idealSupported_contains_coordinates :
    Finsupp.single 0 threeGenerator ∈ idealSupported ∧
      Finsupp.single 1 threeGenerator ∈ idealSupported := by
  constructor <;> exact Finsupp.single_mem_supported (ZMod 6) _ (by simp)

/-- The ideal-model witness is independently FG, nonzero and proper. -/
theorem idealSupported_fg_nonzero_proper :
    idealSupported.toSubmodule.FG ∧ idealSupported.toSubmodule ≠ ⊥ ∧
      idealSupported.toSubmodule ≠ ⊤ :=
  ⟨twoSupported_fg, twoSupported_nonzero_proper threeGenerator threeGenerator_ne_zero⟩

@[simp] theorem idealSupportedComodule_coact (m : idealSupported.toSubmodule) :
    idealSupportedComodule.coact m = m ⊗ₜ[ZMod 6] threeGenerator := rfl

/-- Inclusion of the directly constructed ideal subtype comodule is colinear. -/
theorem idealSupported_subtype_colinear :
    idealSupported.toSubmodule.subtype.rTensor ThreeIdeal ∘ₗ idealSupportedComodule.coact =
      idealComodule.coact ∘ₗ idealSupported.toSubmodule.subtype :=
  by ext m; rfl

/-- The ideal coacting coalgebra is projective, nonfree and has nonsurjective counit. -/
theorem threeIdeal_projective_nonfree_proper_counit :
    Module.Projective (ZMod 6) ThreeIdeal ∧ ¬ Module.Free (ZMod 6) ThreeIdeal ∧
      LinearMap.range (Coalgebra.counit (R := ZMod 6) (A := ThreeIdeal)) ≠ ⊤ :=
  ⟨inferInstance, CoalgebraExamples.zmod_six_ideal_projective_not_free.2,
    CoalgebraExamples.zmod_six_ideal_counit_range_ne_top⟩

/-- The diagonal generator is not group-like, because its counit is three rather than one. -/
theorem threeGenerator_not_groupLike : ¬ IsGroupLikeElem (R := ZMod 6) threeGenerator := by
  intro h
  have hc := h.counit_eq_one
  rw [threeGenerator_counit] at hc
  exact (by decide : (3 : ZMod 6) ≠ 1) hc

/-- The ideal ambient is infinite, projective, nonfree and not module-finite. -/
theorem idealAmbient_infinite_projective_nonfree_not_finite :
    Infinite IdealAmbient ∧ Module.Projective (ZMod 6) IdealAmbient ∧
      ¬ Module.Free (ZMod 6) IdealAmbient ∧ ¬ Module.Finite (ZMod 6) IdealAmbient :=
  ⟨inferInstance, CoalgebraExamples.countable_zmod_six_ideal_projective_not_free_not_finite⟩

/-- The subcomodule API gives image closure on every member of the specified torsion witness. -/
theorem torsionSupported_all_member_closure (m : TorsionAmbient) (hm : m ∈ torsionSupported) :
    torsionComodule.coact m ∈ LinearMap.range (torsionSupported.toSubmodule.subtype.rTensor ℕ) :=
  by
    obtain ⟨t, ht⟩ := torsionSupported.coact_mem hm
    exact ⟨t, ht⟩

/-- The ideal witness is closed for arbitrary linear combinations, not only its coordinates. -/
theorem idealSupported_linear_combination_closed (r t : ZMod 6) :
    idealComodule.coact
        (r • Finsupp.single 0 threeGenerator + t • Finsupp.single 1 threeGenerator) ∈
      LinearMap.range (idealSupported.toSubmodule.subtype.rTensor ThreeIdeal) := by
  have hm : r • Finsupp.single 0 threeGenerator + t • Finsupp.single 1 threeGenerator
      ∈ idealSupported := idealSupported.toSubmodule.add_mem
    (idealSupported.toSubmodule.smul_mem r (Finsupp.single_mem_supported _ _ (by simp)))
    (idealSupported.toSubmodule.smul_mem t (Finsupp.single_mem_supported _ _ (by simp)))
  obtain ⟨v, hv⟩ := idealSupported.coact_mem hm
  exact ⟨v, hv⟩

/-- Finite containment applies to two nonzero vectors in the nonprojective ambient module. -/
theorem torsion_finite_containment :
    ∃ U : Subcomodule ℕ ℕ TorsionAmbient,
      Finsupp.single 0 (1 : ZMod 2) ∈ U ∧ Finsupp.single 1 (1 : ZMod 2) ∈ U ∧
      U.toSubmodule.FG := by
  obtain ⟨U, hs, hfg⟩ := Comodule.exists_fg_subcomodule_of_finite (X := torsionComodule)
    (s := {Finsupp.single 0 (1 : ZMod 2), Finsupp.single 1 (1 : ZMod 2)})
    ((Set.finite_singleton _).insert _)
  exact ⟨U, hs (by simp), hs (by simp), hfg⟩

/-- A finite common bound contains the supported subcomodule and coordinate two. -/
private theorem torsionSupported_common_fg_bound :
    ∃ W : Subcomodule ℕ ℕ TorsionAmbient, Module.Finite ℕ W.toSubmodule ∧
      torsionSupported.toSubmodule ≤ W.toSubmodule ∧
      Finsupp.single 2 (1 : ZMod 2) ∈ W := by
  obtain ⟨V, hV, hfgV⟩ := Comodule.exists_fg_subcomodule_of_finite (X := torsionComodule)
    (Set.finite_singleton (Finsupp.single 2 (1 : ZMod 2)))
  have hfgU : Module.Finite ℕ torsionSupported.toSubmodule :=
    Module.Finite.iff_fg.mpr torsionSupported_fg_nonzero_proper.1
  obtain ⟨W, hUW, hVW⟩ := (Comodule.directed_fg_toSubmodule (X := torsionComodule))
    ⟨torsionSupported, hfgU⟩ ⟨V, Module.Finite.iff_fg.mpr hfgV⟩
  exact ⟨W.val, W.property, hUW, hVW (hV (by simp))⟩

/-- The union supplies a finite subcomodule containing the sum of coordinates zero and two. -/
private theorem torsion_coordinate_sum_mem_fg :
    ∃ U : Subcomodule ℕ ℕ TorsionAmbient, Module.Finite ℕ U.toSubmodule ∧
      Finsupp.single 0 (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2) ∈ U := by
  obtain ⟨U, hU⟩ := Set.iUnion_eq_univ_iff.mp (Comodule.iUnion_fg_eq_univ (X := torsionComodule))
    (Finsupp.single 0 (1 : ZMod 2) + Finsupp.single 2 (1 : ZMod 2))
  exact ⟨U.val, U.property, hU⟩

/-- Finite containment applies with the proper-counit-image projective coacting ideal. -/
theorem ideal_finite_containment :
    ∃ U : Subcomodule (ZMod 6) ThreeIdeal IdealAmbient, Finsupp.single 0 threeGenerator ∈ U ∧
        U.toSubmodule.FG := by
  obtain ⟨U, hs, hfg⟩ := Comodule.exists_fg_subcomodule_of_finite (X := idealComodule)
    (s := {Finsupp.single 0 threeGenerator}) (Set.finite_singleton _)
  exact ⟨U, hs (by simp), hfg⟩

/-- Empty finite subsets use the zero stable witness without finite containment. -/
theorem empty_subset_bot {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [X : Comodule R C M] :
    (∅ : Set M) ⊆ ((⊥ : Subcomodule R C M) : Set M) ∧
      ((⊥ : Subcomodule R C M)).toSubmodule.FG :=
  ⟨Set.empty_subset _, Submodule.fg_bot⟩

/-- Singleton zero has the same specified zero witness. -/
theorem zero_mem_bot {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M] :
    (0 : M) ∈ (⊥ : Subcomodule R C M) :=
  (Submodule.mem_bot R).mpr rfl

/-- The empty-index ambient module carries a scalar coact with no nonzero element. -/
@[instance_reducible] noncomputable def zeroAmbientComodule : Comodule ℕ ℕ (Empty →₀ ℕ) :=
  Comodule.trivial (R := ℕ) («C» := ℕ) (M := _)

/-- The empty-index coalgebra has its regular zero right comodule. -/
@[instance_reducible] noncomputable def zeroCoalgebraComodule : Comodule ℕ (Empty →₀ ℕ) (Empty
    →₀ ℕ) :=
  Comodule.instSelf ℕ _

/-- The scalar coact on the empty-index ambient module is the zero linear map. -/
theorem zeroAmbientComodule_coact_eq_zero : zeroAmbientComodule.coact = 0 :=
  zeroAmbientComodule.coact_eq_zero_iff.mpr inferInstance

/-- The regular coact on the empty-index coalgebra is the zero linear map. -/
theorem zeroCoalgebraComodule_coact_eq_zero : zeroCoalgebraComodule.coact = 0 :=
  zeroCoalgebraComodule.coact_eq_zero_iff.mpr inferInstance

/-- Trivial scalars are permitted by the right-comodule definition. -/
@[instance_reducible] def trivialScalarComodule : Comodule PUnit PUnit PUnit := Comodule.trivial
    (R := PUnit) (C := PUnit) (M := PUnit)

/-- The finite-subset statement preserves three independent universes and closure on all members. -/
theorem finite_containment_independent_universes {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [Module.Projective R C]
    [X : Comodule R C M] {s : Set M} (hs : s.Finite) :
    ∃ U : Subcomodule R C M, s ⊆ (U : Set M) ∧ U.toSubmodule.FG ∧
      ∀ m ∈ U, X.coact m ∈ LinearMap.range (U.toSubmodule.subtype.rTensor C) := by
  obtain ⟨U, hsU, hfg⟩ := Comodule.exists_fg_subcomodule_of_finite (X := X) hs
  exact ⟨U, hsU, hfg, (fun m hm => by
    obtain ⟨t, ht⟩ := U.coact_mem hm
    exact ⟨t, ht⟩)⟩



section CounitChange

local notation "C" => MonoidAlgebra ℕ ℕ
local notation "X" => Comodule.instSelf ℕ C
local notation "ε" => Coalgebra.counitCoalgHom ℕ C
local notation "e₀" => (MonoidAlgebra.single (0 : ℕ) (1 : ℕ) : C)
local notation "e₁" => (MonoidAlgebra.single (1 : ℕ) (1 : ℕ) : C)

/-- The standard infinite basis obstructs module-finiteness over the natural semiring. -/
theorem natural_coalgebra_not_finite : ¬ Module.Finite ℕ C :=
  Module.not_finite_of_infinite_basis (MonoidAlgebra.basis ℕ ℕ)

/-- The standard counit identifies distinct nonzero basis points, so is not injective. -/
theorem natural_counit_noninjective :
    e₀ ≠ 0 ∧ e₁ ≠ 0 ∧ e₀ ≠ e₁ ∧ ε e₀ = 1 ∧ ε e₁ = 1 ∧
      ¬ Function.Injective ε := by
  have h0 : e₀ ≠ 0 := by
    intro h
    have hc := congrArg (fun a : C ↦ a.coeff 0) h
    simp at hc
  have h1 : e₁ ≠ 0 := by
    intro h
    have hc := congrArg (fun a : C ↦ a.coeff 1) h
    simp at hc
  have hne : e₀ ≠ e₁ := by
    intro h
    have hc := congrArg (fun a : C ↦ a.coeff 0) h
    simp at hc
  have hc0 : ε e₀ = 1 := by simp
  have hc1 : ε e₁ = 1 := by simp
  refine ⟨h0, h1, hne, hc0, hc1, ?_⟩
  intro hinj
  exact hne (hinj (hc0.trans hc1.symm))

/-- The definition changes only the coalgebra factor of each diagonal basis tensor. -/
theorem natural_counit_changed_coact (i : ℕ) :
    (Comodule.Corestrict (M := C) ε).coact (MonoidAlgebra.single i 1) =
      (MonoidAlgebra.single i 1 : C) ⊗ₜ[ℕ] 1 := by
  rw [Comodule.corestrict_counit, Comodule.trivial_coact_apply]

/-- Changing the regular coact along the stock counit gives the stock scalar coact. -/
theorem natural_counit_change_eq_scalar :
    Comodule.Corestrict (M := C) ε = Comodule.trivial (R := ℕ) («C» := ℕ) (M := C) :=
  Comodule.corestrict_counit

/-- The counit is colinear from the changed regular source to the regular scalar target. -/
private theorem natural_counit_colinear :
    let h := (ε).toComoduleHom
    let l := @Comodule.Hom.toLinearMap ℕ ℕ C ℕ _ _ _ _ _ _
      (Comodule.Corestrict (M := C) ε) _ _ (Comodule.instSelf ℕ ℕ) h
    l = (ε).toLinearMap ∧ l e₀ = 1 := by
  exact ⟨CoalgHom.toComoduleHom_toLinearMap ε,
    by simp only [CoalgHom.toComoduleHom_toLinearMap]; simp⟩

/-- The module factor survives: counital cancellation still distinguishes the two points. -/
theorem natural_counit_changed_coact_separates :
    (Comodule.Corestrict (M := C) ε).coact e₀ ≠ (Comodule.Corestrict (M := C) ε).coact e₁ := by
  intro h
  exact natural_counit_noninjective.2.2.1 ((Comodule.Corestrict (M := C) ε).coact_injective h)

end CounitChange


/-- The counit-to-scalar identity also connects the existing zero boundary comodules. -/
theorem zeroCoalgebraComodule_map_counit :
    Comodule.Corestrict (M := Empty →₀ ℕ) (Coalgebra.counitCoalgHom ℕ (Empty →₀ ℕ)) =
      zeroAmbientComodule :=
  Comodule.corestrict_counit

end ComoduleExamples

#print axioms ComoduleExamples.torsionComodule
#print axioms ComoduleExamples.torsionSupported
#print axioms ComoduleExamples.torsionSupportedComodule
#print axioms ComoduleExamples.torsionSupported_fg_nonzero_proper
#print axioms ComoduleExamples.torsionSupported_subtype_colinear
#print axioms ComoduleExamples.torsionAmbient_not_finite
#print axioms ComoduleExamples.torsionAmbient_not_projective
#print axioms ComoduleExamples.torsionAmbient_not_free
#print axioms ComoduleExamples.idealComodule
#print axioms ComoduleExamples.idealSupportedComodule
#print axioms ComoduleExamples.idealSupported
#print axioms ComoduleExamples.idealSupported_fg_nonzero_proper
#print axioms ComoduleExamples.idealSupported_subtype_colinear
#print axioms ComoduleExamples.threeIdeal_projective_nonfree_proper_counit
#print axioms ComoduleExamples.threeGenerator_not_groupLike
#print axioms ComoduleExamples.idealAmbient_infinite_projective_nonfree_not_finite

/-!
## Linear operations on comodule morphisms

The scalar coact on the natural-number plane gives two noncommuting coordinate
maps. The scalar coact on `PUnit` gives a zero-module boundary over the same
nontrivial scalar semiring. Tensor naturality proves colinearity of the coordinate
maps; the comodule laws are those of `Comodule.scalar`.
-/

namespace ComoduleHomExamples

universe z

open TauCeti.Comodule.Hom
open TauCeti.Comodule.Hom

/-- The natural-number plane with its scalar coact. -/
@[instance_reducible] noncomputable def plane : Comodule ℕ ℕ (ℕ × ℕ) := Comodule.trivial (R :=
    ℕ) («C» := ℕ) (M := _)

attribute [local instance] plane

/-- The coordinate map `(x, y) ↦ (y, 0)` on the scalar comodule. -/
noncomputable def A : Comodule.Hom ℕ ℕ (ℕ × ℕ) (ℕ × ℕ) :=
  Comodule.Hom.ofTrivial (C := ℕ)
    ((LinearMap.snd ℕ ℕ ℕ).prod (0 : ℕ × ℕ →ₗ[ℕ] ℕ))

/-- The coordinate map `(x, y) ↦ (0, x)` on the scalar comodule. -/
noncomputable def B : Comodule.Hom ℕ ℕ (ℕ × ℕ) (ℕ × ℕ) :=
  Comodule.Hom.ofTrivial (C := ℕ)
    ((0 : ℕ × ℕ →ₗ[ℕ] ℕ).prod (LinearMap.fst ℕ ℕ ℕ))

@[simp] theorem A_apply (m : ℕ × ℕ) : A m = (m.2, 0) := by rw [A, Comodule.Hom.ofTrivial_apply]; rfl
@[simp] theorem B_apply (m : ℕ × ℕ) : B m = (0, m.1) := by rw [B, Comodule.Hom.ofTrivial_apply]; rfl

/-- A point distinguishing the identity and zero morphisms. -/
def e : ℕ × ℕ := (1, 0)

/-- The scalar comodule has a nonzero identity morphism. -/
theorem id_ne_zero : Comodule.Hom.id ℕ ℕ (ℕ × ℕ) ≠ (0 : Comodule.Hom ℕ ℕ (ℕ × ℕ) (ℕ × ℕ)) := by
  intro h
  have hp := congrArg (fun f : Comodule.Hom ℕ ℕ (ℕ × ℕ) (ℕ × ℕ) ↦ (f e).1) h
  simp only [Comodule.Hom.id_apply, Comodule.Hom.zero_apply, e,
    Prod.fst_zero] at hp
  exact Nat.one_ne_zero hp

/-- Addition on morphisms is pointwise addition. -/
theorem id_add_id_at_e :
    (Comodule.Hom.id ℕ ℕ (ℕ × ℕ) + Comodule.Hom.id ℕ ℕ (ℕ × ℕ)) e = (2, 0) := by
    simp only [Comodule.Hom.add_apply,
      Comodule.Hom.id_apply, e]
    rfl

/-- Natural-number scalar multiplication has its ordinary pointwise meaning. -/
theorem three_smul_id_at_e : ((3 : ℕ) • Comodule.Hom.id ℕ ℕ (ℕ × ℕ)) e = (3, 0) := by
    simp only [
      e]
    rfl

/-- Composition applies the inner morphism first. -/
theorem A_comp_B_at_e : A.comp B e = (1, 0) := by
    simp only [
      Comodule.Hom.comp_apply, A_apply, B_apply, e]

/-- The two coordinate morphisms do not commute at `e`. -/
theorem B_comp_A_at_e : B.comp A e = (0, 0) := by
    simp only [
      Comodule.Hom.comp_apply, A_apply, B_apply, e]

/-- Scalar multiplication in both slots agrees with the existing composition. -/
theorem scaled_comp_at_e : ((2 : ℕ) • A).comp ((3 : ℕ) • B) e = (6, 0) := by
  simp only [Comodule.Hom.comp_apply,
    Comodule.Hom.nsmul_apply, A_apply, B_apply, e]
  rfl

/-- The canonical linear-map class supplies additivity directly on morphisms. -/
theorem B_map_add : B (e + e) = B e + B e := map_add B e e

/-- The canonical linear-map class supplies scalar compatibility directly. -/
theorem B_map_smul : B ((3 : ℕ) • e) = (3 : ℕ) • B e := map_smul B 3 e

/-- The generic class preserves zero without an additional morphism lemma. -/
theorem B_map_zero : B 0 = 0 := map_zero B

set_option linter.deprecated false in
/-- Both original coercions agree with the generic class on the coordinate map. -/
theorem A_coercions :
    (A.toLinearMap : (ℕ × ℕ) → (ℕ × ℕ)) = (A : (ℕ × ℕ) → (ℕ × ℕ)) ∧
      (A : (ℕ × ℕ) →ₗ[ℕ] (ℕ × ℕ)) = A.toLinearMap ∧
      LinearMap.ofClass A = A.toLinearMap :=
  ⟨coe_toLinearMap A, ofClass_eq_toLinearMap A, ofClass_eq_toLinearMap A⟩

/-- The bundled forgetful map reads back the coordinate linear map. -/
theorem forget_A : toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := ℕ × ℕ) A =
    (LinearMap.snd ℕ ℕ ℕ).prod (0 : ℕ × ℕ →ₗ[ℕ] ℕ) := by
  rw [toLinearMapₗ_apply]
  rfl

/-- The linear forgetful map preserves natural-number multiples generically. -/
theorem forget_three_id : toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := ℕ × ℕ) ((3 : ℕ) •
    Comodule.Hom.id ℕ ℕ (ℕ × ℕ)) =
    (3 : ℕ) • toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := ℕ × ℕ) (Comodule.Hom.id ℕ ℕ (ℕ
        × ℕ)) :=
  map_nsmul (toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := ℕ × ℕ)) 3 (Comodule.Hom.id ℕ ℕ
      (ℕ × ℕ))

/-- Forgetting morphism linear combinations works in independent universes and both map routes. -/
theorem forget_linear_combination {R : Type u} {C : Type v} {M : Type w} {N : Type z}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [X : Comodule R C M] [Y : Comodule R C N]
    (r : R) (f g : Comodule.Hom R C M N) :
    toLinearMapₗ (R := R) (C := C) (M := M) (N := N) (r • f + g) = r • LinearMap.ofClass f + (g
        : M →ₗ[R] N) := by
  rw [map_add, map_smul]
  simp only [toLinearMapₗ_apply, ofClass_eq_toLinearMap]

/-- Injectivity of the bundled forgetful map detects the nonzero identity. -/
theorem forget_id_ne_zero : toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := ℕ × ℕ)
    (Comodule.Hom.id ℕ ℕ (ℕ × ℕ)) ≠ 0 := by
  intro h
  apply id_ne_zero
  apply toLinearMapₗ_injective
  simpa using h

/-- The one-element module with the scalar coact. -/
@[instance_reducible] noncomputable def point : Comodule ℕ ℕ PUnit := Comodule.trivial (R := ℕ)
    («C» := ℕ) (M := _)

attribute [local instance] point

/-- The zero morphism from the plane to the one-element module. -/
noncomputable def toPoint : Comodule.Hom ℕ ℕ (ℕ × ℕ) PUnit := 0

/-- The zero morphism from the one-element module to the plane. -/
noncomputable def fromPoint : Comodule.Hom ℕ ℕ PUnit (ℕ × ℕ) := 0

/-- Every plane-to-point morphism is pointwise the unique map. -/
theorem toPoint_unique (f : Comodule.Hom ℕ ℕ (ℕ × ℕ) PUnit) : f = toPoint := by
  apply TauCeti.Comodule.Hom.ext
  intro m
  exact Subsingleton.elim _ _

/-- A morphism out of the one-element module vanishes by linearity at zero. -/
theorem fromPoint_unique (f : Comodule.Hom ℕ ℕ PUnit (ℕ × ℕ)) : f = fromPoint := by
  apply TauCeti.Comodule.Hom.ext
  intro m
  calc
    f m = f 0 := congrArg f (Subsingleton.elim m 0)
    _ = 0 := map_zero f
    _ = fromPoint m := rfl

/-- Zero, sum, scalar and forgetful readbacks agree in both zero-module directions. -/
theorem point_readbacks :
    (0 : Comodule.Hom ℕ ℕ (ℕ × ℕ) PUnit) = toPoint ∧
      toPoint + toPoint = toPoint ∧ (3 : ℕ) • toPoint = toPoint ∧
      toLinearMapₗ (R := ℕ) («C» := ℕ) (M := ℕ × ℕ) (N := PUnit) toPoint = 0 ∧
      (0 : Comodule.Hom ℕ ℕ PUnit (ℕ × ℕ)) = fromPoint ∧
      fromPoint + fromPoint = fromPoint ∧ (3 : ℕ) • fromPoint = fromPoint ∧
      toLinearMapₗ (R := ℕ) («C» := ℕ) (M := PUnit) (N := ℕ × ℕ) fromPoint = 0 := by
  simp [toPoint, fromPoint]

end ComoduleHomExamples

/-!
## Inverse colinearity for two colored coacts

The two coacts on `ℕ × ℕ` below use the same stock module structures and the
stock full coalgebra `MonoidAlgebra ℕ Bool`. Their basis colors are fixed; only
the module coordinates are exchanged. Both coact laws are proved directly,
without transport. Mathlib supplies the coalgebra, product maps and tensor maps.
-/

namespace ComoduleExamples

noncomputable section

private abbrev ColoredCoalgebra := MonoidAlgebra ℕ Bool

-- These stock monoid-algebra elements have coefficients `Finsupp.single false 1`
-- and `Finsupp.single true 1`, respectively.
private def color0 : ColoredCoalgebra := MonoidAlgebra.single false 1
private def color1 : ColoredCoalgebra := MonoidAlgebra.single true 1

private theorem color0_groupLike : IsGroupLikeElem ℕ color0 := by
  constructor <;>
    simp [color0, MonoidAlgebra.comul_single, CommSemiring.comul_apply]

private theorem color1_groupLike : IsGroupLikeElem ℕ color1 := by
  constructor <;>
    simp [color1, MonoidAlgebra.comul_single, CommSemiring.comul_apply]

private def coloredRhoX : (ℕ × ℕ) →ₗ[ℕ] (ℕ × ℕ) ⊗[ℕ] ColoredCoalgebra :=
  (((TensorProduct.mk ℕ (ℕ × ℕ) ColoredCoalgebra).flip color0) ∘ₗ
      LinearMap.inl ℕ ℕ ℕ).coprod
    (((TensorProduct.mk ℕ (ℕ × ℕ) ColoredCoalgebra).flip color1) ∘ₗ
      LinearMap.inr ℕ ℕ ℕ)

private def coloredRhoY : (ℕ × ℕ) →ₗ[ℕ] (ℕ × ℕ) ⊗[ℕ] ColoredCoalgebra :=
  (((TensorProduct.mk ℕ (ℕ × ℕ) ColoredCoalgebra).flip color1) ∘ₗ
      LinearMap.inl ℕ ℕ ℕ).coprod
    (((TensorProduct.mk ℕ (ℕ × ℕ) ColoredCoalgebra).flip color0) ∘ₗ
      LinearMap.inr ℕ ℕ ℕ)

private theorem coloredRhoX_apply (a b : ℕ) :
    coloredRhoX (a, b) = (a, 0) ⊗ₜ[ℕ] color0 + (0, b) ⊗ₜ[ℕ] color1 := rfl

private theorem coloredRhoY_apply (a b : ℕ) :
    coloredRhoY (a, b) = (a, 0) ⊗ₜ[ℕ] color1 + (0, b) ⊗ₜ[ℕ] color0 := rfl

@[instance_reducible] private def coloredX : Comodule ℕ ColoredCoalgebra (ℕ × ℕ) where
  coact := coloredRhoX
  coassoc := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change TensorProduct.assoc ℕ (ℕ × ℕ) ColoredCoalgebra ColoredCoalgebra
        (coloredRhoX.rTensor ColoredCoalgebra (coloredRhoX (a, b))) =
      (Coalgebra.comul (R := ℕ) (A := ColoredCoalgebra)).lTensor (ℕ × ℕ)
        (coloredRhoX (a, b))
    rw [coloredRhoX_apply]
    simp only [coloredRhoX_apply, map_add, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul,
      color0_groupLike.comul_eq_tmul_self, color1_groupLike.comul_eq_tmul_self,
      Prod.mk_zero_zero, TensorProduct.zero_tmul, add_zero, zero_add]
    refine (LinearEquiv.map_add
      (TensorProduct.assoc ℕ (ℕ × ℕ) ColoredCoalgebra ColoredCoalgebra)
      (((a, 0) ⊗ₜ[ℕ] color0) ⊗ₜ[ℕ] color0)
      (((0, b) ⊗ₜ[ℕ] color1) ⊗ₜ[ℕ] color1)).trans ?_
    exact congrArg₂ (· + ·)
      (TensorProduct.assoc_tmul (R := ℕ) (M := ℕ × ℕ)
        (N := ColoredCoalgebra) (P := ColoredCoalgebra) (a, 0) color0 color0)
      (TensorProduct.assoc_tmul (R := ℕ) (M := ℕ × ℕ)
        (N := ColoredCoalgebra) (P := ColoredCoalgebra) (0, b) color1 color1)
  lTensor_counit_comp_coact := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (Coalgebra.counit (R := ℕ) (A := ColoredCoalgebra)).lTensor (ℕ × ℕ)
        (coloredRhoX (a, b)) = (a, b) ⊗ₜ[ℕ] 1
    rw [coloredRhoX_apply]
    simp only [map_add, LinearMap.lTensor_tmul,
      color0_groupLike.counit_eq_one, color1_groupLike.counit_eq_one]
    rw [← TensorProduct.add_tmul]
    simp

@[instance_reducible] private def coloredY : Comodule ℕ ColoredCoalgebra (ℕ × ℕ) where
  coact := coloredRhoY
  coassoc := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change TensorProduct.assoc ℕ (ℕ × ℕ) ColoredCoalgebra ColoredCoalgebra
        (coloredRhoY.rTensor ColoredCoalgebra (coloredRhoY (a, b))) =
      (Coalgebra.comul (R := ℕ) (A := ColoredCoalgebra)).lTensor (ℕ × ℕ)
        (coloredRhoY (a, b))
    rw [coloredRhoY_apply]
    simp only [coloredRhoY_apply, map_add, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul,
      color0_groupLike.comul_eq_tmul_self, color1_groupLike.comul_eq_tmul_self,
      Prod.mk_zero_zero, TensorProduct.zero_tmul, add_zero, zero_add]
    refine (LinearEquiv.map_add
      (TensorProduct.assoc ℕ (ℕ × ℕ) ColoredCoalgebra ColoredCoalgebra)
      (((a, 0) ⊗ₜ[ℕ] color1) ⊗ₜ[ℕ] color1)
      (((0, b) ⊗ₜ[ℕ] color0) ⊗ₜ[ℕ] color0)).trans ?_
    exact congrArg₂ (· + ·)
      (TensorProduct.assoc_tmul (R := ℕ) (M := ℕ × ℕ)
        (N := ColoredCoalgebra) (P := ColoredCoalgebra) (a, 0) color1 color1)
      (TensorProduct.assoc_tmul (R := ℕ) (M := ℕ × ℕ)
        (N := ColoredCoalgebra) (P := ColoredCoalgebra) (0, b) color0 color0)
  lTensor_counit_comp_coact := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (Coalgebra.counit (R := ℕ) (A := ColoredCoalgebra)).lTensor (ℕ × ℕ)
        (coloredRhoY (a, b)) = (a, b) ⊗ₜ[ℕ] 1
    rw [coloredRhoY_apply]
    simp only [map_add, LinearMap.lTensor_tmul,
      color0_groupLike.counit_eq_one, color1_groupLike.counit_eq_one]
    rw [← TensorProduct.add_tmul]
    simp

-- Forward colinearity is checked on the specified maps, not inferred from the
-- inverse theorem or a transported coact.
attribute [local instance] coloredX

private def coloredSwapHom : (@Comodule.Hom ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _
    coloredX _ _ coloredY) :=
  @Comodule.Hom.mk ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _ coloredX _ _ coloredY
      (LinearEquiv.prodComm ℕ ℕ ℕ).toLinearMap (by
    symm
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change coloredRhoY (b, a) =
      (LinearEquiv.prodComm ℕ ℕ ℕ).toLinearMap.rTensor ColoredCoalgebra
        (coloredRhoX (a, b))
    rw [coloredRhoY_apply, coloredRhoX_apply]
    simp [LinearMap.rTensor_tmul, add_comm])

-- Nonzero outputs witness both nonzero coacts. Coefficients after the
-- stock projection and tensor unitor detect the changed coact and the
-- failure of the same swap to be colinear from `coloredX` to itself.
example :
    coloredX.coact (1, 0) ≠ 0 ∧ coloredY.coact (1, 0) ≠ 0 ∧
      coloredX.coact ≠ coloredY.coact ∧
      (LinearEquiv.prodComm ℕ ℕ ℕ) (1, 0) ≠ (1, 0) ∧
      ¬ (coloredX.coact ∘ₗ (LinearEquiv.prodComm ℕ ℕ ℕ).toLinearMap =
        (LinearEquiv.prodComm ℕ ℕ ℕ).toLinearMap.rTensor ColoredCoalgebra ∘ₗ
          coloredX.coact) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hz := coloredX.coact_eq_zero.mp h
    simpa using congrArg (fun p : ℕ × ℕ ↦ p.1) hz
  · intro h
    have hz := coloredY.coact_eq_zero.mp h
    simpa using congrArg (fun p : ℕ × ℕ ↦ p.1) hz
  · intro h
    have hxy := LinearMap.congr_fun h (1, 0)
    change coloredRhoX (1, 0) = coloredRhoY (1, 0) at hxy
    rw [coloredRhoX_apply, coloredRhoY_apply] at hxy
    have hc := congrArg
      (fun t : (ℕ × ℕ) ⊗[ℕ] ColoredCoalgebra ↦
        (TensorProduct.lid ℕ ColoredCoalgebra
          ((LinearMap.fst ℕ ℕ ℕ).rTensor ColoredCoalgebra t)).coeff false)
      hxy
    simp [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, color0, color1] at hc
  · simp
  · intro h
    have hswap := LinearMap.congr_fun h (1, 0)
    change coloredRhoX (0, 1) =
      (LinearEquiv.prodComm ℕ ℕ ℕ).toLinearMap.rTensor ColoredCoalgebra
        (coloredRhoX (1, 0)) at hswap
    simp only [coloredRhoX_apply] at hswap
    have hc := congrArg
      (fun t : (ℕ × ℕ) ⊗[ℕ] ColoredCoalgebra ↦
        (TensorProduct.lid ℕ ColoredCoalgebra
          ((LinearMap.snd ℕ ℕ ℕ).rTensor ColoredCoalgebra t)).coeff false)
      hswap
    simp [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, color0, color1] at hc

-- The headline law supplies the inverse colinearity field with exactly the
-- supplied equivalence's inverse linear map, and with the coalgebra fixed.
example : ∃ f : (@Comodule.Hom ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _ coloredY _ _
    coloredX),
    (@Comodule.Hom.toLinearMap ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _ coloredY _ _
        coloredX f) =
      (LinearEquiv.prodComm ℕ ℕ ℕ).symm.toLinearMap := by
  refine ⟨@Comodule.Hom.mk ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _ coloredY _ _ coloredX
    (LinearEquiv.prodComm ℕ ℕ ℕ).symm.toLinearMap (by
      symm
      simpa only [LinearMap.rTensor_def] using
        (TauCeti.Comodule.Hom.colinear_symm
          (LinearEquiv.prodComm ℕ ℕ ℕ)
          (by simpa only [coloredSwapHom, LinearMap.rTensor_def] using (@Comodule.Hom.map_coact
              ℕ ColoredCoalgebra (ℕ × ℕ) (ℕ × ℕ) _ _ _ _ _ _ coloredX _ _ coloredY
              coloredSwapHom).symm))), rfl⟩

-- A cheap identity boundary uses the same already constructed coact.
example :
    coloredX.coact ∘ₗ (LinearEquiv.refl ℕ (ℕ × ℕ)).symm.toLinearMap =
      (LinearEquiv.refl ℕ (ℕ × ℕ)).symm.toLinearMap.rTensor ColoredCoalgebra ∘ₗ
        coloredX.coact := by
  apply TauCeti.Comodule.Hom.colinear_symm
  simp [LinearMap.rTensor_id]

end

end ComoduleExamples
