/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroupsTest.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Right comodules with proper finite support

The scalar coalgebra `ℕ` coacts on `ℕ →₀ ZMod 2` by `m ↦ m ⊗ 1`.
The ambient module is infinite, not module-finite, not projective and not free.
Its submodule supported on `{0, 1}` is specified, proper, nonzero and finitely
generated. Its subtype coaction is the inverse right unitor directly.

The projective ideal `(3)` in `ZMod 6` coacts on its countable direct sum by
`m ↦ m ⊗ e₃`. Here the counit of `e₃` is three, not one: counitality follows
from `3 • m = m`, not from a group-like element or a surjective counit.
Again the submodule supported on `{0, 1}` is proper, nonzero and finitely generated,
with a directly constructed subtype coaction. The projectivity, nonfreeness and
proper counit image reuse the existing idempotent-ideal and split-tensor examples.
Neither direct subtype coaction uses the general induced-subtype construction.

The boundary clients include empty and zero finite subsets, zero ambient modules,
trivial scalars, and independent universes. In the scalar and ideal examples,
the subtype coactions are specified directly; finite generation and properness
follow from the supported submodules. Separate clients apply the finite-containment
theorem to finite subsets of these comodules.

## References

Mathlib supplies Finsupp, supported submodules and scalar coalgebras. The
idempotent-ideal coalgebra and split-tensor examples supply the ideal model.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

open Coalgebra (RightComodule)

namespace RightComoduleExamples

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

/-- The scalar right coaction on the countable torsion module. -/
noncomputable def torsionComodule : RightComodule ℕ ℕ TorsionAmbient :=
  RightComodule.scalar ℕ TorsionAmbient

@[simp] theorem torsionComodule_coaction (m : TorsionAmbient) :
    torsionComodule.coaction m = m ⊗ₜ[ℕ] 1 := rfl

/-- The specified scalar subcomodule with support contained in `{0, 1}`. -/
noncomputable def torsionSupported : torsionComodule.Subcomodule :=
  RightComodule.scalarSubcomodule (Finsupp.supported (ZMod 2) ℕ ({0, 1} : Set ℕ))

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

/-- The scalar subtype coaction is constructed directly by the right unitor. -/
noncomputable def torsionSupportedComodule : RightComodule ℕ ℕ torsionSupported.toSubmodule :=
  torsionSupported.comodule

@[simp] theorem torsionSupportedComodule_coaction (m : torsionSupported.toSubmodule) :
    torsionSupportedComodule.coaction m = m ⊗ₜ[ℕ] 1 := rfl

/-- Inclusion of the directly constructed scalar subtype comodule is colinear. -/
theorem torsionSupported_subtype_colinear :
    torsionSupported.toSubmodule.subtype.rTensor ℕ ∘ₗ torsionSupportedComodule.coaction =
      torsionComodule.coaction ∘ₗ torsionSupported.toSubmodule.subtype :=
  RightComodule.scalar_subtype_colinear _

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

noncomputable local instance threeIdealCoalgebra : Coalgebra (ZMod 6) ThreeIdeal :=
  CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan

noncomputable local instance threeIdealProjective : Module.Projective (ZMod 6) ThreeIdeal :=
  CoalgebraExamples.zmod_six_ideal_projective_not_free.1

@[simp] theorem threeGenerator_counit : Coalgebra.counit (R := ZMod 6) threeGenerator = 3 := rfl

private theorem threeGenerator_ne_zero : threeGenerator ≠ 0 := by
  intro h
  have hcoe := congrArg (fun d : ThreeIdeal ↦ (d : ZMod 6)) h
  exact (by decide : (3 : ZMod 6) ≠ 0) (by simpa [threeGenerator] using hcoe)

noncomputable local instance threeIdealNontrivial : Nontrivial ThreeIdeal :=
  ⟨⟨threeGenerator, 0, threeGenerator_ne_zero⟩⟩

/-- The countable direct sum of the ideal, not its self-coalgebra coaction. -/
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

/-- The constant-tensor coaction of the finite ideal on its infinite direct sum. -/
noncomputable def idealComodule : RightComodule (ZMod 6) ThreeIdeal IdealAmbient :=
  RightComodule.ofTensor threeGenerator threeGenerator_comul (by
    intro m
    rw [threeGenerator_counit]
    exact three_smul m)

@[simp] theorem idealComodule_coaction (m : IdealAmbient) :
    idealComodule.coaction m = m ⊗ₜ[ZMod 6] threeGenerator := rfl

/-- The subtype coaction is given directly by `u ↦ u ⊗ e₃`, with closed constant-tensor laws. -/
noncomputable def idealSupportedComodule : RightComodule (ZMod 6) ThreeIdeal
    (Finsupp.supported ThreeIdeal (ZMod 6) ({0, 1} : Set ℕ)) :=
  RightComodule.ofTensor threeGenerator threeGenerator_comul (by
    intro m
    rw [threeGenerator_counit]
    apply Subtype.ext
    exact three_smul (m : IdealAmbient))

/-- The supported `{0, 1}` submodule with its specified subtype coaction over the finite ideal. -/
noncomputable def idealSupported : idealComodule.Subcomodule where
  toSubmodule := Finsupp.supported ThreeIdeal (ZMod 6) ({0, 1} : Set ℕ)
  comodule := idealSupportedComodule
  subtype_colinear := by
    ext m
    simp [idealSupportedComodule]

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

@[simp] theorem idealSupportedComodule_coaction (m : idealSupported.toSubmodule) :
    idealSupportedComodule.coaction m = m ⊗ₜ[ZMod 6] threeGenerator := rfl

/-- Inclusion of the directly constructed ideal subtype comodule is colinear. -/
theorem idealSupported_subtype_colinear :
    idealSupported.toSubmodule.subtype.rTensor ThreeIdeal ∘ₗ idealSupportedComodule.coaction =
      idealComodule.coaction ∘ₗ idealSupported.toSubmodule.subtype :=
  idealSupported.subtype_colinear

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
    torsionComodule.coaction m ∈ LinearMap.range (torsionSupported.toSubmodule.subtype.rTensor ℕ) :=
  torsionSupported.coaction_mem m hm

/-- The ideal witness is closed for arbitrary linear combinations, not only its coordinates. -/
theorem idealSupported_linear_combination_closed (r t : ZMod 6) :
    idealComodule.coaction
        (r • Finsupp.single 0 threeGenerator + t • Finsupp.single 1 threeGenerator) ∈
      LinearMap.range (idealSupported.toSubmodule.subtype.rTensor ThreeIdeal) := by
  apply idealSupported.coaction_mem
  exact idealSupported.toSubmodule.add_mem
    (idealSupported.toSubmodule.smul_mem r (Finsupp.single_mem_supported _ _ (by simp)))
    (idealSupported.toSubmodule.smul_mem t (Finsupp.single_mem_supported _ _ (by simp)))

/-- Finite containment applies to two nonzero vectors in the nonprojective ambient module. -/
theorem torsion_finite_containment :
    ∃ U : torsionComodule.Subcomodule,
      Finsupp.single 0 (1 : ZMod 2) ∈ U ∧ Finsupp.single 1 (1 : ZMod 2) ∈ U ∧
      U.toSubmodule.FG := by
  obtain ⟨U, hs, hfg⟩ := torsionComodule.exists_fg_subcomodule_of_finite
    (s := {Finsupp.single 0 (1 : ZMod 2), Finsupp.single 1 (1 : ZMod 2)})
    ((Set.finite_singleton _).insert _)
  exact ⟨U, hs (by simp), hs (by simp), hfg⟩

/-- Finite containment applies with the proper-counit-image projective coacting ideal. -/
theorem ideal_finite_containment :
    ∃ U : idealComodule.Subcomodule, Finsupp.single 0 threeGenerator ∈ U ∧ U.toSubmodule.FG := by
  obtain ⟨U, hs, hfg⟩ := idealComodule.exists_fg_subcomodule_of_finite
    (s := {Finsupp.single 0 threeGenerator}) (Set.finite_singleton _)
  exact ⟨U, hs (by simp), hfg⟩

/-- Empty finite subsets use the zero stable witness without finite containment. -/
theorem empty_subset_bot {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] (X : RightComodule R C M) :
    (∅ : Set M) ⊆ (RightComodule.Subcomodule.bot X : Set M) ∧
      (RightComodule.Subcomodule.bot X).toSubmodule.FG :=
  ⟨Set.empty_subset _, Submodule.fg_bot⟩

/-- Singleton zero has the same specified zero witness. -/
theorem zero_mem_bot {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] (X : RightComodule R C M) :
    (0 : M) ∈ RightComodule.Subcomodule.bot X :=
  (Submodule.mem_bot R).mpr rfl

/-- The empty-index ambient module carries a scalar coaction with no nonzero element. -/
noncomputable def zeroAmbientComodule : RightComodule ℕ ℕ (Empty →₀ ℕ) :=
  RightComodule.scalar ℕ _

/-- The empty-index coalgebra has its regular zero right comodule. -/
noncomputable def zeroCoalgebraComodule : RightComodule ℕ (Empty →₀ ℕ) (Empty →₀ ℕ) :=
  RightComodule.regular ℕ _

/-- Trivial scalars are permitted by the right-comodule definition. -/
def trivialScalarComodule : RightComodule PUnit PUnit PUnit := RightComodule.scalar PUnit PUnit

/-- The finite-subset statement preserves three independent universes and closure on all members. -/
theorem finite_containment_independent_universes {R : Type u} {C : Type v} {M : Type w}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [Module.Projective R C]
    (X : RightComodule R C M) {s : Set M} (hs : s.Finite) :
    ∃ U : X.Subcomodule, s ⊆ (U : Set M) ∧ U.toSubmodule.FG ∧
      ∀ m ∈ U, X.coaction m ∈ LinearMap.range (U.toSubmodule.subtype.rTensor C) := by
  obtain ⟨U, hsU, hfg⟩ := X.exists_fg_subcomodule_of_finite hs
  exact ⟨U, hsU, hfg, U.coaction_mem⟩

end RightComoduleExamples

#print axioms RightComoduleExamples.torsionComodule
#print axioms RightComoduleExamples.torsionSupported
#print axioms RightComoduleExamples.torsionSupportedComodule
#print axioms RightComoduleExamples.torsionSupported_fg_nonzero_proper
#print axioms RightComoduleExamples.torsionSupported_subtype_colinear
#print axioms RightComoduleExamples.torsionAmbient_not_finite
#print axioms RightComoduleExamples.torsionAmbient_not_projective
#print axioms RightComoduleExamples.torsionAmbient_not_free
#print axioms RightComoduleExamples.idealComodule
#print axioms RightComoduleExamples.idealSupportedComodule
#print axioms RightComoduleExamples.idealSupported
#print axioms RightComoduleExamples.idealSupported_fg_nonzero_proper
#print axioms RightComoduleExamples.idealSupported_subtype_colinear
#print axioms RightComoduleExamples.threeIdeal_projective_nonfree_proper_counit
#print axioms RightComoduleExamples.threeGenerator_not_groupLike
#print axioms RightComoduleExamples.idealAmbient_infinite_projective_nonfree_not_finite
