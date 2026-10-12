/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal
public import AlgebraicGroupsTest.Algebra.TensorProduct.Split
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite right coideals and subcoalgebras in infinite ambient modules

The additive monoid algebra `ℚ[ℤ]` has a group-like basis. Each basis line is a
nonzero finite-dimensional subspace closed under comultiplication. Away from the
identity index, it does not contain the algebra unit. The integer-indexed basis
also proves that the ambient module is not finite-dimensional.

The free coalgebra `ℕ[ℤ]` is likewise infinite, but its scalars are not a field
and its underlying additive monoid is not a group. Finite right-coideal
containment applies to it, including arbitrary natural linear combinations of
two contained basis elements, using closure on every member of the witness.

The ideal `(3)` in `ZMod 6` and its countable Finsupp coalgebra are projective
but not free. The finite ideal has proper counit image, and the countable module
is not finitely generated. Their genuine split data instantiate projective
right-coideal containment without assuming projectivity as a model hypothesis.
The nonfree and nonfinite proofs reuse the split-tensor examples.

These examples use Mathlib's coalgebra constructions and basis. They also cover
the empty subset, singleton zero, zero ambient coalgebras of finitely supported
functions on the empty type, and a trivial scalar semiring.
-/

@[expose] public section

open scoped TensorProduct

open AddMonoidAlgebra (single)

namespace CoalgebraExamples

-- The comultiplication is diagonal on the group-like basis.
private theorem comul_single_one (g : ℤ) :
    Coalgebra.comul (R := ℚ) (single g (1 : ℚ)) =
      single g (1 : ℚ) ⊗ₜ[ℚ] single g (1 : ℚ) := by
  simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]

/-- The line of a group-like basis element in `ℚ[ℤ]` is closed under comultiplication. -/
theorem basisLine_comul_closed (g : ℤ) :
    ∀ x ∈ Submodule.span ℚ {single g (1 : ℚ)},
      Coalgebra.comul (R := ℚ) x ∈
        LinearMap.range (TensorProduct.mapIncl
          (Submodule.span ℚ {single g (1 : ℚ)})
          (Submodule.span ℚ {single g (1 : ℚ)})) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  let e : Submodule.span ℚ {single g (1 : ℚ)} :=
    ⟨single g 1, Submodule.mem_span_singleton_self _⟩
  refine ⟨a • (e ⊗ₜ[ℚ] e), ?_⟩
  simp only [map_smul, TensorProduct.mapIncl, TensorProduct.map_tmul,
    Submodule.subtype_apply, e, AddMonoidAlgebra.comul_single,
    CommSemiring.comul_apply, AddMonoidAlgebra.lsingle_apply]

-- A specified, nonzero, finitely generated closed subspace, without using containment.
private theorem basisLine_nonzero_fg_closed (g : ℤ) :
    Submodule.span ℚ {single g (1 : ℚ)} ≠ ⊥ ∧
      (Submodule.span ℚ {single g (1 : ℚ)}).FG ∧
      ∀ x ∈ Submodule.span ℚ {single g (1 : ℚ)},
        Coalgebra.comul (R := ℚ) x ∈
          LinearMap.range (TensorProduct.mapIncl
            (Submodule.span ℚ {single g (1 : ℚ)})
            (Submodule.span ℚ {single g (1 : ℚ)})) := by
  refine ⟨?_, Submodule.fg_span_singleton _, basisLine_comul_closed g⟩
  intro h
  have he := Submodule.mem_span_singleton_self (R := ℚ) (single g (1 : ℚ))
  rw [h, Submodule.mem_bot] at he
  have := congrArg (fun f : AddMonoidAlgebra ℚ ℤ ↦ f.coeff g) he
  simp at this

-- The line consists exactly of scalar multiples of its specified basis element.
private theorem mem_basisLine_iff (g : ℤ) (x : AddMonoidAlgebra ℚ ℤ) :
    x ∈ Submodule.span ℚ {single g (1 : ℚ)} ↔
      ∃ a : ℚ, a • single g (1 : ℚ) = x :=
  Submodule.mem_span_singleton

-- Thus a nonidentity basis line cannot be a unital subalgebra.
private theorem one_not_mem_basisLine (g : ℤ) (hg : g ≠ 0) :
    (1 : AddMonoidAlgebra ℚ ℤ) ∉ Submodule.span ℚ {single g (1 : ℚ)} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hcoeff := congrArg (AddMonoidAlgebra.coeffLinearEquiv ℚ) ha
  have hzero := congrArg (fun f : ℤ →₀ ℚ ↦ f 0) hcoeff
  change (a • Finsupp.single g (1 : ℚ)) 0 = Finsupp.single 0 (1 : ℚ) 0 at hzero
  simp only [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hg),
    Finsupp.single_eq_same, smul_zero, zero_ne_one] at hzero

-- An actual infinite basis rules out choosing top as a finite witness.
private theorem not_finite_integer_group_like_coalgebra :
    ¬ Module.Finite ℚ (AddMonoidAlgebra ℚ ℤ) :=
  Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℤ ℚ)

-- Apply finite-set containment to two distinct group-like elements and obtain
-- module finiteness on the resulting subtype through the existing FG bridge.
private theorem exists_finite_closed_submodule_three_seven :
    ∃ D : Submodule ℚ (AddMonoidAlgebra ℚ ℤ),
    single (3 : ℤ) (1 : ℚ) ∈ D ∧ single (7 : ℤ) (1 : ℚ) ∈ D ∧
      Module.Finite ℚ D ∧
      ∀ x ∈ D, Coalgebra.comul (R := ℚ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  obtain ⟨D, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_closed_of_finite
      (K := ℚ) (C := AddMonoidAlgebra ℚ ℤ)
      (s := {single (3 : ℤ) (1 : ℚ), single (7 : ℤ) (1 : ℚ)})
      ((Set.finite_singleton _).insert _)
  exact ⟨D, hs (by simp), hs (by simp), Module.Finite.iff_fg.mpr hfg, hclosed⟩

-- The empty subset has the zero witness in any coalgebra, without containment.
private theorem empty_subset_bot_fg_closed {K C : Type*} [Field K] [AddCommGroup C]
    [Module K C] [Coalgebra K C] :
    (∅ : Set C) ⊆ (⊥ : Submodule K C) ∧ (⊥ : Submodule K C).FG ∧
      ∀ x ∈ (⊥ : Submodule K C), Coalgebra.comul (R := K) x ∈
        LinearMap.range (TensorProduct.mapIncl (⊥ : Submodule K C) ⊥) := by
  refine ⟨Set.empty_subset _, Submodule.fg_bot, ?_⟩
  intro x hx
  have hx0 : x = 0 := (Submodule.mem_bot K).mp hx
  simp [hx0]

-- The existing Finsupp construction on Empty is a zero coalgebra over ℚ.
private theorem exists_fg_closed_submodule_empty_finsupp : ∃ D : Submodule ℚ (Empty →₀ ℚ),
    (Set.univ : Set (Empty →₀ ℚ)) ⊆ (D : Set (Empty →₀ ℚ)) ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := ℚ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  refine ⟨⊥, ?_, Submodule.fg_bot, ?_⟩
  · intro x _
    exact (Submodule.mem_bot ℚ).mpr (Subsingleton.elim x 0)
  · intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot ℚ).mp hx
    simp [hx0]

-- The one-factor theorem applies to a finite set in the infinite-dimensional
-- example without relying on tensor-square containment.
private theorem exists_finite_right_closed_submodule_three_seven :
    ∃ U : Submodule ℚ (AddMonoidAlgebra ℚ ℤ),
    single (3 : ℤ) (1 : ℚ) ∈ U ∧ single (7 : ℤ) (1 : ℚ) ∈ U ∧
      Module.Finite ℚ U ∧
      ∀ x ∈ U, Coalgebra.comul (R := ℚ) x ∈
        LinearMap.range (U.subtype.rTensor (AddMonoidAlgebra ℚ ℤ)) := by
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite
      (K := ℚ) (C := AddMonoidAlgebra ℚ ℤ)
      (s := {single (3 : ℤ) (1 : ℚ), single (7 : ℤ) (1 : ℚ)})
      ((Set.finite_singleton _).insert _)
  exact ⟨U, hs (by simp), hs (by simp), Module.Finite.iff_fg.mpr hfg, hclosed⟩

-- The integer-indexed natural basis rules out an FG ambient top witness.
private theorem not_finite_natural_integer_coalgebra :
    ¬ Module.Finite ℕ (AddMonoidAlgebra ℕ ℤ) :=
  Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℤ ℕ)

-- This ambient additive monoid has an element with no additive inverse.
private theorem single_three_has_no_additive_inverse :
    ¬ ∃ z : AddMonoidAlgebra ℕ ℤ, single (3 : ℤ) (1 : ℕ) + z = 0 := by
  rintro ⟨z, hz⟩
  have hcoeff := congrArg (fun f : AddMonoidAlgebra ℕ ℤ ↦ f.coeff 3) hz
  simp at hcoeff

-- Use the general containment theorem, not a diagonal span construction.
-- The arbitrary sums are handled by its closure on the whole witness U.
private theorem exists_fg_natural_right_coideal_three_seven :
    ∃ U : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      single (3 : ℤ) (1 : ℕ) ∈ U ∧ single (7 : ℤ) (1 : ℕ) ∈ U ∧ U.FG ∧
      (∀ x ∈ U, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (U.subtype.rTensor (AddMonoidAlgebra ℕ ℤ))) ∧
      ∀ a b : ℕ, Coalgebra.comul (R := ℕ)
        (a • single (3 : ℤ) (1 : ℕ) + b • single (7 : ℤ) (1 : ℕ)) ∈
          LinearMap.range (U.subtype.rTensor (AddMonoidAlgebra ℕ ℤ)) := by
  let : Module.Free ℕ (AddMonoidAlgebra ℕ ℤ) :=
    Module.Free.of_basis (AddMonoidAlgebra.basis ℤ ℕ)
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite
      (K := ℕ) (C := AddMonoidAlgebra ℕ ℤ)
      (s := {single (3 : ℤ) (1 : ℕ), single (7 : ℤ) (1 : ℕ)})
      ((Set.finite_singleton _).insert _)
  have hthree : single (3 : ℤ) (1 : ℕ) ∈ U := hs (by simp)
  have hseven : single (7 : ℤ) (1 : ℕ) ∈ U := hs (by simp)
  refine ⟨U, hthree, hseven, hfg, hclosed, ?_⟩
  intro a b
  exact hclosed _ (U.add_mem (U.smul_mem a hthree) (U.smul_mem b hseven))

-- The empty finite set invokes the same API with independent scalar/module universes.
private theorem exists_fg_right_coideal_empty {K : Type*} {C : Type*}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C] [Module.Free K C] :
    ∃ U : Submodule K C,
      (∅ : Set C) ⊆ (U : Set C) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := K) Set.finite_empty

-- Singleton zero is a nonfield call with potentially empty tensor support.
private theorem exists_fg_natural_right_coideal_zero :
    ∃ U : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      (0 : AddMonoidAlgebra ℕ ℤ) ∈ U ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (U.subtype.rTensor (AddMonoidAlgebra ℕ ℤ)) := by
  let : Module.Free ℕ (AddMonoidAlgebra ℕ ℤ) :=
    Module.Free.of_basis (AddMonoidAlgebra.basis ℤ ℕ)
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite
      (K := ℕ) (C := AddMonoidAlgebra ℕ ℤ) (s := {0}) (Set.finite_singleton _)
  exact ⟨U, hs (by simp), hfg, hclosed⟩

-- Mathlib's empty-index Finsupp coalgebra is zero over the nonfield semiring ℕ.
private theorem exists_fg_natural_right_coideal_empty_finsupp :
    ∃ U : Submodule ℕ (Empty →₀ ℕ),
      (Set.univ : Set (Empty →₀ ℕ)) ⊆ (U : Set (Empty →₀ ℕ)) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (U.subtype.rTensor (Empty →₀ ℕ)) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := ℕ)
    (Set.Finite.of_subsingleton _)

-- No nontriviality assumption is needed on the scalars.
private theorem exists_fg_right_coideal_trivial_scalar :
    ∃ U : Submodule PUnit PUnit,
      (Set.univ : Set PUnit) ⊆ (U : Set PUnit) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := PUnit) x ∈
        LinearMap.range (U.subtype.rTensor PUnit) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := PUnit)
    (Set.Finite.of_subsingleton _)

/-- Free coalgebras use inferred projectivity with a named scalar argument. -/
theorem free_right_coideal_call {K C : Type*}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [Module.Free K C] {s : Set C} (hs : s.Finite) :
    ∃ U : Submodule K C, s ⊆ (U : Set C) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := K) hs

/-- The expected submodule conclusion also infers the scalar for a free caller. -/
theorem free_right_coideal_inferred_scalar {K C : Type*}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [Module.Free K C] {s : Set C} (hs : s.Finite) :
    ∃ U : Submodule K C, s ⊆ (U : Set C) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite hs

/-- Arbitrary fields still use the unchanged two-factor containment theorem. -/
theorem field_two_factor_call {K C : Type*}
    [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
    {s : Set C} (hs : s.Finite) :
    ∃ D : Submodule K C, s ⊆ (D : Set C) ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := K) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) :=
  Coalgebra.exists_fg_submodule_comul_closed_of_finite (K := K) hs

/-- The infinite Finsupp coalgebra over `ℕ` is a free semiring example. -/
theorem natural_finsupp_right_coideal :
    ∃ U : Submodule ℕ (ℕ →₀ ℕ), Finsupp.single 3 1 ∈ U ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (U.subtype.rTensor (ℕ →₀ ℕ)) := by
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := ℕ)
      (s := {Finsupp.single 3 1}) (Set.finite_singleton _)
  exact ⟨U, hs (by simp), hfg, hclosed⟩

/-- The empty finite subset is a projective-module call, in independent universes. -/
theorem projective_right_coideal_empty {K C : Type*}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [Module.Projective K C] :
    ∃ U : Submodule K C, (∅ : Set C) ⊆ (U : Set C) ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C) :=
  Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := K) Set.finite_empty

/-- Three is an idempotent in the scalar ring of the nonfree examples. -/
theorem zmod_six_three_idempotent : IsIdempotentElem (3 : ZMod 6) := by
  change (3 : ZMod 6) * 3 = 3
  decide

/-- Install the existing idempotent-ideal coalgebra, with counit scalar inclusion. -/
noncomputable local instance zmodSixIdealCoalgebra :
    Coalgebra (ZMod 6) (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) :=
  zmod_six_three_idempotent.coalgebraSpan

/-- The countable direct sum is projective by its existing canonical section. -/
noncomputable local instance countableZmodSixIdealProjective :
    Module.Projective (ZMod 6) (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) := by
  obtain ⟨σ, hσ, _⟩ :=
    (TensorProduct.SplitExamples.countable_ideal_tensor_coordinates 0).2.2
  exact ⟨⟨σ, hσ⟩⟩

/-- The ideal `(3)` is a direct summand of its countable projective direct sum. -/
noncomputable local instance zmodSixIdealProjective :
    Module.Projective (ZMod 6) (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) := by
  apply Module.Projective.of_split (Finsupp.lsingle (0 : ℕ)) (Finsupp.lapply 0)
  ext d
  simp

/-- The installed ideal coalgebra is genuinely projective but not free. -/
theorem zmod_six_ideal_projective_not_free :
    Module.Projective (ZMod 6) (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) ∧
      ¬ Module.Free (ZMod 6) (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) :=
  ⟨inferInstance, TensorProduct.SplitExamples.idempotent_ideal_coordinate.1⟩

/-- Projectivity does not force the counit image to be the whole scalar ring. -/
theorem zmod_six_ideal_counit_range_ne_top :
    LinearMap.range (Coalgebra.counit (R := ZMod 6)
      (A := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))) ≠ ⊤ := by
  rw [zmod_six_three_idempotent.coalgebraSpan_counit, Submodule.range_subtype]
  intro h
  have hmem : (1 : ZMod 6) ∈ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)) := by
    rw [h]
    exact Submodule.mem_top
  have hmul := congrArg
    (fun d : Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)) ↦ (d : ZMod 6))
    (zmod_six_three_idempotent.smul_span_singleton ⟨1, hmem⟩)
  have hne : (3 : ZMod 6) ≠ 1 := by decide
  exact hne (by simpa using hmul)

/-- Finite right-coideal containment applies to the nonfree ideal coalgebra. -/
theorem zmod_six_ideal_right_coideal :
    ∃ U : Submodule (ZMod 6) (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))),
      Ideal.spanSingletonGenerator (3 : ZMod 6) ∈ U ∧ U.FG ∧
      ∀ x ∈ U, Coalgebra.comul (R := ZMod 6) x ∈
        LinearMap.range
          (U.subtype.rTensor (Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))) := by
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := ZMod 6)
      (s := {Ideal.spanSingletonGenerator (3 : ZMod 6)}) (Set.finite_singleton _)
  exact ⟨U, hs (by simp), hfg, hclosed⟩

/-- The countable ideal coalgebra is projective, nonfree and not module-finite.
Thus neither freeness nor ambient finite generation is implicit in containment. -/
theorem countable_zmod_six_ideal_projective_not_free_not_finite :
    Module.Projective (ZMod 6) (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) ∧
      ¬ Module.Free (ZMod 6) (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) ∧
      ¬ Module.Finite (ZMod 6) (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) := by
  have h := TensorProduct.SplitExamples.countable_ideal_tensor_coordinates 0
  exact ⟨inferInstance, h.1, h.2.1⟩

/-- The infinite nonfree coalgebra has a proper FG right coideal containing two
specified vectors. Its all-member clause applies to arbitrary scalar combinations. -/
theorem countable_zmod_six_ideal_right_coideal :
    ∃ U : Submodule (ZMod 6) (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))),
      Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)) ∈ U ∧
      Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6)) ∈ U ∧
      U.FG ∧ U ≠ ⊤ ∧
      (∀ x ∈ U, Coalgebra.comul (R := ZMod 6) x ∈
        LinearMap.range
          (U.subtype.rTensor (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))))) ∧
      ∀ r t : ZMod 6, Coalgebra.comul (R := ZMod 6)
          (r • Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)) +
            t • Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6))) ∈
        LinearMap.range
          (U.subtype.rTensor (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))) := by
  obtain ⟨U, hs, hfg, hclosed⟩ :=
    Coalgebra.exists_fg_submodule_comul_right_closed_of_finite (K := ZMod 6)
      (s := {Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)),
        Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6))})
      ((Set.finite_singleton _).insert _)
  have h3 := hs (by simp : Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)) ∈
    {Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)),
      Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6))})
  have h7 := hs (by simp : Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6)) ∈
    {Finsupp.single 3 (Ideal.spanSingletonGenerator (3 : ZMod 6)),
      Finsupp.single 7 (Ideal.spanSingletonGenerator (3 : ZMod 6))})
  refine ⟨U, h3, h7, hfg, ?_, hclosed, ?_⟩
  · intro htop
    exact countable_zmod_six_ideal_projective_not_free_not_finite.2.2
      (Module.Finite.of_fg_top (htop ▸ hfg))
  · intro r t
    exact hclosed _ (U.add_mem (U.smul_mem r h3) (U.smul_mem t h7))

end CoalgebraExamples
