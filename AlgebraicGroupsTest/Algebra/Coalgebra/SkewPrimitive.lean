/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.SkewPrimitive
import AlgebraicGroupsTest.Algebra.Coalgebra.GroupLikeHom
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Differences of group-like elements and translations of skew primitives

These examples compose the group-like difference lemma with the existing
singleton-span, submodule membership, and ordinary translation APIs. The
translation is a permutation of the skew-primitive submodule, not a linear,
additive, or coalgebra equivalence.

The diagonal coalgebra on `AddMonoidAlgebra ℤ ℤ` has distinct normalized
endpoints, a nonzero difference, and a third basis vector outside the
skew-primitive submodule. Both that submodule and the difference span are
nonzero and proper. Its integer-indexed basis also proves that the ambient
module is not finitely generated; finite support of each vector does not make
the ambient module finite. No equality between the skew submodule and the
difference span, or quotient or extension-class description, is asserted.

Coincident endpoints, zero translation scalar, the scalar-self coalgebra, and
zero scalars are collapsing cases. The zero carrier over nontrivial scalars
has no normalized group-like endpoints and is not a positive witness.

## References

These examples reuse Robert Hawkins's Mathlib skew-primitive formalization,
Yaël Dillies and Michał Mrugała's group-like formalization, and Mathlib's
monoid-algebra coalgebra and bialgebra formalizations by Amelia Livingston,
Yaël Dillies, and Michał Mrugała. The module and basis constructions follow
Mathlib's monoid-algebra module API by Johannes Hölzl, Yury Kudryashov, and
Kim Morrison; the non-finiteness argument uses Johan Commelin's finite-module
API. The mathematical skew-primitive terminology follows Etingof, Gelaki,
Nikshych, and Ostrik, *Tensor Categories*, as in Mathlib's primitive module.
-/

open Coalgebra
open scoped TensorProduct

universe u v

noncomputable section

namespace CoalgebraTest.SkewPrimitive

section StockClients

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]
variable {g h : C}

-- Neither membership of a nor invertibility of t is an input.
example (hg : IsGroupLikeElem R g) (hh : IsGroupLikeElem R h) (a : C) (t : R) :
    Submodule.span R {g - h} ≤ skewPrimitive R g h ∧
      (a + t • (g - h) ∈ skewPrimitive R g h ↔ a ∈ skewPrimitive R g h) ∧
      (IsSkewPrimitiveElem R g h (a + t • (g - h)) ↔ IsSkewPrimitiveElem R g h a) := by
  have hd : g - h ∈ skewPrimitive R g h :=
    mem_skewPrimitive.mpr (hg.isSkewPrimitiveElem_sub hh)
  have ht := (skewPrimitive R g h).smul_mem t hd
  have hiff := (skewPrimitive R g h).add_mem_iff_left (x := a) ht
  refine ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr hd, ?_, ?_⟩
  · exact ⟨fun ha => hiff.mp ha, fun ha => hiff.mpr ha⟩
  · simpa only [mem_skewPrimitive] using hiff

-- The construction is the stock permutation on the existing subtype.
-- Coercions read back both its action and its inverse in the ambient module.
example (hg : IsGroupLikeElem R g) (hh : IsGroupLikeElem R h) (t : R) :
    let S := skewPrimitive R g h
    let d : S := ⟨g - h, mem_skewPrimitive.mpr (hg.isSkewPrimitiveElem_sub hh)⟩
    let e : S ≃ S := Equiv.addRight (t • d)
    (∀ x : S, (e x : C) = (x : C) + t • (g - h) ∧
      (e.symm x : C) = (x : C) - t • (g - h)) ∧
      (∀ x : S, e.symm (e x) = x) ∧ (∀ x : S, e (e.symm x) = x) := by
  let S := skewPrimitive R g h
  let d : S := ⟨g - h, mem_skewPrimitive.mpr (hg.isSkewPrimitiveElem_sub hh)⟩
  let e : S ≃ S := Equiv.addRight (t • d)
  refine ⟨?_, e.symm_apply_apply, e.apply_symm_apply⟩
  intro x
  constructor
  · simp only [Equiv.coe_addRight, Submodule.coe_add, Submodule.coe_smul]
  · simp only [Equiv.addRight_symm_apply, Submodule.coe_add, Submodule.coe_neg,
      Submodule.coe_smul, sub_eq_add_neg]

end StockClients

section IntegerDiagonal

private abbrev IntegerDiagonal := AddMonoidAlgebra ℤ ℤ

private abbrev leftPoint : IntegerDiagonal := AddMonoidAlgebra.single 0 1
private abbrev rightPoint : IntegerDiagonal := AddMonoidAlgebra.single 1 1
private abbrev difference : IntegerDiagonal := leftPoint - rightPoint
private abbrev outsidePoint : IntegerDiagonal := AddMonoidAlgebra.single 2 1
private abbrev skew : Submodule ℤ IntegerDiagonal := skewPrimitive ℤ leftPoint rightPoint
private abbrev differenceSpan : Submodule ℤ IntegerDiagonal := Submodule.span ℤ {difference}

private theorem leftPoint_groupLike : IsGroupLikeElem ℤ leftPoint :=
  AddMonoidAlgebra.isGroupLikeElem_single_one 0

private theorem rightPoint_groupLike : IsGroupLikeElem ℤ rightPoint :=
  AddMonoidAlgebra.isGroupLikeElem_single_one 1

private theorem difference_skew : IsSkewPrimitiveElem ℤ leftPoint rightPoint difference :=
  leftPoint_groupLike.isSkewPrimitiveElem_sub rightPoint_groupLike

private theorem difference_mem : difference ∈ skew := mem_skewPrimitive.mpr difference_skew

private theorem difference_coefficients :
    difference.coeff 0 = 1 ∧ difference.coeff 1 = -1 ∧ difference.coeff 2 = 0 := by
  simp only [difference, leftPoint, rightPoint, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_single]
  simp

private theorem endpoints_ne : leftPoint ≠ rightPoint := by
  intro h
  have hc := congrArg (fun x : IntegerDiagonal => x.coeff 0) h
  simp [leftPoint, rightPoint] at hc

private theorem difference_ne_zero : difference ≠ 0 := by
  intro h
  have hc := congrArg (fun x : IntegerDiagonal => x.coeff 0) h
  rw [difference_coefficients.1] at hc
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (one_ne_zero : (1 : ℤ) ≠ 0) hc

private theorem outsidePoint_counit : counit (R := ℤ) outsidePoint = 1 := by
  simp only [outsidePoint, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]

private theorem outsidePoint_not_mem : outsidePoint ∉ skew := by
  intro hw
  exact (one_ne_zero : (1 : ℤ) ≠ 0)
    (outsidePoint_counit.symm.trans (mem_skewPrimitive.mp hw).counit_eq_zero)

private theorem differenceSpan_le : differenceSpan ≤ skew :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr difference_mem

-- Both fields of the canonical predicate, with the ordered (leftPoint,rightPoint) tensors.
example : IsGroupLikeElem ℤ leftPoint ∧ IsGroupLikeElem ℤ rightPoint ∧
    counit (R := ℤ) difference = 0 ∧
      comul difference = leftPoint ⊗ₜ[ℤ] difference + difference ⊗ₜ[ℤ] rightPoint :=
  ⟨leftPoint_groupLike, rightPoint_groupLike,
    difference_skew.counit_eq_zero, difference_skew.comul_eq_tmul_add_tmul⟩

-- An inhabited subtype with a specified nonzero element, and proper/nonzero submodules.
example : leftPoint ≠ rightPoint ∧ difference ≠ 0 ∧
    difference.coeff 0 = 1 ∧ difference.coeff 1 = -1 ∧ difference.coeff 2 = 0 ∧
    (∃ x : skew, (x : IntegerDiagonal) = difference ∧ x ≠ 0) ∧
    skew ≠ ⊥ ∧ skew ≠ ⊤ ∧ differenceSpan ≤ skew ∧
    differenceSpan ≠ ⊥ ∧ differenceSpan ≠ ⊤ ∧ outsidePoint ∉ differenceSpan := by
  have hSbot : skew ≠ ⊥ := by
    intro h
    exact difference_ne_zero ((Submodule.mem_bot ℤ).mp (h ▸ difference_mem))
  have hStop : skew ≠ ⊤ := by
    intro h
    apply outsidePoint_not_mem
    rw [h]
    exact Submodule.mem_top
  have hDout : outsidePoint ∉ differenceSpan := fun hw =>
    outsidePoint_not_mem (differenceSpan_le hw)
  have hDbot : differenceSpan ≠ ⊥ := by
    intro h
    exact difference_ne_zero (Submodule.span_singleton_eq_bot.mp h)
  have hDtop : differenceSpan ≠ ⊤ := by
    intro h
    apply hDout
    rw [h]
    exact Submodule.mem_top
  refine ⟨endpoints_ne, difference_ne_zero,
    difference_coefficients.1, difference_coefficients.2.1, difference_coefficients.2.2,
    ⟨⟨difference, difference_mem⟩, rfl, ?_⟩, hSbot, hStop, differenceSpan_le,
    hDbot, hDtop, hDout⟩
  intro h
  exact difference_ne_zero (congrArg (fun x : skew => (x : IntegerDiagonal)) h)

-- The wrapper's coefficient equivalence and its genuinely infinite-index basis are used directly.
example (x : IntegerDiagonal) (n : ℤ) :
    (AddMonoidAlgebra.coeffLinearEquiv ℤ x : ℤ →₀ ℤ) = x.coeff ∧
      AddMonoidAlgebra.basis ℤ ℤ n = AddMonoidAlgebra.single n 1 := by
  constructor
  · rfl
  · exact AddMonoidAlgebra.basis_apply ℤ n

example : Infinite IntegerDiagonal := inferInstance

example : ¬ Module.Finite ℤ IntegerDiagonal :=
  Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℤ ℤ)

-- With a=0 and t=1 the permutation genuinely moves zero; its inverse recovers zero.
example :
    let d : skew := ⟨difference, difference_mem⟩
    let e : skew ≃ skew := Equiv.addRight ((1 : ℤ) • d)
    (e 0 : IntegerDiagonal) = difference ∧ e 0 ≠ 0 ∧ e.symm d = 0 ∧
      e ≠ Equiv.refl skew ∧
      (∀ x : skew, (e.symm x : IntegerDiagonal) = (x : IntegerDiagonal) - difference) ∧
      (∀ x : skew, e.symm (e x) = x) := by
  let d : skew := ⟨difference, difference_mem⟩
  let e : skew ≃ skew := Equiv.addRight ((1 : ℤ) • d)
  have hval : (e 0 : IntegerDiagonal) = difference := by
    simp only [e, one_smul, Equiv.coe_addRight, zero_add, d]
  have hmove : e 0 ≠ 0 := by
    intro h
    apply difference_ne_zero
    rw [← hval]
    exact congrArg (fun x : skew => (x : IntegerDiagonal)) h
  refine ⟨hval, hmove, ?_, ?_, ?_, e.symm_apply_apply⟩
  · simp only [one_smul, Equiv.addRight_symm_apply, add_neg_cancel]
  · intro h
    apply hmove
    exact congrArg (fun f : skew ≃ skew => f 0) h
  · intro x
    simp only [one_smul, Equiv.addRight_symm_apply, Submodule.coe_add,
      Submodule.coe_neg, sub_eq_add_neg]

-- False/false membership preservation: the translate of the outside vector stays outside for all t.
example (t : ℤ) : counit (R := ℤ) (outsidePoint + t • difference) = 1 ∧
    outsidePoint ∉ skew ∧ outsidePoint + t • difference ∉ skew ∧
      (outsidePoint + t • difference ∈ skew ↔ outsidePoint ∈ skew) := by
  have hε : counit (R := ℤ) (outsidePoint + t • difference) = 1 := by
    simp only [map_add, map_smul, difference_skew.counit_eq_zero, smul_zero,
      add_zero, outsidePoint_counit]
  have hout : outsidePoint + t • difference ∉ skew := by
    intro hx
    exact (one_ne_zero : (1 : ℤ) ≠ 0)
      (hε.symm.trans (mem_skewPrimitive.mp hx).counit_eq_zero)
  exact ⟨hε, outsidePoint_not_mem, hout,
    (skew.add_mem_iff_left (skew.smul_mem t difference_mem))⟩

-- Removing endpoint normalization is not a difference theorem, even in this lawful coalgebra.
example : ¬ IsGroupLikeElem ℤ (0 : IntegerDiagonal) ∧
    ¬ IsSkewPrimitiveElem ℤ leftPoint 0 (leftPoint - 0) := by
  constructor
  · intro h
    exact h.ne_zero rfl
  · intro h
    have hε := h.counit_eq_zero
    simp only [sub_zero, leftPoint_groupLike.counit_eq_one] at hε
    exact (one_ne_zero : (1 : ℤ) ≠ 0) hε

end IntegerDiagonal

section CollapsingCases

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C]

-- Coincident endpoints do not assert that the whole skew submodule vanishes.
example (g : C) (t : R) : Submodule.span R {g - g} = ⊥ ∧
    Equiv.addRight (t • (g - g)) = Equiv.refl C := by
  constructor
  · simp only [sub_self, Submodule.span_singleton_eq_bot]
  · ext x
    simp only [Equiv.coe_addRight, sub_self, smul_zero, add_zero, Equiv.refl_apply]

example (g h : C) : Equiv.addRight ((0 : R) • (g - h)) = Equiv.refl C := by
  ext x
  simp only [Equiv.coe_addRight, zero_smul, add_zero, Equiv.refl_apply]

example {g h : R} (hg : IsGroupLikeElem R g) (hh : IsGroupLikeElem R h) :
    g = 1 ∧ h = 1 ∧ g - h = 0 ∧ skewPrimitive R g h = ⊥ ∧
      (∀ t : R, Equiv.addRight (t • (g - h)) = Equiv.refl R) := by
  have hg1 := isGroupLikeElem_self.mp hg
  have hh1 := isGroupLikeElem_self.mp hh
  refine ⟨hg1, hh1, ?_, ?_, ?_⟩
  · rw [hg1, hh1, sub_self]
  · apply le_antisymm
    · intro x hx
      apply (Submodule.mem_bot R).mpr
      simpa only [CommSemiring.counit_apply] using (mem_skewPrimitive.mp hx).counit_eq_zero
    · exact bot_le
  · intro t
    ext x
    simp only [Equiv.coe_addRight, hg1, hh1, sub_self, smul_zero, add_zero, Equiv.refl_apply]

end CollapsingCases

-- Zero scalars allow a normalized zero endpoint, but all motion collapses.
example : IsGroupLikeElem (ZMod 1) (0 : ZMod 1) ∧
    skewPrimitive (ZMod 1) (0 : ZMod 1) 0 = ⊥ ∧
    skewPrimitive (ZMod 1) (0 : ZMod 1) 0 = ⊤ ∧
      (∀ t : ZMod 1, Equiv.addRight (t • (0 - 0 : ZMod 1)) = Equiv.refl (ZMod 1)) := by
  refine ⟨isGroupLikeElem_self.mpr (Subsingleton.elim _ _), ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      apply (Submodule.mem_bot (ZMod 1)).mpr
      simpa only [CommSemiring.counit_apply] using (mem_skewPrimitive.mp hx).counit_eq_zero
    · exact bot_le
  · apply le_antisymm le_top
    intro x _
    rw [mem_skewPrimitive, Subsingleton.elim x 0]
    exact IsSkewPrimitiveElem.zero
  · intro t
    ext x
    simp only [Equiv.coe_addRight, sub_self, smul_zero, add_zero, Equiv.refl_apply]

-- This zero-carrier boundary has no endpoints: it cannot witness nonvacuity over ℤ.
example : ¬ Nonempty (GroupLike ℤ (Empty →₀ ℤ)) ∧
    ¬ Nonempty (ℤ →ₗc[ℤ] (Empty →₀ ℤ)) :=
  Finsupp.not_nonempty_groupLike_and_coalgHom_empty ℤ

end CoalgebraTest.SkewPrimitive
