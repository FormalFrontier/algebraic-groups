/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.Tactic.NormNum

/-!
# Coideal joins in the integer additive group algebra

In `AddMonoidAlgebra ℤ ℤ`, write `e n` for the standard vector at `n`.
The lines spanned by `e 0 - e 1` and `e 0 - e 2` are nonzero, proper and
incomparable coideals. Their binary join is still proper. Local proofs from
`Submodule.IsCoideal.sup` give the quotient coalgebra and its canonical
projection as a value: the two generators vanish, while the class of `e 0`
has counit `1`, diagonal comultiplication and is nonzero.

The arbitrary-join theorem is also used on the infinite family of lines
spanned by `e 0 - e n`, indexed by all integers. Its quotient projection
identifies every `e n` with `e 0`, and this common class remains nonzero.
An empty family gives the bottom submodule and its quotient projection.

All coalgebra structures on the group algebra and its quotients are supplied
by Mathlib. Coideal proofs are installed only locally; no instance search
rule for joins is added.

## References

- Mathlib's `Mathlib.RingTheory.Bialgebra.MonoidAlgebra` supplies the lawful
  group algebra and its group-like standard vectors.
- Mathlib's submodule-span, coefficient and quotient APIs supply membership,
  incomparability and readback on representatives.
-/

@[expose] public section

noncomputable section

open Coalgebra
open scoped TensorProduct

namespace AddMonoidAlgebra

private abbrev A := AddMonoidAlgebra ℤ ℤ

private abbrev e (n : ℤ) : A := single n 1

private abbrev differenceLine (n : ℤ) : Submodule ℤ A :=
  Submodule.span ℤ ({e 0 - e n} : Set A)

private lemma difference_mem (n : ℤ) : e 0 - e n ∈ differenceLine n :=
  Submodule.mem_span_singleton_self _

private lemma counit_e (n : ℤ) : counit (R := ℤ) (e n) = 1 :=
  (isGroupLikeElem_single_one (R := ℤ) (A := ℤ) n).counit_eq_one

private lemma comul_e (n : ℤ) : comul (R := ℤ) (e n) = e n ⊗ₜ[ℤ] e n :=
  (isGroupLikeElem_single_one (R := ℤ) (A := ℤ) n).comul_eq_tmul_self

private lemma differenceLine_isCoideal (n : ℤ) : (differenceLine n).IsCoideal := by
  apply (Submodule.isCoideal_span_iff (R := ℤ) ({e 0 - e n} : Set A)).mpr
  constructor
  · intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simp only [map_sub, counit_e, sub_self]
  · intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hq : (differenceLine n).mkQ (e 0) = (differenceLine n).mkQ (e n) := by
      apply sub_eq_zero.mp
      rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact difference_mem n
    change TensorProduct.map (differenceLine n).mkQ (differenceLine n).mkQ
      (comul (R := ℤ) (e 0 - e n)) = 0
    simp only [map_sub, comul_e, TensorProduct.map_tmul, hq, sub_self]

private lemma differenceLine_ne_bot {n : ℤ} (hn : n ≠ 0) : differenceLine n ≠ ⊥ := by
  intro h
  have hx := difference_mem n
  rw [h, Submodule.mem_bot] at hx
  have hc := congrArg (fun x : A => x.coeff n) hx
  simp only [e, coeff_sub, coeff_single, coeff_zero, Finsupp.sub_apply,
    Finsupp.single_apply, ite_eq_right (Ne.symm hn), Finsupp.zero_apply] at hc
  norm_num at hc

private lemma differenceLine_not_le {m n : ℤ} (hm : m ≠ 0) (hmn : m ≠ n) :
    ¬ differenceLine m ≤ differenceLine n := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h (difference_mem m))
  have hc := congrArg (fun x : A => x.coeff m) ha
  simp only [coeff_smul_apply, e, coeff_sub, coeff_single, Finsupp.sub_apply,
    Finsupp.single_apply, ite_eq_right (Ne.symm hm), ite_eq_right (Ne.symm hmn)] at hc
  norm_num at hc

private lemma proper_of_isCoideal (I : Submodule ℤ A) [I.IsCoideal] : I ≠ ⊤ := by
  intro h
  have hz := Submodule.IsCoideal.counit_eq_zero (I := I)
    (show e 0 ∈ I by rw [h]; exact Submodule.mem_top)
  rw [counit_e] at hz
  norm_num at hz

section BinaryJoin

local instance :
    (Submodule.span ℤ
      ({single 0 1 - single 1 1} : Set (AddMonoidAlgebra ℤ ℤ)) ⊔
      Submodule.span ℤ ({single 0 1 - single 2 1} : Set (AddMonoidAlgebra ℤ ℤ))).IsCoideal :=
  (differenceLine_isCoideal 1).sup (differenceLine_isCoideal 2)

private abbrev binaryProjection :
    A →ₗc[ℤ] A ⧸ (differenceLine 1 ⊔ differenceLine 2) :=
  Coalgebra.Quotient.mkQCoalgHom _

/-- Two nonzero incomparable coideal lines in the integer group algebra have a proper join. -/
theorem integer_difference_lines_nontrivial :
    let I := Submodule.span ℤ
      ({single 0 1 - single 1 1} : Set (AddMonoidAlgebra ℤ ℤ))
    let J := Submodule.span ℤ
      ({single 0 1 - single 2 1} : Set (AddMonoidAlgebra ℤ ℤ))
    I ≠ ⊥ ∧ J ≠ ⊥ ∧ I ≠ ⊤ ∧ J ≠ ⊤ ∧ ¬ I ≤ J ∧ ¬ J ≤ I ∧ I ⊔ J ≠ ⊤ := by
  have hjoin := proper_of_isCoideal (differenceLine 1 ⊔ differenceLine 2)
  refine ⟨differenceLine_ne_bot (by norm_num), differenceLine_ne_bot (by norm_num),
    ?_, ?_, differenceLine_not_le (by norm_num) (by norm_num),
    differenceLine_not_le (by norm_num) (by norm_num), hjoin⟩
  · intro h
    change differenceLine 1 = ⊤ at h
    apply hjoin
    rw [h, top_sup_eq]
  · intro h
    change differenceLine 2 = ⊤ at h
    apply hjoin
    rw [h, sup_top_eq]

private lemma binaryProjection_difference (n : ℤ)
    (hn : e 0 - e n ∈ differenceLine 1 ⊔ differenceLine 2) :
    binaryProjection (e 0 - e n) = 0 := by
  rw [Coalgebra.Quotient.mkQCoalgHom_apply, Submodule.Quotient.mk_eq_zero]
  exact hn

/-- The canonical quotient projection kills both generators; its class at `0`
remains nonzero, with counit `1` and diagonal comultiplication. -/
theorem integer_binary_join_quotient_values :
    let I := Submodule.span ℤ
      ({single 0 1 - single 1 1} : Set (AddMonoidAlgebra ℤ ℤ)) ⊔
      Submodule.span ℤ ({single 0 1 - single 2 1} : Set (AddMonoidAlgebra ℤ ℤ))
    let q := Coalgebra.Quotient.mkQCoalgHom I
    q (single 0 1 - single 1 1) = 0 ∧ q (single 0 1 - single 2 1) = 0 ∧
      q (single 0 1) = q (single 1 1) ∧ q (single 0 1) = q (single 2 1) ∧
      counit (R := ℤ) (q (single 0 1)) = 1 ∧
      comul (R := ℤ) (q (single 0 1)) = q (single 0 1) ⊗ₜ[ℤ] q (single 0 1) ∧
      q (single 0 1) ≠ 0 := by
  have h1 := binaryProjection_difference 1 (Submodule.mem_sup_left (difference_mem 1))
  have h2 := binaryProjection_difference 2 (Submodule.mem_sup_right (difference_mem 2))
  have hg := (isGroupLikeElem_single_one (R := ℤ) (A := ℤ) (0 : ℤ)).map binaryProjection
  refine ⟨h1, h2, ?_, ?_, hg.counit_eq_one, hg.comul_eq_tmul_self, hg.ne_zero⟩
  · apply sub_eq_zero.mp
    rwa [← map_sub]
  · apply sub_eq_zero.mp
    rwa [← map_sub]

end BinaryJoin

section ArbitraryJoin

private abbrev allDifferenceLines : Submodule ℤ A := ⨆ n : ℤ, differenceLine n

local instance :
    (⨆ n : ℤ, Submodule.span ℤ
      ({single 0 1 - single n 1} : Set (AddMonoidAlgebra ℤ ℤ))).IsCoideal :=
  Submodule.IsCoideal.iSup differenceLine differenceLine_isCoideal

private abbrev allProjection : A →ₗc[ℤ] A ⧸ allDifferenceLines :=
  Coalgebra.Quotient.mkQCoalgHom _

/-- An infinite join gives a proper quotient, whose projection identifies all
standard vectors without annihilating their common class. -/
theorem integer_arbitrary_join_quotient_values :
    let I := ⨆ n : ℤ, Submodule.span ℤ
      ({single 0 1 - single n 1} : Set (AddMonoidAlgebra ℤ ℤ))
    let q := Coalgebra.Quotient.mkQCoalgHom I
    I ≠ ⊤ ∧ (∀ n : ℤ, q (single 0 1 - single n 1) = 0) ∧
      (∀ n : ℤ, q (single 0 1) = q (single n 1)) ∧
      counit (R := ℤ) (q (single 0 1)) = 1 ∧ q (single 0 1) ≠ 0 := by
  have hd (n : ℤ) : allProjection (e 0 - e n) = 0 := by
    rw [Coalgebra.Quotient.mkQCoalgHom_apply, Submodule.Quotient.mk_eq_zero]
    exact (le_iSup differenceLine n) (difference_mem n)
  have hg := (isGroupLikeElem_single_one (R := ℤ) (A := ℤ) (0 : ℤ)).map allProjection
  refine ⟨proper_of_isCoideal allDifferenceLines, hd, ?_, hg.counit_eq_one, hg.ne_zero⟩
  intro n
  apply sub_eq_zero.mp
  rw [← map_sub, hd]

end ArbitraryJoin

section EmptyJoin

private abbrev emptyJoin : Submodule ℤ A := ⨆ _ : Empty, (⊥ : Submodule ℤ A)

private local instance : emptyJoin.IsCoideal :=
  Submodule.IsCoideal.iSup (fun _ : Empty => (⊥ : Submodule ℤ A)) (fun i => nomatch i)

example : emptyJoin = ⊥ := by simp [emptyJoin]

example : (Coalgebra.Quotient.mkQCoalgHom emptyJoin) (e 0) ≠ 0 :=
  ((isGroupLikeElem_single_one (R := ℤ) (A := ℤ) (0 : ℤ)).map
    (Coalgebra.Quotient.mkQCoalgHom emptyJoin)).ne_zero

end EmptyJoin

end AddMonoidAlgebra
