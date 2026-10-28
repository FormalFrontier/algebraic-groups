/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Tactic.NormNum

/-!
# Joins of scalar subcomodules over the integers

The submodules of `ℤ` spanned by `2` and `3` are nonzero, proper and distinct.
Their join is top: `(-1) • 2 + 3 = 1`. The scalar subcomodule construction
preserves this join, so the join contains `1` although neither summand does.
The same pair, indexed by `Bool`, illustrates the named indexed join.

The boundary examples cover the zero subcomodule, a binary self-join
and an empty indexed join. Each scalar subtype coaction is the inverse
right unitor.

## References

These examples use Mathlib's submodule span, integer divisibility and order
APIs, together with the scalar comodule and subcomodule constructions.
-/

@[expose] public section

open Coalgebra
open Coalgebra.RightComodule

namespace SubcomoduleJoinExamples

local notation "U₂" => Submodule.span ℤ ({2} : Set ℤ)
local notation "U₃" => Submodule.span ℤ ({3} : Set ℤ)

private theorem two_mem : (2 : ℤ) ∈ U₂ := Submodule.mem_span_singleton_self 2

private theorem three_mem : (3 : ℤ) ∈ U₃ := Submodule.mem_span_singleton_self 3

private theorem span_separation :
    (1 : ℤ) ∉ U₂ ∧ (1 : ℤ) ∉ U₃ ∧ (2 : ℤ) ∉ U₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have hd : (2 : ℤ) ∣ 1 :=
      ⟨a, by simpa only [smul_eq_mul, mul_comm] using ha.symm⟩
    norm_num at hd
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have hd : (3 : ℤ) ∣ 1 :=
      ⟨a, by simpa only [smul_eq_mul, mul_comm] using ha.symm⟩
    norm_num at hd
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have hd : (3 : ℤ) ∣ 2 :=
      ⟨a, by simpa only [smul_eq_mul, mul_comm] using ha.symm⟩
    norm_num at hd

/-- Neither integer span is zero or top, and the two spans are distinct. -/
theorem integer_spans_nontrivial :
    U₂ ≠ ⊥ ∧ U₃ ≠ ⊥ ∧ U₂ ≠ ⊤ ∧ U₃ ≠ ⊤ ∧ U₂ ≠ U₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hm := two_mem
    rw [h, Submodule.mem_bot] at hm
    norm_num at hm
  · intro h
    have hm := three_mem
    rw [h, Submodule.mem_bot] at hm
    norm_num at hm
  · intro h
    exact span_separation.1 (h.symm ▸ Submodule.mem_top)
  · intro h
    exact span_separation.2.1 (h.symm ▸ Submodule.mem_top)
  · intro h
    exact span_separation.2.2 (h ▸ two_mem)

/-- The integer `1` is a sum of members of the two different spans. -/
theorem one_mem_integer_spans_sup : (1 : ℤ) ∈ U₂ ⊔ U₃ := by
  refine Submodule.mem_sup.mpr
    ⟨(-1 : ℤ) • 2, Submodule.smul_mem U₂ (-1) two_mem, 3, three_mem, ?_⟩
  norm_num [smul_eq_mul]

/-- The spans of `2` and `3` together generate the integer module. -/
theorem integer_spans_sup_eq_top : U₂ ⊔ U₃ = ⊤ := by
  apply top_unique
  intro x _
  simpa only [smul_eq_mul, mul_one] using
    (U₂ ⊔ U₃).smul_mem x one_mem_integer_spans_sup

/-- The two stable scalar submodules have a stable binary join. -/
example : (scalar ℤ ℤ).IsStable (U₂ ⊔ U₃) :=
  (scalar_isStable U₂).sup (scalar_isStable U₃)

/-- Joining the two specified scalar subcomodules gives the scalar subcomodule on top. -/
theorem scalar_integer_spans_sup :
    scalarSubcomodule U₂ ⊔ scalarSubcomodule U₃ =
      scalarSubcomodule (⊤ : Submodule ℤ ℤ) := by
  calc
    scalarSubcomodule U₂ ⊔ scalarSubcomodule U₃ =
        scalarSubcomodule (U₂ ⊔ U₃) := scalarSubcomodule_sup U₂ U₃
    _ = scalarSubcomodule (⊤ : Submodule ℤ ℤ) :=
      congrArg scalarSubcomodule integer_spans_sup_eq_top

/-- The binary join has top underlying submodule. -/
theorem scalar_integer_spans_sup_toSubmodule :
    (scalarSubcomodule U₂ ⊔ scalarSubcomodule U₃).toSubmodule = ⊤ := by
  rw [scalar_integer_spans_sup, scalarSubcomodule_toSubmodule]

/-- The binary join contains a member which belongs to neither summand. -/
theorem scalar_integer_spans_new_member :
    (1 : ℤ) ∈ scalarSubcomodule U₂ ⊔ scalarSubcomodule U₃ ∧
      (1 : ℤ) ∉ scalarSubcomodule U₂ ∧ (1 : ℤ) ∉ scalarSubcomodule U₃ := by
  refine ⟨?_, span_separation.1, span_separation.2.1⟩
  rw [← Subcomodule.mem_toSubmodule, scalar_integer_spans_sup_toSubmodule]
  exact Submodule.mem_top

/-- The same two summands, indexed by `Bool`, also have top named indexed join. -/
example :
    Subcomodule.iSup
        (fun b : Bool ↦ scalarSubcomodule (if b then U₂ else U₃)) =
      scalarSubcomodule (⊤ : Submodule ℤ ℤ) := by
  rw [scalarSubcomodule_iSup]
  congr 1
  apply le_antisymm le_top
  rw [← integer_spans_sup_eq_top]
  exact sup_le (le_iSup (fun b : Bool ↦ if b then U₂ else U₃) true)
    (le_iSup (fun b : Bool ↦ if b then U₂ else U₃) false)

example :
    Subcomodule.bot (scalar ℤ ℤ) ⊔ scalarSubcomodule U₂ = scalarSubcomodule U₂ :=
  bot_sup_eq _

example : scalarSubcomodule U₂ ⊔ scalarSubcomodule U₂ = scalarSubcomodule U₂ :=
  sup_idem _

example :
    Subcomodule.iSup (fun _ : Empty ↦ scalarSubcomodule U₂) =
      Subcomodule.bot (scalar ℤ ℤ) := by
  apply Subcomodule.ext
  rw [Subcomodule.iSup_toSubmodule, Subcomodule.bot_toSubmodule]
  exact iSup_of_empty _

end SubcomoduleJoinExamples
