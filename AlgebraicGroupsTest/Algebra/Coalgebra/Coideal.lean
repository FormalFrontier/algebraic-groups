/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Coideal
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.Tactic.NormNum

/-!
# Coideal cores in the rational group-like coalgebra

The canonical coalgebra on `MonoidAlgebra ℚ ℕ` has its standard basis indexed by
all natural numbers. Its counit kernel contains the nonzero vector `δ₁ - δ₀`
and excludes `δ₀`. The kernel is bundled using `CoalgHomClass.ker_isCoideal`.

The core API fixes this kernel and places `δ₁ - δ₀` in the greatest coideal.
Counit elimination excludes `δ₀` even from that coideal, whose carrier is thus
nonzero and proper, unlike the ambient top submodule. The same witness exercises
binary, set-indexed and natural-number-indexed joins, and core-based meets.

## References

Mathlib's `MonoidAlgebra.instCoalgebra`, `Coalgebra.counitCoalgHom`, and coefficient
API supply the coalgebra, counit morphism and coordinate calculation. The kernel
coideality theorem is from `AlgebraicGroups.Algebra.Coalgebra.Quotient`.
-/

@[expose] public section

namespace CoidealExamples

/-- The rational coalgebra with its natural-number-indexed group-like basis. -/
abbrev C := MonoidAlgebra ℚ ℕ

/-- The standard basis vector at a natural number. -/
noncomputable def delta (n : ℕ) : C := MonoidAlgebra.single n 1

/-- The kernel of the canonical counit, bundled by the kernel coideality theorem. -/
noncomputable def counitKernel : Coideal ℚ C :=
  Coideal.ofSubmodule
    (LinearMap.ofClass (Coalgebra.counitCoalgHom ℚ C) : C →ₗ[ℚ] ℚ).ker
    (CoalgHomClass.ker_isCoideal (Coalgebra.counitCoalgHom ℚ C))

private theorem mem_counitKernel (x : C) :
    x ∈ counitKernel ↔ Coalgebra.counit (R := ℚ) x = 0 := by
  simp only [counitKernel, Coideal.mem_ofSubmodule, LinearMap.mem_ker,
    LinearMap.coe_ofClass, Coalgebra.counitCoalgHom_apply]

/-- The counit kernel is a nonzero proper fixed point of core. The greatest
coideal has a nonzero proper carrier; lattice operations retain the kernel witness. -/
example :
    Coideal.core counitKernel.toSubmodule = counitKernel ∧
    delta 1 - delta 0 ∈ Coideal.core counitKernel.toSubmodule ∧
    delta 1 - delta 0 ≠ 0 ∧
    delta 0 ∉ Coideal.core counitKernel.toSubmodule ∧
    (⊤ : Coideal ℚ C).toSubmodule ≠ ⊥ ∧
    (⊤ : Coideal ℚ C).toSubmodule ≠ ⊤ ∧
    (⊥ : Coideal ℚ C) ≠ ⊤ ∧
    delta 1 - delta 0 ∈ counitKernel ⊔ (⊥ : Coideal ℚ C) ∧
    delta 1 - delta 0 ∈ sSup ({counitKernel, ⊥} : Set (Coideal ℚ C)) ∧
    delta 1 - delta 0 ∈ (⨆ n : ℕ, if n = 0 then counitKernel else ⊥) ∧
    delta 1 - delta 0 ∈ counitKernel ⊓ (⊤ : Coideal ℚ C) ∧
    delta 1 - delta 0 ∈ sInf ({counitKernel, ⊤} : Set (Coideal ℚ C)) := by
  have hx : delta 1 - delta 0 ∈ counitKernel := by
    rw [mem_counitKernel]
    simp [delta]
  have hx_ne : delta 1 - delta 0 ≠ (0 : C) := by
    intro h
    have hcoeff := congrArg (fun z : C => z.coeff 1) h
    norm_num [delta, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single,
      Finsupp.single_apply] at hcoeff
  have hzero : delta 0 ∉ counitKernel := by
    rw [mem_counitKernel]
    simp [delta]
  have hfixed := Coideal.core_coe counitKernel
  have hle : counitKernel ≤ (⊤ : Coideal ℚ C) := by
    rw [Coideal.top_eq_core]
    exact Coideal.le_core_iff.mpr le_top
  have hxtop : delta 1 - delta 0 ∈ (⊤ : Coideal ℚ C) := hle hx
  have hzero_top : delta 0 ∉ (⊤ : Coideal ℚ C) := by
    intro h
    have he := (⊤ : Coideal ℚ C).isCoideal.counit_eq_zero ((Coideal.mem_iff _).mp h)
    norm_num [delta] at he
  have htop_ne_bot : (⊤ : Coideal ℚ C).toSubmodule ≠ ⊥ := by
    intro hbot
    have hmem := (Coideal.mem_iff _).mp hxtop
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx_ne hmem
  have htop_proper : (⊤ : Coideal ℚ C).toSubmodule ≠ ⊤ := by
    intro htop
    apply hzero_top
    apply (Coideal.mem_iff _).mpr
    simp only [htop, Submodule.mem_top]
  have hxm := (Coideal.mem_iff _).mp hx
  refine ⟨hfixed, ?_, hx_ne, ?_, htop_ne_bot, htop_proper, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfixed]
    exact hx
  · rw [hfixed]
    exact hzero
  · intro h
    apply htop_ne_bot
    rw [← h, Coideal.toSubmodule_bot]
  · rw [Coideal.mem_iff, Coideal.toSubmodule_sup]
    exact (le_sup_left : counitKernel.toSubmodule ≤ _) hxm
  · rw [Coideal.mem_iff, Coideal.toSubmodule_sSup]
    exact (le_sSup (Set.mem_image_of_mem Coideal.toSubmodule
      (show counitKernel ∈ ({counitKernel, ⊥} : Set (Coideal ℚ C)) by simp))) hxm
  · rw [Coideal.mem_iff, Coideal.toSubmodule_iSup]
    exact (le_iSup (fun n : ℕ =>
      (if n = 0 then counitKernel else (⊥ : Coideal ℚ C)).toSubmodule) 0) hxm
  · rw [Coideal.inf_eq_core]
    exact (Coideal.le_core (I := counitKernel) (le_inf le_rfl
      (Coideal.toSubmodule_le_toSubmodule.mpr hle))) hx
  · have hmeet : counitKernel.toSubmodule ≤
        sInf (Coideal.toSubmodule '' ({counitKernel, ⊤} : Set (Coideal ℚ C))) := by
      refine le_sInf ?_
      rintro _ ⟨I, hI, rfl⟩
      rcases Set.mem_insert_iff.mp hI with rfl | hI
      · exact le_rfl
      · rw [Set.mem_singleton_iff] at hI
        subst I
        exact Coideal.toSubmodule_le_toSubmodule.mpr hle
    rw [Coideal.sInf_eq_core]
    exact (Coideal.le_core (I := counitKernel) hmeet) hx

end CoidealExamples
