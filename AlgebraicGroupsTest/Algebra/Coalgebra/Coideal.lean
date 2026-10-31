/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Coideal
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.Tactic.NormNum

/-!
# Coideal cores and a group-like coideal correspondence

The canonical coalgebra on `MonoidAlgebra ℚ ℕ` has its standard basis indexed by
all natural numbers. Its counit kernel contains the nonzero vector `δ₁ - δ₀`
and excludes `δ₀`. The kernel is bundled using `CoalgHomClass.ker_isCoideal`.

The core API fixes this kernel and places `δ₁ - δ₀` in the greatest coideal.
Counit elimination excludes `δ₀` even from that coideal, whose carrier is thus
nonzero and proper, unlike the ambient top submodule. The same witness exercises
binary, set-indexed and natural-number-indexed joins, and core-based meets.
Its image under the counit is bottom, and the core-preimage of bottom is this
nonzero proper kernel.

Over `ZMod 4`, the predecessor pushforward on the natural-number-indexed
group-like coalgebra is surjective with nonzero kernel. Its coideal correspondence
sends that kernel to bottom and the source counit kernel to the nonzero target
counit kernel, giving two distinct inputs to the order isomorphism.

## References

Mathlib's `MonoidAlgebra.instCoalgebra`, `Coalgebra.counitCoalgHom`, and coefficient
API supply the rational coalgebra, counit morphism and coordinate calculation.
The modular example uses `Finsupp.instCoalgebra`, `Finsupp.lmapDomain` and
`Finsupp.mapDomain_surjective`. The kernel coideality theorems are from
`AlgebraicGroups.Algebra.Coalgebra.Quotient`.
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
coideal has a nonzero proper carrier; lattice operations retain the kernel witness.
The counit sends the kernel to bottom and has this kernel as the core-preimage of bottom. -/
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
    delta 1 - delta 0 ∈ sInf ({counitKernel, ⊤} : Set (Coideal ℚ C)) ∧
    Coideal.map (Coalgebra.counitCoalgHom ℚ C) counitKernel = (⊥ : Coideal ℚ ℚ) ∧
    Coideal.coreComap (Coalgebra.counitCoalgHom ℚ C) (⊥ : Coideal ℚ ℚ) = counitKernel := by
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
  refine ⟨hfixed, ?_, hx_ne, ?_, htop_ne_bot, htop_proper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · apply le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (Coideal.mem_map _ _).mp hy
    exact Coideal.mem_bot.mpr ((mem_counitKernel x).mp hx)
  · rw [Coideal.coreComap_eq_core]
    have hpre : (⊥ : Coideal ℚ ℚ).toSubmodule.comap
        (Coalgebra.counitCoalgHom ℚ C : C →ₗ[ℚ] ℚ) = counitKernel.toSubmodule := by
      apply Submodule.ext
      intro x
      simp only [Submodule.mem_comap, Coideal.toSubmodule_bot, Submodule.mem_bot,
        CoalgHom.coe_toLinearMap, Coalgebra.counitCoalgHom_apply,
        Coideal.mem_toSubmodule, mem_counitKernel]
    rw [hpre]
    exact hfixed

end CoidealExamples

namespace CoidealExamples.ModFour

private abbrev R := ZMod 4
private abbrev C := ℕ →₀ R

private noncomputable def delta (n : ℕ) : C := Finsupp.single n 1

private noncomputable def predecessor : C →ₗc[R] C where
  toLinearMap := Finsupp.lmapDomain R R Nat.pred
  counit_comp := by
    apply Finsupp.lhom_ext
    intro n r
    simp
  map_comp_comul := by
    apply Finsupp.lhom_ext
    intro n r
    simp

private theorem predecessor_surjective : Function.Surjective predecessor := by
  change Function.Surjective (Finsupp.mapDomain Nat.pred : C → C)
  exact Finsupp.mapDomain_surjective (fun n => ⟨n + 1, rfl⟩)

private noncomputable def counitKernel : Coideal R C :=
  Coideal.ofSubmodule
    (Coalgebra.counitCoalgHom R C : C →ₗ[R] R).ker
    (CoalgHomClass.ker_isCoideal_of_surjective (Coalgebra.counitCoalgHom R C)
      (fun r => ⟨Finsupp.single 0 r, by simp⟩))

private theorem mem_counitKernel (x : C) :
    x ∈ counitKernel ↔ Coalgebra.counit (R := R) x = 0 := by
  simp only [counitKernel, Coideal.mem_ofSubmodule, LinearMap.mem_ker,
    CoalgHom.coe_toLinearMap, Coalgebra.counitCoalgHom_apply]

/-- The predecessor map on the group-like coalgebra over `ZMod 4` has two distinct
kernel-containing coideals. The correspondence sends its ordinary kernel to bottom
and its counit kernel to the nonzero counit kernel. A nonzero element of the first
input is annihilated by `2`, and the second input is proper as an ambient submodule. -/
example :
    ∃ I₀ I₁ : {I : Coideal R C // (predecessor : C →ₗ[R] C).ker ≤ I.toSubmodule},
      I₀.1 = Coideal.coreComap predecessor (⊥ : Coideal R C) ∧
      I₁.1 = counitKernel ∧
      I₀ ≠ I₁ ∧
      Coideal.orderIsoMapCoreComapOfSurjective predecessor predecessor_surjective I₀ = ⊥ ∧
      Coideal.orderIsoMapCoreComapOfSurjective predecessor predecessor_surjective I₁ =
        counitKernel ∧
      (2 : R) • (delta 1 - delta 0) ∈ I₀.1 ∧
      (2 : R) • (delta 1 - delta 0) ≠ 0 ∧
      (2 : R) • ((2 : R) • (delta 1 - delta 0)) = 0 ∧
      counitKernel ≠ ⊥ ∧
      counitKernel.toSubmodule ≠ ⊤ := by
  let K := Coideal.coreComap predecessor (⊥ : Coideal R C)
  have hK : K.toSubmodule = (predecessor : C →ₗ[R] C).ker := by
    simpa only [Coideal.toSubmodule_bot, Submodule.comap_bot] using
      Coideal.toSubmodule_coreComap_of_surjective predecessor predecessor_surjective
        (⊥ : Coideal R C)
  have hle : (predecessor : C →ₗ[R] C).ker ≤ counitKernel.toSubmodule := by
    intro x hx
    apply (Coideal.mem_iff _).mp
    apply (mem_counitKernel x).mpr
    have hpx : predecessor x = 0 := LinearMap.mem_ker.mp hx
    rw [← CoalgHomClass.counit_comp_apply predecessor x, hpx, map_zero]
  have hmap : Coideal.map predecessor counitKernel = counitKernel := by
    apply Coideal.ext
    intro y
    rw [Coideal.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (mem_counitKernel _).mpr
      simpa only [CoalgHomClass.counit_comp_apply] using (mem_counitKernel x).mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := predecessor_surjective y
      refine ⟨x, ?_, rfl⟩
      apply (mem_counitKernel x).mpr
      simpa only [CoalgHomClass.counit_comp_apply] using (mem_counitKernel _).mp hy
  have hu : delta 1 - delta 0 ∈ counitKernel := by
    rw [mem_counitKernel]
    simp [delta]
  have hu_ne : delta 1 - delta 0 ≠ (0 : C) := by
    intro h
    have hcoeff := congrArg (fun z : C => z 1) h
    norm_num [delta, Finsupp.single_apply, ZMod.one_eq_zero_iff] at hcoeff
  have hnonzero : counitKernel ≠ ⊥ := by
    intro h
    have hz := hu
    rw [h, Coideal.mem_bot] at hz
    exact hu_ne hz
  have hproper : counitKernel.toSubmodule ≠ ⊤ := by
    have hzero : delta 0 ∉ counitKernel := by
      rw [mem_counitKernel]
      norm_num [delta, ZMod.one_eq_zero_iff]
    intro h
    apply hzero
    apply (Coideal.mem_iff _).mpr
    simp only [h, Submodule.mem_top]
  have hwK : (2 : R) • (delta 1 - delta 0) ∈ K := by
    apply (Coideal.mem_iff _).mpr
    rw [hK, LinearMap.mem_ker]
    rw [LinearMap.map_smul, map_sub]
    simp [predecessor, delta]
  have hw_ne : (2 : R) • (delta 1 - delta 0) ≠ (0 : C) := by
    intro h
    have hcoeff := congrArg (fun z : C => z 1) h
    have htwo : (2 : R) ≠ 0 := by decide
    apply htwo
    simpa [delta, Finsupp.single_apply, smul_eq_mul] using hcoeff
  have hw_annihilated : (2 : R) • ((2 : R) • (delta 1 - delta 0)) = (0 : C) := by
    rw [← mul_smul]
    have hfour : (2 : R) * 2 = 0 := by decide
    rw [hfour, zero_smul]
  let I₀ : {I : Coideal R C // (predecessor : C →ₗ[R] C).ker ≤ I.toSubmodule} :=
    ⟨K, le_of_eq hK.symm⟩
  let I₁ : {I : Coideal R C // (predecessor : C →ₗ[R] C).ker ≤ I.toSubmodule} :=
    ⟨counitKernel, hle⟩
  have hzero :
      Coideal.orderIsoMapCoreComapOfSurjective predecessor predecessor_surjective I₀ = ⊥ := by
    rw [Coideal.orderIsoMapCoreComapOfSurjective_apply]
    exact Coideal.map_coreComap_of_surjective predecessor predecessor_surjective ⊥
  have hone :
      Coideal.orderIsoMapCoreComapOfSurjective predecessor predecessor_surjective I₁ =
        counitKernel := by
    rw [Coideal.orderIsoMapCoreComapOfSurjective_apply]
    exact hmap
  have hdistinct : I₀ ≠ I₁ := by
    intro h
    have heq := congrArg
      (Coideal.orderIsoMapCoreComapOfSurjective predecessor predecessor_surjective) h
    rw [hzero, hone] at heq
    exact hnonzero heq.symm
  exact ⟨I₀, I₁, rfl, rfl, hdistinct, hzero, hone, hwK, hw_ne, hw_annihilated,
    hnonzero, hproper⟩

end CoidealExamples.ModFour
