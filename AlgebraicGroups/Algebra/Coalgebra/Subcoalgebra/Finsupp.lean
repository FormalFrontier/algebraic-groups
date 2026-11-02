/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Subcoalgebras of finitely supported functions with prescribed support

For any set `s` of indices, `Finsupp.supportedSubcoalgebra K s` is the subcoalgebra of
`ι →₀ K` whose underlying submodule is `Finsupp.supported K K s`. It is spanned by the
unit coordinate vectors indexed by `s`. Its carrier is finitely generated, and its
underlying module is finite, whenever `s` is finite; the construction itself requires
no finiteness assumption.

`Finsupp.supportedSubcoalgebraOrderIso` classifies every subcoalgebra by its unit
coordinate vectors. Its inverse records exactly the indices whose unit vectors lie in
the subcoalgebra. The classification allows arbitrary and empty index types.

The construction extends the two-coordinate construction in
`AlgebraicGroupsTest.Algebra.Coalgebra.SubcoalgebraDiagonal` to arbitrary index types and
supports. It uses `Subcoalgebra.mk'` and the closure of spans of group-like elements from
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan`. The restricted coalgebra and its
inclusion are the canonical ones supplied by `Subcoalgebra`.

## References

The diagonal coalgebra and the unit-coordinate formulas are from Mathlib's
`Mathlib.RingTheory.Coalgebra.Basic`. The carrier, membership and span descriptions use
`Mathlib.LinearAlgebra.Finsupp.Supported`; the finiteness consequences use
`Mathlib.RingTheory.Finiteness.Basic`.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace Finsupp

variable (K : Type u) [Field K] {ι : Type v} (s : Set ι)

/-- The subcoalgebra of the diagonal Finsupp coalgebra consisting of the functions
supported on `s`. -/
def supportedSubcoalgebra : Subcoalgebra K (ι →₀ K) :=
  Subcoalgebra.mk' (supported K K s) <| by
    intro x hx
    rw [supported_eq_span_single] at hx ⊢
    exact Coalgebra.comul_mem_range_mapIncl_span_of_isGroupLikeElem
      (by
        rintro y ⟨i, hi, rfl⟩
        exact {
          counit_eq_one := by simp
          comul_eq_tmul_self := by simp }) hx

/-- The underlying submodule consists exactly of functions supported on `s`. -/
@[simp]
theorem supportedSubcoalgebra_toSubmodule :
    (supportedSubcoalgebra K s).toSubmodule = supported K K s := by
  simp only [supportedSubcoalgebra, Subcoalgebra.toSubmodule_mk']

/-- Membership in the supported subcoalgebra is containment of the finite support in `s`. -/
@[simp]
theorem mem_supportedSubcoalgebra (x : ι →₀ K) :
    x ∈ supportedSubcoalgebra K s ↔ (↑x.support : Set ι) ⊆ s := by
  rw [Subcoalgebra.mem_iff, supportedSubcoalgebra_toSubmodule]
  exact mem_supported K x

/-- The supported subcoalgebra is spanned by its unit coordinate vectors. -/
theorem supportedSubcoalgebra_toSubmodule_eq_span :
    (supportedSubcoalgebra K s).toSubmodule =
      Submodule.span K ((fun i : ι => single i (1 : K)) '' s) := by
  rw [supportedSubcoalgebra_toSubmodule, supported_eq_span_single]

/-- A coordinate vector with any coefficient belongs to the supported subcoalgebra
whenever its index belongs to `s`. -/
theorem single_mem_supportedSubcoalgebra {i : ι} (a : K) (hi : i ∈ s) :
    single i a ∈ supportedSubcoalgebra K s := by
  rw [Subcoalgebra.mem_iff, supportedSubcoalgebra_toSubmodule]
  exact single_mem_supported K a hi

/-- The carrier lies in a submodule exactly when that submodule contains all the unit
coordinate vectors indexed by `s`. -/
theorem supportedSubcoalgebra_toSubmodule_le_iff (T : Submodule K (ι →₀ K)) :
    (supportedSubcoalgebra K s).toSubmodule ≤ T ↔ ∀ i ∈ s, single i (1 : K) ∈ T := by
  rw [supportedSubcoalgebra_toSubmodule_eq_span, Submodule.span_le]
  constructor
  · intro h i hi
    exact h (Set.mem_image_of_mem _ hi)
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

/-- Finite support sets give finitely generated carriers. -/
theorem supportedSubcoalgebra_fg (hs : s.Finite) :
    (supportedSubcoalgebra K s).toSubmodule.FG := by
  rw [supportedSubcoalgebra_toSubmodule_eq_span]
  exact Submodule.fg_span (hs.image _)

/-- The supported subcoalgebra is finite as a module when its support set is finite. -/
theorem supportedSubcoalgebra_finite (hs : s.Finite) :
    Module.Finite K (supportedSubcoalgebra K s) :=
  Module.Finite.iff_fg.mpr (supportedSubcoalgebra_fg K s hs)

variable {K s}

private theorem contract_comul_eq_single (i : ι) :
    (TensorProduct.lid K (ι →₀ K)).toLinearMap ∘ₗ
        (lapply i : (ι →₀ K) →ₗ[K] K).rTensor (ι →₀ K) ∘ₗ
        Coalgebra.comul (R := K) =
      (lsingle i : K →ₗ[K] (ι →₀ K)) ∘ₗ lapply i := by
  classical
  apply Finsupp.lhom_ext
  intro j a
  by_cases h : j = i
  · subst j
    simp
  · simp [Ne.symm h]

private theorem single_mem_of_mem
    (D : Subcoalgebra K (ι →₀ K)) {x : ι →₀ K} (hx : x ∈ D) (i : ι) :
    single i (x i) ∈ D := by
  let c : ((ι →₀ K) ⊗[K] (ι →₀ K)) →ₗ[K] (ι →₀ K) :=
    (TensorProduct.lid K (ι →₀ K)).toLinearMap ∘ₗ
      (lapply i : (ι →₀ K) →ₗ[K] K).rTensor (ι →₀ K)
  have hclosed : ∀ t : D.toSubmodule ⊗[K] D.toSubmodule,
      c (TensorProduct.mapIncl D.toSubmodule D.toSubmodule t) ∈ D := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
        change (TensorProduct.lid K (ι →₀ K))
          ((lapply i : (ι →₀ K) →ₗ[K] K).rTensor (ι →₀ K)
            (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype
              (u ⊗ₜ[K] v))) ∈ D
        rw [TensorProduct.map_tmul, LinearMap.rTensor_tmul,
          TensorProduct.lid_tmul]
        simpa only [lapply_apply, Submodule.subtype_apply] using
          D.smul_mem ((u : ι →₀ K) i) v.property
    | add t u iht ihu =>
        simpa only [map_add] using D.add_mem iht ihu
  obtain ⟨t, ht⟩ := D.comul_mem hx
  have hct := hclosed t
  rw [ht] at hct
  have hc := LinearMap.congr_fun (contract_comul_eq_single (K := K) i) x
  change c (Coalgebra.comul (R := K) x) = single i (x i) at hc
  simpa only [hc] using hct

private theorem single_one_mem_of_mem
    (D : Subcoalgebra K (ι →₀ K)) {x : ι →₀ K} (hx : x ∈ D)
    {i : ι} (hxi : x i ≠ 0) : single i (1 : K) ∈ D := by
  have h := D.smul_mem (x i)⁻¹ (single_mem_of_mem D hx i)
  simpa only [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hxi] using h

private theorem single_one_mem_supportedSubcoalgebra (s : Set ι) (i : ι) :
    single i (1 : K) ∈ supportedSubcoalgebra K s ↔ i ∈ s := by
  rw [Subcoalgebra.mem_iff, supportedSubcoalgebra_toSubmodule_eq_span]
  exact Finsupp.single_mem_span_single (R := K)

private theorem supportedSubcoalgebra_unitCoordinates
    (D : Subcoalgebra K (ι →₀ K)) :
    supportedSubcoalgebra K {i | single i (1 : K) ∈ D} = D := by
  apply le_antisymm
  · change (supportedSubcoalgebra K _).toSubmodule ≤ D.toSubmodule
    exact (supportedSubcoalgebra_toSubmodule_le_iff K _ D.toSubmodule).mpr
      (fun i hi => hi)
  · intro x hx
    rw [mem_supportedSubcoalgebra]
    intro i hi
    exact single_one_mem_of_mem D hx (Finsupp.mem_support_iff.mp hi)

/-- Subcoalgebras of the diagonal coalgebra of finitely supported functions correspond
in order to subsets of its unit coordinate basis. -/
noncomputable def supportedSubcoalgebraOrderIso
    (K : Type u) [Field K] (ι : Type v) :
    Set ι ≃o Subcoalgebra K (ι →₀ K) where
  toFun := supportedSubcoalgebra K
  invFun := fun D => {i | single i (1 : K) ∈ D}
  left_inv s := by
    ext i
    exact single_one_mem_supportedSubcoalgebra s i
  right_inv D := by exact supportedSubcoalgebra_unitCoordinates D
  map_rel_iff' := by
    intro s t
    constructor
    · intro h i hi
      exact (single_one_mem_supportedSubcoalgebra t i).mp
        (h (single_mem_supportedSubcoalgebra K s (1 : K) hi))
    · intro h x hx
      exact (mem_supportedSubcoalgebra K t x).mpr
        (fun i hi => h ((mem_supportedSubcoalgebra K s x).mp hx hi))

/-- The forward classification is the supported subcoalgebra. -/
@[simp] theorem supportedSubcoalgebraOrderIso_apply
    (K : Type u) [Field K] (ι : Type v) (s : Set ι) :
    supportedSubcoalgebraOrderIso K ι s = supportedSubcoalgebra K s := rfl

/-- The inverse classification records membership of unit coordinate vectors. -/
@[simp] theorem supportedSubcoalgebraOrderIso_symm_apply
    (K : Type u) [Field K] (ι : Type v) (D : Subcoalgebra K (ι →₀ K)) :
    (supportedSubcoalgebraOrderIso K ι).symm D =
      {i | single i (1 : K) ∈ D} := rfl

end Finsupp
