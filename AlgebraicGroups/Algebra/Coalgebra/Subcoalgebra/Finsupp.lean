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

end Finsupp
