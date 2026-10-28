/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Order

/-!
# The superdiagonal central filtration of a unitriangular group

For a commutative ring `R`, the group `Matrix.UnitriangularGroup (Fin n) R` has a
descending normal filtration by the vanishing of its first superdiagonals.
Products of matrices supported above superdiagonals `r` and `s` are supported
above superdiagonal `r + s`; this gives a central series and a nilpotency-class
bound even for the zero ring and empty index type.

Milne proves unitriangular algebraic-group nilpotence using a central series;
passing to point groups gives nilpotence in his field-based setting. This
module instead constructs a coarser whole-superdiagonal filtration over any
commutative ring, including the zero ring and `Fin 0`, without asserting a
group-scheme correspondence. The group, coefficient map and general-linear
matrix operations come from
`AlgebraicGroups.GroupScheme.Unitriangular` and Mathlib.

## References

- J. S. Milne, *Algebraic Groups* (2017), Definition 6.34, Remark 6.35,
  Example 6.36 and §6.49 (unitriangular algebraic-group nilpotence via a
  central series, a field-based point-group antecedent).
- Mathlib contributors, `Mathlib.GroupTheory.Nilpotent` (descending and lower
  central series, nilpotency class) and `Mathlib.GroupTheory.Commutator.Basic`
  (subgroup commutators).
-/

public section

open scoped commutatorElement

namespace TauCeti.UpperUnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- The stage numbered zero is also the whole group. -/
@[simp]
theorem superdiagonalSubgroup_zero : superdiagonalSubgroup (n := n) (R := R) 0 = ⊤ := by
  apply top_unique
  rw [← superdiagonalSubgroup_one (n := n) (R := R)]
  exact superdiagonalSubgroup_antitone (Nat.zero_le 1)

/-- Each superdiagonal subgroup is normal in the unitriangular point group. -/
instance superdiagonalSubgroup_normal (r : ℕ) :
    (superdiagonalSubgroup (n := n) (R := R) r).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff,
    Subgroup.le_normalizer_iff_commutator_le_left]
  rw [← superdiagonalSubgroup_one (n := n) (R := R)]
  exact (commutator_superdiagonalSubgroup_le r 1).trans
    (superdiagonalSubgroup_antitone (Nat.le_add_right r 1))

/-- The full infinite family satisfies Mathlib's descending-central-series
predicate. Compare Milne, *Algebraic Groups* (2017), Definition 6.34 and
Remark 6.35, for the algebraic-group setting. -/
theorem superdiagonalSubgroup_isDescendingCentralSeries :
    Subgroup.IsDescendingCentralSeries
      (fun t ↦ superdiagonalSubgroup (n := n) (R := R) (t + 1)) := by
  constructor
  · exact superdiagonalSubgroup_one
  · intro x t hx g
    have hg : g ∈ superdiagonalSubgroup (n := n) (R := R) 1 := by simp
    exact (Subgroup.commutator_le.mp
      (commutator_superdiagonalSubgroup_le (t + 1) 1)) x hx g hg

/-- Coefficient homomorphisms preserve every superdiagonal stage pointwise. -/
theorem map_mem_superdiagonalSubgroup {S : Type} [CommRing S]
    (f : R →+* S) {r : ℕ} {g : TauCeti.upperUnitriangularGroup (Fin n) R}
    (hg : g ∈ superdiagonalSubgroup (n := n) (R := R) r) :
    map f g ∈ superdiagonalSubgroup (n := n) (R := S) r := by
  rw [mem_superdiagonalSubgroup_iff] at hg ⊢
  intro i j hij
  simpa [map_apply, Matrix.one_apply] using congrArg f (hg i j hij)

/-- The coefficient-map group homomorphism maps each stage into its counterpart. -/
theorem superdiagonalSubgroup_map {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) :
    (superdiagonalSubgroup (n := n) (R := R) r).map (map f) ≤
      superdiagonalSubgroup (n := n) (R := S) r := by
  rintro g ⟨x, hx, rfl⟩
  exact map_mem_superdiagonalSubgroup n R f hx

end TauCeti.UpperUnitriangularGroup
