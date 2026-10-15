/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.NormNum

/-!
# Coordinates in an infinite-dimensional diagonal coalgebra

The coalgebra `ℤ →₀ ℚ` has normalized group-like points `single i 1`. Its
canonical Finsupp basis spans the whole coalgebra, although the ambient module
is not finite-dimensional. No multiplication on the coalgebra is used.

For the vector `v = 2 • single 0 1 + 3 • single 1 1`, the canonical basis
coordinates are `2` at `0`, `3` at `1`, and zero elsewhere. Reconstruction from
these finitely supported coordinates returns `v`. Its counit is `5`, while its
comultiplication is the corresponding diagonal sum, so `v` is not normalized
group-like.

## References

* Mathlib's `Mathlib.RingTheory.Coalgebra.Basic`, by Ali Ramsey and Eric Wieser,
  provides the lawful Finsupp coalgebra and the formulas for a single term.
* Mathlib's `Mathlib.RingTheory.Coalgebra.GroupLike`, by Yaël Dillies and
  Michał Mrugała, provides the normalized predicate and bundled points.
* Mathlib's `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, by Johannes Hölzl,
  provides `Finsupp.basisSingleOne`. Reconstruction and spanning use Mathlib's
  basis API; non-finiteness uses `Module.not_finite_of_infinite_basis` from
  `Mathlib.RingTheory.Finiteness.Cardinality`, by Johan Commelin.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Coalgebra.FinsuppCoordinates

local notation "C∞" => ℤ →₀ ℚ

/-- The normalized coordinate point at an integer index. -/
def point (i : ℤ) : GroupLike ℚ C∞ where
  val := Finsupp.single i 1
  isGroupLikeElem_val := {
    counit_eq_one := by
      simp only [Finsupp.counit_single, CommSemiring.counit_apply]
    comul_eq_tmul_self := by
      simp only [Finsupp.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, Finsupp.lsingle_apply] }

/-- A coordinate point has the specified single nonzero coefficient. -/
@[simp] theorem point_val (i : ℤ) : (point i).val = Finsupp.single i 1 := rfl

/-- Every coordinate point has counit one. -/
@[simp] theorem point_counit (i : ℤ) : counit (R := ℚ) (point i).val = 1 :=
  (point i).isGroupLikeElem_val.counit_eq_one

/-- Comultiplication is diagonal on each coordinate point. -/
@[simp] theorem point_comul (i : ℤ) :
    comul (R := ℚ) (point i).val = (point i).val ⊗ₜ[ℚ] (point i).val :=
  (point i).isGroupLikeElem_val.comul_eq_tmul_self

local notation "δ₀" => GroupLike.val (point 0)
local notation "δ₁" => GroupLike.val (point 1)

/-- The normalized points at zero and one are distinct, as seen at coefficient zero. -/
theorem point_zero_val_ne_point_one_val : δ₀ ≠ δ₁ := by
  intro h
  have hc := congrArg (fun f : C∞ ↦ f 0) h
  norm_num [point_val, Finsupp.single_apply] at hc

/-- A vector with two nonzero rational coordinates. -/
def vector : C∞ := (2 : ℚ) • δ₀ + (3 : ℚ) • δ₁

/-- The scalar multiples in `vector` give coefficients two and three. -/
theorem vector_eq_single_add :
    vector = Finsupp.single 0 2 + Finsupp.single 1 3 := by
  simp only [vector, point_val, Finsupp.smul_single_one]

/-- The coefficient at zero is two. -/
@[simp] theorem vector_apply_zero : vector 0 = 2 := by
  norm_num [vector_eq_single_add, Finsupp.single_apply]

/-- The coefficient at one is three. -/
@[simp] theorem vector_apply_one : vector 1 = 3 := by
  norm_num [vector_eq_single_add, Finsupp.single_apply]

/-- All coefficients away from zero and one vanish. -/
theorem vector_apply_of_ne (i : ℤ) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : vector i = 0 := by
  simp [vector_eq_single_add, Ne.symm hi0, Ne.symm hi1]

/-- Both displayed coefficients are nonzero, so the support is exactly `{0, 1}`. -/
theorem vector_support : vector.support = {0, 1} := by
  ext i
  by_cases hi0 : i = 0
  · subst i
    norm_num [Finsupp.mem_support_iff]
  · by_cases hi1 : i = 1
    · subst i
      norm_num [Finsupp.mem_support_iff]
    · simp [Finsupp.mem_support_iff, vector_apply_of_ne i hi0 hi1, hi0, hi1]

/-- The counit adds the two coordinates, giving five. -/
@[simp] theorem vector_counit : counit (R := ℚ) vector = 5 := by
  norm_num [vector, map_add, map_smul]

/-- Comultiplication has the two diagonal terms, with their original coefficients. -/
theorem vector_comul :
    comul (R := ℚ) vector =
      (2 : ℚ) • (δ₀ ⊗ₜ[ℚ] δ₀) + (3 : ℚ) • (δ₁ ⊗ₜ[ℚ] δ₁) := by
  simp only [vector, map_add, map_smul, point_comul]

/-- The vector fails the normalization condition for a group-like element. -/
theorem vector_not_isGroupLikeElem : ¬ IsGroupLikeElem ℚ vector := by
  intro hv
  have h := hv.counit_eq_one
  rw [vector_counit] at h
  norm_num at h

/-- The canonical Finsupp basis records precisely the two nonzero coordinates. -/
theorem vector_repr :
    (Finsupp.basisSingleOne : Module.Basis ℤ ℚ C∞).repr vector =
      Finsupp.single 0 2 + Finsupp.single 1 3 := by
  change vector = _
  exact vector_eq_single_add

/-- Reconstructing from the explicitly computed finite coordinates returns the vector. -/
theorem vector_reconstruction :
    Finsupp.linearCombination ℚ (Finsupp.basisSingleOne : Module.Basis ℤ ℚ C∞)
      (Finsupp.single 0 2 + Finsupp.single 1 3) = vector := by
  rw [← vector_repr]
  exact Module.Basis.linearCombination_repr _ _

/-- The normalized coordinate points span the whole coalgebra. -/
theorem span_point_eq_top :
    Submodule.span ℚ (Set.range fun i : ℤ ↦ (point i).val) = ⊤ := by
  simpa only [point_val, Finsupp.coe_basisSingleOne] using
    (Finsupp.basisSingleOne : Module.Basis ℤ ℚ C∞).span_eq

/-- The integer-indexed canonical basis rules out a finite-dimensional ambient module. -/
theorem not_module_finite : ¬ Module.Finite ℚ C∞ :=
  Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne : Module.Basis ℤ ℚ C∞)

end Coalgebra.FinsuppCoordinates
