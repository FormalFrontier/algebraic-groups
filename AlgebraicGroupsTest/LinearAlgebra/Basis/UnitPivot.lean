/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.Basis.Semilocal
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Unit-pivot basis replacement

The standard integer basis of `ℕ →₀ ℤ` can be changed at zero to `δ₀ + δ₁`.
The resulting basis is the image under a transvection, with inverse coordinates
`v ↦ v - v 0 • δ₁`. A finite specialization agrees with `Basis.ofEquivFun`.
Both finite selection results apply to the real-coordinate plane in `ℂ²`.

## References

Mathlib's `LinearEquiv.transvection`, `Finsupp.basisSingleOne` and
`Basis.ofEquivFun` supply the comparison constructions and their characteristic API.
-/

public section

noncomputable section

open Module

namespace Basis

private abbrev integerBasis : Basis ℕ ℤ (ℕ →₀ ℤ) := Finsupp.basisSingleOne

private def replacement : ℕ →₀ ℤ := Finsupp.single 0 1 + Finsupp.single 1 1

private theorem replacement_unit : IsUnit (integerBasis.repr replacement 0) := by
  simp [integerBasis, replacement]

private def shearedBasis : Basis ℕ ℤ (ℕ →₀ ℤ) :=
  integerBasis.update 0 replacement replacement_unit

private def shear : (ℕ →₀ ℤ) ≃ₗ[ℤ] (ℕ →₀ ℤ) :=
  LinearEquiv.transvection (f := integerBasis.coord 0) (v := integerBasis 1)
    (by simp [Basis.coord_apply])

private theorem shear_apply (v : ℕ →₀ ℤ) :
    shear v = v + v 0 • Finsupp.single 1 1 := by
  simp [shear, LinearMap.transvection.apply, integerBasis]

private theorem shearedBasis_eq_map : shearedBasis = integerBasis.map shear := by
  apply DFunLike.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [shearedBasis, replacement, shear_apply, integerBasis]
  · simp [shearedBasis, Basis.update_apply, shear_apply, integerBasis, hn, Ne.symm hn]

private theorem shearedBasis_repr (v : ℕ →₀ ℤ) :
    shearedBasis.repr v = v - v 0 • Finsupp.single 1 1 := by
  rw [shearedBasis_eq_map, Basis.map_repr]
  simp [shear, LinearEquiv.transvection.symm_eq, LinearMap.transvection.apply,
    Basis.coord_apply, integerBasis, sub_eq_add_neg]

private theorem shearedBasis_repr_zero (v : ℕ →₀ ℤ) :
    shearedBasis.repr v 0 = v 0 := by
  rw [shearedBasis_repr]
  simp

private theorem shearedBasis_repr_one (v : ℕ →₀ ℤ) :
    shearedBasis.repr v 1 = v 1 - v 0 := by
  rw [shearedBasis_repr]
  simp

private theorem shearedBasis_repr_other (v : ℕ →₀ ℤ) (n : ℕ) (hn : n ≠ 1) :
    shearedBasis.repr v n = v n := by
  rw [shearedBasis_repr]
  simp [hn]

private theorem shearedBasis_recovers_zero :
    Finsupp.single 0 (1 : ℤ) = shearedBasis 0 - shearedBasis 1 := by
  simp [shearedBasis, Basis.update_apply, integerBasis, replacement]

private theorem shearedBasis_ne : shearedBasis ≠ integerBasis := by
  intro h
  have hcoord := congrArg (fun b : Basis ℕ ℤ (ℕ →₀ ℤ) ↦ b 0 1) h
  simp [shearedBasis, integerBasis, replacement] at hcoord

private abbrev finiteBasis : Basis (Fin 2) ℤ (Fin 2 → ℤ) := Pi.basisFun ℤ (Fin 2)

private def finiteShear : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  LinearEquiv.transvection (f := finiteBasis.coord 0) (v := finiteBasis 1)
    (by simp [Basis.coord_apply])

private theorem finitePivot_unit : IsUnit (finiteBasis.repr (finiteBasis 0 + finiteBasis 1) 0) := by
  simp

private theorem finite_constructor_agreement :
    finiteBasis.update 0 (finiteBasis 0 + finiteBasis 1) finitePivot_unit =
      Basis.ofEquivFun finiteShear.symm := by
  apply DFunLike.ext
  intro n
  simp only [Basis.update_apply, Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  by_cases hn : n = 0
  · subst n
    simp [finiteShear, LinearMap.transvection.apply, finiteBasis]
  · simp [finiteShear, LinearMap.transvection.apply, finiteBasis, hn]

private def realPlane : Submodule ℝ (Fin 2 → ℂ) where
  carrier := {v | ∀ i, (v i).im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i
    simp [hv i, hw i]
  smul_mem' := by
    intro r v hv i
    simp [hv i]

private theorem realPlane_basis_mem (i : Fin 2) : Pi.basisFun ℂ (Fin 2) i ∈ realPlane := by
  intro j
  by_cases h : j = i
  · subst j
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

private theorem realPlane_span : Submodule.span ℂ (realPlane : Set (Fin 2 → ℂ)) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun ℂ (Fin 2))).2
  intro i
  exact Submodule.subset_span (realPlane_basis_mem i)

private theorem realPlane_proper : realPlane ≠ ⊤ := by
  intro h
  have hv : (fun _ : Fin 2 ↦ Complex.I) ∈ realPlane := by
    rw [h]
    exact Submodule.mem_top
  have hi := hv 0
  simp at hi

private theorem finite_field_selection :
    ∃ b : Basis (Fin 2) ℂ (Fin 2 → ℂ), ∀ i, b i ∈ realPlane :=
  (Pi.basisFun ℂ (Fin 2)).exists_basis_subset realPlane realPlane_span

private theorem finite_local_selection :
    ∃ b : Basis (Fin 2) ℂ (Fin 2 → ℂ), ∀ i, b i ∈ realPlane := by
  let _ : Infinite (IsLocalRing.ResidueField ℝ) :=
    Infinite.of_injective (IsLocalRing.residue ℝ) (IsLocalRing.residue ℝ).injective
  apply (Pi.basisFun ℂ (Fin 2)).exists_basis_subset_of_le_jacobson realPlane realPlane_span
  simp only [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  exact bot_le

/- A separate infinite-index boundary with pivot unit -1, rather than a shear. -/
private def negativeReplacement : ℕ →₀ ℤ := -Finsupp.single 0 1 + Finsupp.single 1 1

private theorem negativeReplacement_unit : IsUnit (integerBasis.repr negativeReplacement 0) := by
  simp [integerBasis, negativeReplacement]

private def negativePivotBasis : Basis ℕ ℤ (ℕ →₀ ℤ) :=
  integerBasis.update 0 negativeReplacement negativeReplacement_unit

private theorem negativePivot_inverse : (↑(negativeReplacement_unit.unit⁻¹) : ℤ) = -1 := by
  have hmul : (↑(negativeReplacement_unit.unit⁻¹) : ℤ) * (-1) = 1 := by
    simp [integerBasis, negativeReplacement]
  simpa using congrArg (fun z : ℤ ↦ -z) hmul

private theorem negativePivotBasis_zero :
    negativePivotBasis 0 = -Finsupp.single 0 1 + Finsupp.single 1 1 := by
  simp [negativePivotBasis, negativeReplacement]

private theorem negativePivotBasis_repr_zero (v : ℕ →₀ ℤ) :
    negativePivotBasis.repr v 0 = -v 0 := by
  simpa [negativePivotBasis, negativePivot_inverse, integerBasis, negativeReplacement] using
    integerBasis.repr_update_same 0 negativeReplacement v negativeReplacement_unit

private theorem negativePivotBasis_repr_one (v : ℕ →₀ ℤ) :
    negativePivotBasis.repr v 1 = v 1 + v 0 := by
  simpa [negativePivotBasis, negativePivot_inverse, integerBasis, negativeReplacement] using
    integerBasis.repr_update_of_ne 0 negativeReplacement v negativeReplacement_unit 1 (by decide)

private theorem negativePivotBasis_repr_other (v : ℕ →₀ ℤ) (n : ℕ)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) : negativePivotBasis.repr v n = v n := by
  simpa [negativePivotBasis, negativePivot_inverse, integerBasis, negativeReplacement,
    hn0, hn1, Ne.symm hn0, Ne.symm hn1] using
    integerBasis.repr_update_of_ne 0 negativeReplacement v negativeReplacement_unit n hn0

private theorem negativePivotBasis_recovers_zero :
    Finsupp.single 0 (1 : ℤ) = -negativePivotBasis 0 + negativePivotBasis 1 := by
  apply negativePivotBasis.repr.injective
  ext n
  simp only [map_add, map_neg, Finsupp.add_apply, Finsupp.neg_apply, Basis.repr_self]
  by_cases hn0 : n = 0
  · subst n
    rw [negativePivotBasis_repr_zero]
    simp
  · by_cases hn1 : n = 1
    · subst n
      rw [negativePivotBasis_repr_one]
      simp
    · rw [negativePivotBasis_repr_other _ n hn0 hn1]
      simp [hn0, hn1]

end Basis
