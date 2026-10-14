/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Infinite dimension of general linear coordinate algebras

For a nonempty finite index type, the determinant-localized coordinate algebra
of the general linear group over a field is not finite as a module over that
field. The powers of any entry of the universal matrix form a countably infinite
linearly independent family. This is a statement about vector-space dimension,
not merely the cardinality of the coordinate algebra.

The polynomial-to-localization map is injective because the generic determinant
is nonzero and the matrix-entry polynomial ring is a domain. Independence of
the entry powers then follows from the monomial basis of that polynomial ring.
The nonempty-index hypothesis is necessary: for the empty index type, the
coordinate algebra is the base field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8: the determinant
  localization giving the coordinate algebra of the general linear group.
* Mathlib, `LinearAlgebra/Matrix/MvPolynomial`, `RingTheory/Localization/Defs`,
  `RingTheory/MvPolynomial/Basic`, and `LinearAlgebra/Dimension/Finite`: the
  nonzero generic determinant, localization injection, monomial basis, and the
  obstruction to finite dimension from an infinite independent family.
-/

@[expose] public section

universe u v

namespace GeneralLinearCoordinateRing

variable (K : Type u) [Field K] (n : Type v) [Fintype n] [DecidableEq n]

/-- The powers of any entry of the universal matrix are linearly independent
over the base field, by injection of the polynomial monomial basis into the
determinant localization. -/
theorem linearIndependent_matrix_entry_powers (i j : n) :
    LinearIndependent K (fun k : ℕ ↦ matrix K n i j ^ k) := by
  have hdet : determinant K n ≠ 0 := Matrix.det_mvPolynomialX_ne_zero n K
  have hinj : Function.Injective
      (algebraMap (PolynomialRing K n) (CoordinateRing K n)) :=
    IsLocalization.injective (CoordinateRing K n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hdet)
  have hpolynomial : LinearIndependent K
      (fun k : ℕ ↦ (MvPolynomial.X (i, j) : PolynomialRing K n) ^ k) := by
    simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials,
      ← MvPolynomial.X_pow_eq_monomial] using
      (MvPolynomial.basisMonomials (n × n) K).linearIndependent.comp
        (Finsupp.single (i, j)) (Finsupp.single_injective _)
  let f : PolynomialRing K n →ₐ[K] CoordinateRing K n :=
    IsScalarTower.toAlgHom K (PolynomialRing K n) (CoordinateRing K n)
  have hf : LinearMap.ker f.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  simpa only [f, Function.comp_def, AlgHom.toLinearMap_apply,
    IsScalarTower.toAlgHom_apply, map_pow, matrix_apply] using
    hpolynomial.map' f.toLinearMap hf

/-- For a nonempty finite index type, the general linear coordinate algebra of
Milne's determinant localization in item 2.8 is infinite-dimensional over its
base field. -/
theorem not_finite [Nonempty n] : ¬ Module.Finite K (CoordinateRing K n) := by
  intro h
  let : Module.Finite K (CoordinateRing K n) := h
  obtain ⟨i⟩ := ‹Nonempty n›
  exact (Module.Finite.not_linearIndependent_of_infinite
    (R := K) (fun k : ℕ ↦ matrix K n i i ^ k))
    (linearIndependent_matrix_entry_powers K n i i)

end GeneralLinearCoordinateRing
