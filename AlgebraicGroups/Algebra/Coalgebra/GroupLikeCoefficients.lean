/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.Coalgebra.GroupLikeCoordinates
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Group-like elements and monoid-algebra coefficients

The standard basis identifies the coordinates of `MonoidAlgebra R M` with its coefficients.
The basis-coordinate criterion for group-like elements therefore says that these coefficients
have pairwise zero products and finite-support sum one. The index type `M` is arbitrary:
neither the standard basis nor the canonical coalgebra requires a monoid structure on it.

Over a commutative domain, the coefficient condition agrees with Mathlib's classification of
group-like elements as the elements `MonoidAlgebra.single i 1`.

## References

The constructions and proofs use Mathlib's standard monoid-algebra basis and canonical
coalgebra. The basis-coordinate criterion uses Mathlib's orthogonal-idempotent API, and the
domain corollary reuses `MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {R : Type u} {M : Type v}

section Semiring

variable [Semiring R]

/-- The coordinate representation in Mathlib's standard monoid-algebra basis is the
coefficient finitely supported function. -/
@[simp]
theorem basis_repr (x : MonoidAlgebra R M) :
    (MonoidAlgebra.basis M R).repr x = x.coeff :=
  rfl

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- The basis-coordinate group-like criterion specializes to pairwise zero products of
coefficients and finite-support coefficient sum one, without a monoid structure on `M`. -/
theorem isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one
    (x : MonoidAlgebra R M) :
    IsGroupLikeElem R x ↔
      Pairwise (fun i j ↦ x.coeff i * x.coeff j = 0) ∧
        x.coeff.sum (fun _ r ↦ r) = 1 := by
  have hb : ∀ i, IsGroupLikeElem R (MonoidAlgebra.basis M R i) := by
    intro i
    simpa only [MonoidAlgebra.basis_apply] using
      (MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) i)
  simpa only [basis_repr] using
    (Module.Basis.isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one
      (MonoidAlgebra.basis M R) hb x)

end CommSemiring

section CommRing

variable [CommRing R] [IsDomain R]

/-- Over a commutative domain, the coefficient condition agrees with Mathlib's
classification of group-like elements as single basis elements with coefficient one. -/
theorem pairwise_mul_eq_zero_sum_eq_one_iff_mem_range_single_one
    (x : MonoidAlgebra R M) :
    (Pairwise (fun i j ↦ x.coeff i * x.coeff j = 0) ∧
      x.coeff.sum (fun _ r ↦ r) = 1) ↔
        x ∈ Set.range (MonoidAlgebra.single · 1) :=
  (isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one x).symm.trans
    (isGroupLikeElem_iff_mem_range_single_one (x := x))

end CommRing

end MonoidAlgebra
