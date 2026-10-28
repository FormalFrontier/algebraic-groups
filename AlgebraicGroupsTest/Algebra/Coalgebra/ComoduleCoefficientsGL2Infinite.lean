/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing.Dimension

/-!
# Infinite dimension of the rational general linear coordinate coalgebra

The determinant-localized coordinate algebra of `GL₂` over `ℚ` is not finite
as a `ℚ`-module. The powers of the upper-left entry of the universal matrix
form a countably infinite linearly independent family. These specialize the
general dimension results for the coordinate algebra, with its existing
Hopf and coalgebra structures; no alternative coalgebra is defined.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8: the determinant
  localization giving the coordinate algebra of the general linear group.
* `GeneralLinearCoordinateRing.Dimension` supplies the entry-powers and
  module-dimension results.
-/

@[expose] public section

namespace GeneralLinearCoordinateRing

/-- The powers of the upper-left coordinate in the determinant localization of
`GL₂` over `ℚ` are linearly independent. -/
theorem linearIndependent_matrix_zero_zero_powers :
    LinearIndependent ℚ (fun k : ℕ ↦
      TauCeti.GeneralLinear.reindexedGenericMatrix ℚ (Fin 2) 0 0 ^ k) :=
  linearIndependent_matrix_entry_powers ℚ (Fin 2) 0 0

/-- The coordinate coalgebra of `GL₂` over `ℚ` is infinite-dimensional as a
`ℚ`-vector space, not merely infinite as a set. -/
theorem not_finite_fin_two : ¬ Module.Finite ℚ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℚ 2) :=
  not_finite ℚ (Fin 2)

end GeneralLinearCoordinateRing
