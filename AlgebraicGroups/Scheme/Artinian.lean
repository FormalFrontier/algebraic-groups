/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite morphisms from zero-dimensional schemes

This file packages the standard passage from a zero-dimensional finite-type
scheme over a locally Artinian base to a finite morphism.

## References

- J. S. Milne, *Algebraic Groups*, Proposition 11.2, for the finite-over-a-field
  special case among its equivalent conditions on zero-dimensional algebraic schemes.
- Mathlib's `IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
  `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`, and
  `IsFinite.of_locallyQuasiFinite` give the locally Artinian and quasi-finite steps.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A quasi-compact, locally finite-type morphism to a locally Artinian scheme
is finite if its source has topological Krull dimension at most zero. Over a field,
this is one direction of Milne, *Algebraic Groups*, Proposition 11.2; the other
equivalences in that proposition are not asserted here. -/
lemma IsFinite.of_topologicalKrullDim_le_zero (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyArtinian Y]
    (hX : topologicalKrullDim X ≤ 0) : IsFinite f := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hX
  let _ : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ ↦
      DiscreteTopology.isDiscrete
  exact .of_locallyQuasiFinite f

end AlgebraicGeometry
