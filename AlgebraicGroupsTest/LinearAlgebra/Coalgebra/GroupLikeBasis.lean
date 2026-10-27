/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Defs

import AlgebraicGroups.LinearAlgebra.Coalgebra.GroupLikeBasis
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.DualNumber
import Mathlib.Topology.Connected.Clopen

/-!
# A group-like basis over field dual numbers

The canonical monoid-algebra coalgebra over `DualNumber K`, for a field `K`, has
its standard basis indexed by the infinite type `ℕ`. Its scalar ring is local
and has nonzero nilpotent epsilon, so it is not a domain. All prime ideals
specialize to the local ring's closed point, giving a preconnected spectrum.
The group-like basis classification specializes to this coalgebra.

## References

The scalar ring and its local structure are from
`Mathlib.RingTheory.DualNumber`; the coalgebra, basis, and group-likeness of its
single-one vectors are from Mathlib's monoid-algebra modules. The local spectrum
uses `IsLocalRing.specializes_closedPoint` from
`Mathlib.RingTheory.Spectrum.Prime.Topology`.
-/

@[expose] public section

noncomputable section

universe u

variable (K : Type u) [Field K]

private theorem dualNumber_eps_ne_zero :
    (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro h
  have hsnd := congrArg (TrivSqZeroExt.snd : DualNumber K → K) h
  exact one_ne_zero (by simpa only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] using hsnd)

private theorem dualNumber_spectrum_preconnected :
    PreconnectedSpace (PrimeSpectrum (DualNumber K)) := by
  classical
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  by_cases h : IsLocalRing.closedPoint (DualNumber K) ∈ s
  · right
    apply Set.eq_univ_of_forall
    intro x
    exact (IsLocalRing.specializes_closedPoint x).mem_open hs.2 h
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h ((IsLocalRing.specializes_closedPoint x).mem_closed hs.1 hx)

private theorem dualNumber_groupLike_basis :
    ¬ IsDomain (DualNumber K) ∧
      ∀ (x : MonoidAlgebra (DualNumber K) ℕ),
        IsGroupLikeElem (DualNumber K) x →
          ∃! i : ℕ, x = MonoidAlgebra.basis ℕ (DualNumber K) i := by
  constructor
  · intro h
    let : IsDomain (DualNumber K) := h
    exact dualNumber_eps_ne_zero K (DualNumber.isNilpotent_eps (R := K)).eq_zero
  · intro x hx
    let : PreconnectedSpace (PrimeSpectrum (DualNumber K)) :=
      dualNumber_spectrum_preconnected K
    exact (MonoidAlgebra.basis ℕ (DualNumber K)).existsUnique_eq_of_isGroupLikeElem
      (fun i ↦ by
        rw [MonoidAlgebra.basis_apply]
        exact MonoidAlgebra.isGroupLikeElem_single_one
          (R := DualNumber K) (A := DualNumber K) i)
      x hx
