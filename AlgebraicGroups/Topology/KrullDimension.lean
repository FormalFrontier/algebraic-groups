/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import MinimalPrimes.Topology.KrullDimension.OpenCover

/-!
# Topological Krull dimension and open covers

This file specializes the open-cover formula for topological Krull dimension
from `MinimalPrimes.Topology.KrullDimension.OpenCover` to the connected components
of a locally connected space. It also gives a Jacobson-space discreteness
criterion and a quotient-space dimension bound.

The cover result holds for arbitrary spaces, without Noetherian, separation or
finite-cover assumptions. The empty space and empty cover retain the `WithBot ℕ∞`
dimension convention.

The open-cover formula is supplied by MinimalPrimes. The Jacobson criterion
uses closed points in nonempty locally closed subsets.

## References

* The Stacks Project, [Lemma 5.10.2](https://stacks.math.columbia.edu/tag/0B7I)
  for the chain-through-a-point open-neighborhood dimension argument, and
  [Section 5.18](https://stacks.math.columbia.edu/tag/005T) for Jacobson
  spaces and closed points in nonempty locally closed subsets.
* `MinimalPrimes.Topology.KrullDimension.OpenCover` for the open-cover formula.
* The mathlib community, *Mathlib*, `Mathlib.Topology.KrullDimension` for dimension
  and the subspace bound, `Mathlib.Topology.JacobsonSpace` for the closed-point
  criterion, and `Mathlib.Topology.Connected.LocallyConnected` for openness of
  connected components.
-/

public section

open Order Set TopologicalSpace Topology
open TopologicalSpace.IrreducibleCloseds

variable {X : Type*} [TopologicalSpace X]

/-- A Jacobson space is discrete if each of its closed points is open.
The proof uses the locally-closed-set characterization of Jacobson spaces in
mathlib's `Topology.JacobsonSpace`; see the Stacks Project, Section 5.18. -/
theorem JacobsonSpace.discreteTopology_of_isOpen_singleton_closedPoint
    [JacobsonSpace X]
    (h : ∀ x ∈ closedPoints X, IsOpen ({x} : Set X)) :
    DiscreteTopology X := by
  have hopen : IsOpen (closedPoints X) := by
    rw [← (closedPoints X).biUnion_of_singleton]
    exact isOpen_biUnion h
  have hclosed : closedPoints X = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
      (X := X) (⟨x, hx⟩ : ((closedPoints X)ᶜ).Nonempty)
      hopen.isClosed_compl.isLocallyClosed
    exact hy hyclosed
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  exact h x (by rw [hclosed]; trivial)

/-- A quotient of a space onto a Jacobson space has topological Krull
dimension at most zero if the inverse image of every closed point is open.
Quotient openness transfers the hypothesis to the target; then the Jacobson
closed-point criterion (Stacks Project, Section 5.18) gives discreteness and
mathlib's `topologicalKrullDim_zero_of_discreteTopology` gives the bound. -/
theorem Topology.IsQuotientMap.topologicalKrullDim_le_zero_of_isOpen_preimage_closedPoint
    {Y : Type*} [TopologicalSpace Y] {f : X → Y} [JacobsonSpace Y]
    (hf : IsQuotientMap f)
    (h : ∀ y ∈ closedPoints Y, IsOpen (f ⁻¹' ({y} : Set Y))) :
    topologicalKrullDim Y ≤ 0 := by
  let _ : DiscreteTopology Y :=
    JacobsonSpace.discreteTopology_of_isOpen_singleton_closedPoint fun y hy ↦ by
      rw [← hf.isOpen_preimage]
      exact h y hy
  exact topologicalKrullDim_zero_of_discreteTopology Y

/-- In a locally connected space, topological Krull dimension is the supremum
of the dimensions of the connected components. Specializes the open-cover
formula (compare Stacks Project, Lemma 5.10.2) using mathlib's
`isOpen_connectedComponent`. -/
theorem topologicalKrullDim_eq_iSup_connectedComponent
    [LocallyConnectedSpace X] :
    topologicalKrullDim X =
      ⨆ x : X, topologicalKrullDim (connectedComponent x) := by
  apply topologicalKrullDim_eq_iSup_of_isOpen_cover
  · exact fun _ ↦ isOpen_connectedComponent
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion_of_mem x mem_connectedComponent
