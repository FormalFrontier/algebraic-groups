/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension

/-!
# Topological Krull dimension and open covers

This file proves that topological Krull dimension is local on an arbitrary open
cover.  It then specializes the result to the open cover of a locally connected
space by its connected components.
-/

public section

open Order Set TopologicalSpace Topology
open TopologicalSpace.IrreducibleCloseds

variable {X : Type*} [TopologicalSpace X]

/-- A Jacobson space is discrete if each of its closed points is open. -/
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
dimension at most zero if the inverse image of every closed point is open. -/
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

/-- The topological Krull dimension of a space is the supremum of the
dimensions of the members of any open cover. -/
theorem topologicalKrullDim_eq_iSup_of_isOpen_cover
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim]
    apply iSup_le
    intro p
    obtain ⟨z, hz⟩ := p.head.isIrreducible.nonempty
    have hzcover : z ∈ ⋃ i, U i := by
      rw [hcover]
      exact Set.mem_univ z
    rw [Set.mem_iUnion] at hzcover
    obtain ⟨i, hi⟩ := hzcover
    let e := orderIsoOfIsOpenEmbedding (Subtype.val : U i → X)
      (hU i).isOpenEmbedding_subtypeVal
    let q : LTSeries (IrreducibleCloseds (U i)) :=
      LTSeries.mk p.length
        (fun j ↦ e.symm ⟨p j, ⟨⟨z, hi⟩, p.head_le j hz⟩⟩)
        (fun _ _ hjk ↦ e.symm.strictMono (p.strictMono hjk))
    apply le_iSup_of_le i
    change (q.length : WithBot ℕ∞) ≤ Order.krullDim (IrreducibleCloseds (U i))
    exact q.length_le_krullDim
  · apply iSup_le
    intro i
    exact topologicalKrullDim_subspace_le X (U i)

/-- In a locally connected space, topological Krull dimension is the supremum
of the dimensions of the connected components. -/
theorem topologicalKrullDim_eq_iSup_connectedComponent
    [LocallyConnectedSpace X] :
    topologicalKrullDim X =
      ⨆ x : X, topologicalKrullDim (connectedComponent x) := by
  apply topologicalKrullDim_eq_iSup_of_isOpen_cover
  · exact fun _ ↦ isOpen_connectedComponent
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion_of_mem x mem_connectedComponent
