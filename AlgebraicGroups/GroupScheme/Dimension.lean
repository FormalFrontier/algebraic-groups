/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ComponentSchemeMap
public import AlgebraicGroups.GroupScheme.ReducedIdentityComponent
public import AlgebraicGroups.Topology.KrullDimension

/-!
# Dimensions of identity components

This file identifies the topological Krull dimension of a locally finite-type
group scheme over an algebraically closed field with the dimension of its
identity component.  It also combines this with invariance under scheme
reduction to treat the identity component of the reduction.

## References

- J. S. Milne, *Algebraic Groups*, the dimension discussion following
  Summary 1.36 (printed p. 17), for the common dimension of translated
  connected components. These are topological Krull dimensions; the
  tangent-space statement of Proposition 1.37 is different.
- The local `Topology.KrullDimension` supplies the open-cover supremum
  formula, `GroupScheme.ComponentGroup` the rational representatives,
  `GroupScheme.ComponentSchemeMap` the translation isomorphisms, and
  `Scheme.Reduction` the invariance of topological dimension under reduction.
  The mathlib community, *Mathlib*, supplies topological Krull dimension
  and the dimension invariance of homeomorphisms and embeddings.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

/-- A locally finite-type group scheme over an algebraically closed field and
its identity component have the same topological Krull dimension. This
follows the common-component-dimension discussion in Milne,
*Algebraic Groups*, immediately following Summary 1.36, using translations
and the open-cover formula rather than irreducible-component dimensions. -/
theorem identityComponent_topologicalKrullDim [LocallyOfFiniteType f] :
    topologicalKrullDim (Scheme.identityComponentOver (Over.mk f)).left =
      topologicalKrullDim G := by
  apply le_antisymm
  · exact (Scheme.identityComponentι (Over.mk f)).left.isOpenEmbedding.isInducing
      |>.topologicalKrullDim_le
  · rw [topologicalKrullDim_eq_iSup_of_isOpen_cover
      (fun c : ConnectedComponents G ↦ (G.connectedComponentOpen c : Set G))
      (fun c ↦ (G.connectedComponentOpen c).isOpen) (by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iUnion_of_mem (ConnectedComponents.mk x)
          ((G.mem_connectedComponentOpen (ConnectedComponents.mk x) x).2 rfl))]
    apply iSup_le
    intro c
    obtain ⟨a, rfl⟩ := groupSchemePointComponent_surjective f c
    let e := (identityComponentIsoConnectedComponent f a).schemeIsoToHomeo
    exact (e.isHomeomorph.topologicalKrullDim_eq e).symm.le

/-- The identity component of the reduction of a locally finite-type group
scheme over an algebraically closed field has the same topological Krull
dimension as the original scheme.  Reducedness of the Cartesian square of the
reduction is the explicit hypothesis needed for its group-scheme structure.
The component-dimension idea is in Milne, *Algebraic Groups*, after Summary
1.36; the final equality uses the local reduction-dimension invariance. -/
theorem reducedIdentityComponent_topologicalKrullDim
    [LocallyOfFiniteType f]
    [IsReduced ((Scheme.reductionOver (Over.mk f) ⊗
      Scheme.reductionOver (Over.mk f)).left)] :
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
      topologicalKrullDim G := by
  let _ : IsClosedImmersion (Scheme.reductionι.app G) := by
    change IsClosedImmersion G.nilradical.subschemeι
    infer_instance
  let _ : LocallyOfFiniteType (Scheme.reductionOver (Over.mk f)).hom := by
    change LocallyOfFiniteType (Scheme.reductionι.app G ≫ f)
    infer_instance
  let _ : GrpObj (Over.mk (Scheme.reductionOver (Over.mk f)).hom) :=
    inferInstanceAs (GrpObj (Scheme.reductionOver (Over.mk f)))
  let _ : LocallyConnectedSpace (Over.mk
      (Scheme.reductionOver (Over.mk f)).hom).left :=
    inferInstanceAs (LocallyConnectedSpace
      (Scheme.reductionOver (Over.mk f)).left)
  calc
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
        topologicalKrullDim (Scheme.reductionOver (Over.mk f)).left :=
      identityComponent_topologicalKrullDim
        (Scheme.reductionOver (Over.mk f)).hom
    _ = topologicalKrullDim G := Scheme.reduction_topologicalKrullDim G

end

end AlgebraicGeometry
