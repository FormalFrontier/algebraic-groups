/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPoints
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import SchemeProperties.ComponentFibers
public import SchemeProperties.NoetherianComponents

/-!
# Geometric integrality of connected group schemes

A connected group scheme of finite type over a field is geometrically
irreducible, and is geometrically integral if it is geometrically reduced.
Finite type is expressed by local finite type and quasi-compactness. Neither
properness nor a choice of algebraic closure is part of either statement.

Geometric reducedness is essential for integrality: in positive characteristic
the connected finite group scheme `α_p` is not reduced. Even reducedness over the ground field
is insufficient over an imperfect field: in characteristic `p`, the reduced
additive subgroup defined by `x^p - a*y^p = 0`, with `a` not a `p`-th power,
acquires nilpotents after adjoining a `p`-th root of `a`. Connectedness is also
essential, as witnessed by the constant group scheme of order two.

## References

- J. S. Milne, *Abelian Varieties*, Chapter I, §1, p. 8: smoothness,
  irreducibility and geometric connectedness of connected group varieties.
- `AlgebraicGroups.GroupScheme.ClosedPoints`, for transitivity of translations
  on closed points over algebraically closed fields.
- SchemeProperties, `ComponentFibers` and `NoetherianComponents`, for geometric
  connectedness in the presence of a section and irreducibility of homogeneous
  connected components.
- Mathlib, `AlgebraicGeometry.Geometrically.Integral`, for geometric integrality.
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

private theorem irreducibleSpace_of_grpObj_of_connectedSpace_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [GrpObj (Over.mk f)]
    [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace X] :
    IrreducibleSpace X := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := ⟨⟩
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hhom : ∀ x y : closedPoints X, ∃ e : X ≃ₜ X, e x.1 = y.1 := by
    intro x y
    obtain ⟨e, he⟩ := exists_groupSchemeIso_map_closedPoint f x y
    exact ⟨((Over.forget _).mapIso e).schemeIsoToHomeo, he⟩
  rw [irreducibleSpace_def]
  simpa only [PreconnectedSpace.connectedComponent_eq_univ, Set.top_eq_univ] using
    isIrreducible_connectedComponent_of_closedPoints_homogeneous hhom
      (η[Over.mk f].left (IsLocalRing.closedPoint K))

/-- A connected group scheme of finite type over a field is geometrically
irreducible, without a reducedness hypothesis.

This follows the connected group-variety discussion in Milne, *Abelian
Varieties*, Chapter I, §1, p. 8, using translations on closed points in place
of smoothness to obtain irreducibility. -/
theorem geometricallyIrreducible_of_grpObj_of_connectedSpace
    {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [ConnectedSpace G.left] : GeometricallyIrreducible G.hom := by
  let _ : GeometricallyConnected G.hom :=
    geometricallyConnected_of_connectedSpace_of_section G η[G]
  let _ : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ ?_⟩
  -- After any field extension, pass to an algebraic closure, where translations
  -- make the closed points homogeneous. Irreducibility then descends.
  let fL : pullback G.hom y ⟶ Spec (.of L) := pullback.snd G.hom y
  let _ : GrpObj (Over.mk fL) := Over.grpObjMkPullbackSnd
  let Ω := AlgebraicClosure L
  let z : Spec (.of Ω) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L Ω))
  let fΩ : pullback fL z ⟶ Spec (.of Ω) := pullback.snd fL z
  let _ : GrpObj (Over.mk fΩ) := Over.grpObjMkPullbackSnd
  let _ : ConnectedSpace ↥(pullback fL z) :=
    GeometricallyConnected.connectedSpace_of_subsingleton fΩ
  let _ : IrreducibleSpace ↥(pullback fL z) :=
    irreducibleSpace_of_grpObj_of_connectedSpace_of_isAlgClosed fΩ
  exact (pullback.fst fL z).surjective.irreducibleSpace (pullback.fst fL z).continuous

/-- A connected geometrically reduced group scheme of finite type over a field
is geometrically integral.

This gives the scheme-theoretic geometric-integrality consequence of the
connected group-variety discussion in Milne, *Abelian Varieties*, Chapter I,
§1, p. 8. It imposes neither properness nor a separate separatedness hypothesis. -/
theorem geometricallyIntegral_of_grpObj_of_connectedSpace
    {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [GeometricallyReduced G.hom] [ConnectedSpace G.left] :
    GeometricallyIntegral G.hom := by
  let _ : GeometricallyIrreducible G.hom :=
    geometricallyIrreducible_of_grpObj_of_connectedSpace G
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible G.hom

end AlgebraicGeometry
