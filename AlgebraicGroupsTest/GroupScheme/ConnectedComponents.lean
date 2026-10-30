/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.ClosedPoints
import SchemeProperties.NoetherianComponents
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Artinian.Module

/-!
# Connected components of group schemes

A topologically Noetherian group scheme locally of finite type over an
algebraically closed field has irreducible connected components. Left
translations give ambient homeomorphisms carrying any closed point to any other,
and local finite type supplies the Jacobson hypothesis.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

example {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [CategoryTheory.GrpObj (Over.mk f)] [TopologicalSpace.NoetherianSpace G]
    (x : G) : IsIrreducible (connectedComponent x) := by
  let : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  exact isIrreducible_connectedComponent_of_closedPoints_homogeneous
    (fun x y ↦ by
      obtain ⟨e, he⟩ := AlgebraicGeometry.exists_groupSchemeIso_map_closedPoint f x y
      exact ⟨((CategoryTheory.Over.forget _).mapIso e).schemeIsoToHomeo, he⟩)
    x
