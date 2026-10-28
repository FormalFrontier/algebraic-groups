/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.FiniteTriangularGeometry
import AlgebraicGroups.GroupScheme.GeometricallyIntegral

/-!
# A connected group-scheme geometric-integrality example

The multiplicative group over any field satisfies the hypotheses. Its
connectedness comes from its domain coordinate ring, and its geometric
reducedness comes from smoothness. In particular the hypotheses are satisfied
by a positive-dimensional group, not only by the trivial group scheme.
-/

open AlgebraicGeometry

universe u

example (K : Type u) [Field K] :
    GeometricallyIrreducible ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).hom := by
  let _ : IsIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).left :=
    inferInstance
  exact geometricallyIrreducible_of_grpObj_of_connectedSpace
    ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)

example (K : Type u) [Field K] :
    GeometricallyIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).hom := by
  let _ : IsIntegral ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).left :=
    inferInstance
  let _ : GeometricallyReduced ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X).hom :=
    inferInstance
  exact geometricallyIntegral_of_grpObj_of_connectedSpace
    ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)
