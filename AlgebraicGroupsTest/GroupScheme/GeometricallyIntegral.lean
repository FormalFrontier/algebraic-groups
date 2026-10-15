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
    GeometricallyIrreducible (multiplicativeGroupUnderlyingScheme K).hom := by
  let _ : IsIntegral (multiplicativeGroupUnderlyingScheme K).left := by
    change IsIntegral (Spec (.of (multiplicativeGroupCoordinateRing K)))
    infer_instance
  exact geometricallyIrreducible_of_grpObj_of_connectedSpace
    (multiplicativeGroupUnderlyingScheme K)

example (K : Type u) [Field K] :
    GeometricallyIntegral (multiplicativeGroupUnderlyingScheme K).hom := by
  let _ : IsIntegral (multiplicativeGroupUnderlyingScheme K).left := by
    change IsIntegral (Spec (.of (multiplicativeGroupCoordinateRing K)))
    infer_instance
  let _ : GeometricallyReduced (multiplicativeGroupUnderlyingScheme K).hom :=
    Smooth.geometricallyReduced _
  exact geometricallyIntegral_of_grpObj_of_connectedSpace
    (multiplicativeGroupUnderlyingScheme K)
