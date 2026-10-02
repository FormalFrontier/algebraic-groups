<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Positive-stage projection onto additive coordinates

Import `AlgebraicGroups.GroupScheme.UnitriangularStageProjectionBridge`.
For `[CommRing K]`, a matrix rank `n` and a stage `r` with `hr : 1 ≤ r`,
write `D = Matrix.UnitriangularGroup.superdiagonalIndex n r` for the
current-superdiagonal positions and `S =
UnitriangularStageCoordinateRing.SurvivingPair n r` for all positions
remaining in the stage quotient. The injection
`stageSuperdiagonalInclusion n r hr : D → S` retains the same matrix
positions; `mem_range_stageSuperdiagonalInclusion` characterizes its image
by gap exactly `r`.

`stageProductCoordinatePullback K n r hr` first renames the polynomial
variables indexed by `D` into those indexed by `S` and then applies the
inverse stage polynomial equivalence. Thus each current variable pulls
back to the **actual** stage coordinate, as recorded by
`stageProductCoordinatePullback_X` and
`stageCoordinateAlgHom_eq_productPullback`. This is the contravariant
coordinate map: it maps the product's coordinate ring **into** the stage
coordinate ring. `unitriangularStageUnderlyingSpecIso` compares the
underlying stage with the polynomial spectrum. The theorem
`unitriangularStageCoordinateMap_underlying_spec` identifies the **whole**
underlying genuine group-scheme arrow with this spectrum projection;
`unitriangularStageCoordinateMap_underlying_affineSpace` transports it to
the actual affine-space comparison. These statements use the full
additive-product fan's universal property, not just equality of points.

`stageProductCoordinateKill` retains current variables and kills the
higher-gap variables. The resulting contravariant pullback
`stageProductSectionPullback` has readbacks
`stageProductSectionPullback_inclusion` and
`stageProductSectionPullback_higher`. Its spectrum map defines
`unitriangularStageCoordinateSectionOver`, and
`unitriangularStageCoordinateSectionOver_comp` says that this is a
section of the **underlying arrow over `Spec K`**. The examples in
`AlgebraicGroupsTest.GroupScheme.UnitriangularStageProjectionBridge`
check ranks `0,1,3`, stages `1,2,3,4`, empty coordinate types,
`K = ℤ` and `K = ZMod 1`. Run
`lake exe cache get` followed by
`lake build AlgebraicGroupsTest.GroupScheme.UnitriangularStageProjectionBridge`
with the pinned graph for that ordinary-import client.

This chosen zero-higher-entry section is **not** asserted to be a
group-scheme morphism: at rank `3`, stage `1`, the matrix multiplication
cross term obstructs that particular choice, not every conceivable
group section. No group quotient, descent, smoothness, flatness, base-change
tower is asserted.

Formal Frontier Agents contributed the stage projection and section
argument and Lean proof. See [credits](../../../CREDITS.md) for collective credit.
