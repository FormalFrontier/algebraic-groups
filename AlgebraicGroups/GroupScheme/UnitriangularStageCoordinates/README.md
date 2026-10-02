<!-- SPDX-License-Identifier: Apache-2.0 -->

# Positive-stage unitriangular coordinates

Let `K` be any commutative ring, `n r : ℕ` and **`hr : 1 ≤ r`**. Import
`AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates` for the actual
group-scheme morphism in `Grp (Over (Spec (.of K)))`:

```lean
unitriangularStageCoordinateMap K n r hr :
  unitriangularStageScheme K n r ⟶
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
      additiveGroupScheme K)
```

For each index, the
[`UnitriangularStageCoordinateRing.coordinateBialgHom`](../../Algebra/UnitriangularStageCoordinates.lean)
sends the additive group's rank-one symmetric-algebra generator to the
universal stage entry. Its counit is zero and its coproduct is primitive:
the two endpoint terms survive, while intermediate matrix-entry terms lie in
the forbidden-entry ideal. Applying `hopfSpec` gives the group-scheme
projections, whose categorical product is the displayed map. No field,
nontriviality, reducedness or characteristic hypothesis is imposed; zero
rings, empty superdiagonal index types and ranks `n = 0, 1` are included.
There is **no coordinate map at `r = 0`**.

`unitriangularStageCoordinateMap_point` identifies each actual product
projection at every commutative `K`-algebra `R` with the corresponding
component of `superdiagonalCoordinateHom` under
`unitriangularStagePointMulEquiv` and `additiveGroupMulEquivPoints`.
The target `Multiplicative (superdiagonalIndex n r → R)` uses pointwise
**addition**, not multiplication of matrices. The separate
`unitriangularStageCoordinateMap_point_natural` states compatibility with
arbitrary `K`-algebra homomorphisms. The successor-stage coordinates vanish
by `UnitriangularStageCoordinateRing.successor_coordinate`, and
`unitriangularStageCoordinateMap_successor_zero` identifies the composite
`S_(r+1) → S_r → Gₐ^J` with the **zero group-scheme morphism**.

The [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UnitriangularStageCoordinates.lean)
checks the `(0,1)` and `(1,2)` first-stage entries, the `(0,2)` second-stage
entry in rank three, zero-ring/empty-index cases and the rank-three cross
term: over `ℤ`, `(1 + E₀₁)(1 + E₁₂)` has `(0,2)` entry one, though both
factors have that entry zero. This rules out the indicated higher-coordinate
or zero-higher-entry **homomorphism**, not every possible section.

With the pinned toolchain, first fetch the matching mathlib cache successfully
and then check both producers and the public client:

```sh
lake exe cache get
lake build +AlgebraicGroups.Algebra.UnitriangularStageCoordinates +AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates +AlgebraicGroupsTest.GroupScheme.UnitriangularStageCoordinates
```

The coordinate module proves successor **vanishing**, not a kernel square.
The separate [kernel guide](../UnitriangularStageKernel/README.md) gives the
stronger underlying over-scheme pullback. Neither result supplies a whole-stage
additive Hopf/group-scheme isomorphism, group-homomorphic section, represented
or sheaf quotient, surjectivity, effective epimorphism, flatness, smoothness,
descent, native base-change tower or source-level coverage. See the repository
[credits](../../../CREDITS.md) for Formal Frontier Agents' contributor roles.
