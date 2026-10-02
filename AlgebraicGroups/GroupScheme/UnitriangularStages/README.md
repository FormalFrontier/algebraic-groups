<!-- SPDX-License-Identifier: Apache-2.0 -->

# Closed superdiagonal stages of the unitriangular group scheme

Fix a commutative ring `K` and natural numbers `n, r`. All constructions in
[`UnitriangularStageCoordinateRing.lean`](../../Algebra/UnitriangularStageCoordinateRing.lean)
and [`UnitriangularStages.lean`](../UnitriangularStages.lean) work without a
field, reducedness, nontriviality, or positive-rank assumption. Coefficient
change applies to **every commutative `K`-algebra**, including zero rings.

## The coordinate quotient

Let `C` be the existing unitriangular coordinate Hopf algebra
`UnitriangularCoordinateRing.CoordinateRing K (Fin n)`. The ideal
`UnitriangularStageCoordinateRing.ideal K n r` is generated in `C` by its
universal entries `xᵢⱼ` satisfying `i < j` and `j.val < i.val + r`.
For a `K`-algebra map `f : C →ₐ[K] R`, `mem_stage_iff` says exactly that
`f` annihilates this ideal if and only if its corresponding matrix belongs to
the existing `Matrix.UnitriangularGroup.superdiagonalSubgroup n R r`.
This is an equality-of-entries condition, not a condition on radicals or
geometric points. In particular, rank three at stage two kills entries
`(0,1)` and `(1,2)` but leaves `(0,2)` unconstrained.

`ideal_isHopfIdeal` proves stability under the counit, coproduct and
antipode. The proof uses the universal quotient points over their own
coordinate rings and the published matrix-stage subgroup laws, so it also
holds for nonreduced base rings. The quotient
`CoordinateRing K n r = C ⧸ ideal K n r` inherits its **native Hopf algebra**
structure; `quotientBialgHom` is the canonical quotient morphism. The
lemmas `ideal_zero` and `ideal_one` identify the first two ideals with
bottom. `ideal_le_succ` gives `Iᵣ ≤ Iᵣ₊₁`.

## Closed group schemes and points

`unitriangularStageScheme K n r` is the native group object in
`Over (Spec (.of K))` represented by the quotient Hopf algebra. The
`unitriangularStageInclusion` and `unitriangularStageSuccessor` are
**group-object morphisms** induced by Hopf morphisms and their underlying
scheme arrows are closed immersions. For a successor, the coordinate map
`CoordinateRing K n r →ₐ[K] CoordinateRing K n (r + 1)` goes from the
earlier quotient to the later quotient; `Spec.map` reverses it, yielding
an inclusion of the later stage into the earlier stage. The lemma
`unitriangularStageSuccessor_inclusion` identifies its composite with
the ambient stage inclusion.

For any `K`-algebra `R`, `unitriangularStagePointMulEquiv K n r R` identifies
the published matrix stage subgroup with morphisms
`Spec R → unitriangularStageUnderlyingScheme K n r` over `Spec K`, preserving
**the multiplication of the native group object**. The functors
`unitriangularStageFunctor` and `unitriangularStagePointsFunctor` on
`CommAlgCat K` are naturally isomorphic as **group-valued** functors by
`unitriangularStagePointsIso`. Coefficient maps act entrywise on matrix
stages and by point precomposition on represented points. The equalities
`unitriangularStageInclusion_point` and
`unitriangularStageSuccessor_point` identify both inclusions at *every*
coefficient algebra, not only at `K`-valued points.

[`AlgebraicGroupsTest/GroupScheme/UnitriangularStages.lean`](../../../AlgebraicGroupsTest/GroupScheme/UnitriangularStages.lean)
exercises the rank-three second stage, the successor and ambient point maps,
and the zero ring and empty/singleton dimensions. The published matrix
filtration gives trivial points once `n ≤ r`; the construction does not
assert that the quotient coordinate ring literally equals `K` without an
additional coordinate-algebra result.

## Scope

This construction does **not** supply an ambient categorical normal-subgroup
proof, a finite-additive-coordinate kernel square, flatness or smoothness, a
scheme/sheaf quotient, or a group-homomorphic section of an entry map.
Its scope is the closed filtration stages themselves and their natural
multiplicative functors of points.

With the repository's pinned toolchain and dependency cache ready, scoped
checks run as:

```sh
lake exe cache get
lake build AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
lake build AlgebraicGroups.GroupScheme.UnitriangularStages
lake build AlgebraicGroupsTest.GroupScheme.UnitriangularStages
```
