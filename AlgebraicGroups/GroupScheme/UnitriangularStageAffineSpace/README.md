<!-- SPDX-License-Identifier: Apache-2.0 -->

# Underlying affine space of a unitriangular stage

For a commutative ring `K` and natural numbers `n,r`, the actual unitriangular
stage quotient is a polynomial algebra on strict-upper index pairs `(i,j)` with
`i.val + r ≤ j.val`. This module carries that algebra
equivalence through `Spec` to an isomorphism over `Spec K`:

```lean
unitriangularStageUnderlyingScheme K n r ≅
  (AffineSpace (SurvivingPair n r) (Spec (.of K))).asOver (Spec (.of K))
```

Here `SurvivingPair` and `polynomialEquiv` are in
`UnitriangularStageCoordinateRing`; the scheme declarations are in
`AlgebraicGeometry`. The isomorphism uses the actual structural maps to the base,
not just a correspondence between rational points. No field, domain,
nontriviality or positive-stage hypothesis is imposed. The zero ring, empty rank
and empty surviving-variable set are included.

## Public interface

Import `AlgebraicGroups.GroupScheme.UnitriangularStageAffineSpace` using an ordinary
public import. The API consists of:

- `unitriangularStageUnderlyingAffineSpaceIso`: the underlying over-scheme iso;
- `unitriangularStageUnderlyingAffineSpaceIso_preimage_variable`: pulling back
  an affine-space coordinate gives its actual stage-quotient entry;
- `unitriangularStageUnderlyingAffineSpaceIso_preimage_inverse`: pulling back a
  regular function through the inverse gives its polynomial expression.

The [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UnitriangularStageAffineSpace.lean)
exercises the
general interface, inverse identity, integer and zero-ring examples, empty
index cases, and rank-three/stage-two's surviving `(0,2)` coordinate.

## Dependencies, checking and limits

The producer imports the stage polynomial algebra, actual stage
schemes and mathlib affine-space interface. The proof pattern follows the
existing whole-unitriangular underlying-scheme comparison, with the inverse
stage algebra equivalence in the contravariant direction.

With the pinned toolchain available, first obtain the matching mathlib cache
successfully, then check the producer and public client:

```sh
lake exe cache get
lake build +AlgebraicGroups.GroupScheme.UnitriangularStageAffineSpace +AlgebraicGroupsTest.GroupScheme.UnitriangularStageAffineSpace
```

This is not an additive-Hopf or group-scheme isomorphism. It does not identify
the categorical product of copies of the additive group, prove equality with
the full positive-stage coordinate projection, construct a section, establish
a quotient or descent theorem, or assert flatness/smoothness or base-change
tower coherence. The known rank-three cross term obstructs the
chosen zero-higher-entry section's group compatibility, not
every possible group section.

## Credit

Formal Frontier Agents implemented the stage algebra, native stages and this
geometric comparison. This implementation reuses the stage polynomial
equivalence and adapts the existing whole-unitriangular
`AlgebraicGroups.GroupScheme.UnitriangularGeometry` Spec/Over proof pattern,
using mathlib's affine-space machinery. See
[credits](../../../CREDITS.md) for contributors and reuse attribution.

## References

- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field*, Cambridge University Press, 2017, item 2.9 (the full
  unitriangular algebraic group's polynomial presentation). The arbitrary-base
  whole-stage over-scheme isomorphism is a separate result.
- Mathlib contributors, `Mathlib.AlgebraicGeometry.AffineSpace`
  (`AffineSpace.SpecIso` and its structural-map comparison).
- The existing `UnitriangularGeometry` supplies the whole-group
  `Spec`/`Over.isoMk` pattern.
