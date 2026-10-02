<!-- SPDX-License-Identifier: Apache-2.0 -->

# Normal closed unitriangular stages

For any commutative ring `K` and natural numbers `n,r`, the represented
superdiagonal stage `S_r` is a native normal subgroup object of the
upper-unitriangular group scheme `U_n` over `Spec K`. This includes the zero
ring, empty and one-element ranks, and the stages `r = 0, 1`.

Import `AlgebraicGroups.GroupScheme.UnitriangularStageNormality` for the
`AlgebraicGeometry.unitriangularStageInclusion_normal` instance of
`IsMonHom.Normal`. The module also constructs the underlying over-scheme
conjugation factor `AlgebraicGeometry.unitriangularStageConjugation` from
`U_n ×_K S_r` back to `S_r`. The theorem
`unitriangularStageConjugation_inclusion` identifies its composite with the
closed immersion as categorical conjugation in `U_n`; the closed immersion is
a monomorphism. At every commutative `K`-algebra,
`unitriangularStageConjugation_point` reads the factor as ordinary matrix
conjugation, naturally under algebra maps.

The construction uses the tensor-product coordinate algebra of the affine
product, obtains the conjugate within the matrix stage by subgroup normality,
and applies the [stage-point equivalence](../UnitriangularStages/README.md)
over that *same* tensor-product algebra. Equality after the inclusion is proved
on the universal product, not inferred solely from individual affine points.

The [ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UnitriangularStageNormality.lean)
includes boundary cases. To check this module and client in the repository's
pinned toolchain, fetch the matching mathlib cache successfully first:

```sh
lake exe cache get
lake build +AlgebraicGroups.GroupScheme.UnitriangularStageNormality +AlgebraicGroupsTest.GroupScheme.UnitriangularStageNormality
```

Conjugation here is **not** asserted to be a homomorphism from the product
group. This module does not establish an additive-coordinate kernel, a
scheme/sheaf quotient, flatness, smoothness or source-level coverage. The
[positive-stage coordinate map](../UnitriangularStageCoordinates/README.md)
is a separate construction; normality is not a prerequisite for its proof.

Formal Frontier Agents developed the stage constructions and normality proof;
see the repository [credits](../../../CREDITS.md) for contributor roles and
dependency attribution.
