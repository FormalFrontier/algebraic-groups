# Identity and scalar towers for unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence` (or
`AlgebraicGroups`) for the identity and tower laws of the existing native
`AlgebraicGeometry.unitriangularGroupSchemeBaseChangeIso`. The corresponding
ordinary-import inverse-coordinate client is
`AlgebraicGroupsTest.GroupScheme.UnitriangularBaseChangeCoherence`.

Let `R`, `S`, `T` be commutative rings in the same universe with `[Algebra R S]`,
`[Algebra S T]`, `[Algebra R T]`, and `[IsScalarTower R S T]`. Let `ι` be a
finite linearly ordered type in that universe. There is no additional
nontriviality, nonempty-index, flatness, injectivity, or base-map compatibility
assumption. In particular, the statements include zero rings and `Fin 0`/`Fin 1`.

`unitriangularBaseMap R S` abbreviates the map
`Spec (.of S) ⟶ Spec (.of R)` induced by `algebraMap R S`.
`unitriangularBaseMap_comp R S T` says that `b_ST ≫ b_RS = b_RT`,
and `unitriangularBaseMap_self R` says `b_RR = 𝟙`.

Write `G_R := unitriangularGroupScheme R ι`. The forward direction of
`unitriangularGroupSchemeBaseChangeTowerIso R S T ι` is **direct to iterated**:

```lean
(Over.pullback b_RT).mapGrp.obj G_R ≅
  (Over.pullback b_ST).mapGrp.obj ((Over.pullback b_RS).mapGrp.obj G_R)
```

It transports along `b_ST ≫ b_RS = b_RT`, then applies
`Functor.mapGrpNatIso (Over.pullbackComp b_ST b_RS)` and
`Functor.mapGrpCompIso`, evaluated at `G_R`. Thus
`unitriangularGroupSchemeBaseChangeIso_tower R S T ι` identifies the **existing**
direct comparison's hom with the composite of this forward map, the pullback
of the **existing** `R → S` comparison, and the **existing** `S → T`
comparison, in that order. `unitriangularGroupSchemeBaseChangeSelfIso R ι`
likewise uses the equality transport `b_RR = 𝟙`,
`Functor.mapGrpNatIso Over.pullbackId`, and `Functor.mapGrpIdIso`;
`unitriangularGroupSchemeBaseChangeIso_self R ι` identifies the existing
`R → R` comparison with its hom.

The proofs compare the actual pullback mates by their projections. The affine
comparison uses tensor congruence and
`Algebra.TensorProduct.cancelBaseChange`, together with the coordinate
equations `UnitriangularCoordinateRing.baseChange_self` and
`UnitriangularCoordinateRing.baseChange_tower`. It does not replace the native
group law or introduce an arbitrary isomorphism in place of canonical pullback.
The `Fin 2` client begins with a point of the **pulled-back group object** over
`Spec T`. Using `GrpObj.inv_comp`, the native point equivalence's `map_inv`,
and the tower law, it proves equality of the direct and canonical iterated
`(0,1)` inverse coordinates, both read as the corresponding inverse matrix
entry. Generic and zero-ring/empty/singleton examples are also included.

This API does **not** assert arbitrary-morphism naturality, index reordering,
a general pseudofunctor, rational-map or `PartialIso` laws, or source-specific
coverage. It builds on the separately documented
[native one-step group-scheme comparison](UnitriangularSchemeBaseChange.md).

This repository pins `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, Scheme Properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`, and General Linear Groups
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` (13 resolved packages,
three direct requirements). From the repository root, a future authorized
verifier installs the pinned toolchain and **successfully fetches the matching
precompiled mathlib cache before any build**, then checks the producer and
ordinary-import client:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence
lake build AlgebraicGroupsTest.GroupScheme.UnitriangularBaseChangeCoherence
```

The destination preparation dated 2026-09-30 is static: it has not run those
commands or established complete transitive standard-axiom evidence on this
dependency graph. Original proofs and client: worker-b Task
`hive-request-060cf9c4f55345280f96724efb23b870529b5dd3` (UID
`a59545aa-87cc-40a0-b35e-c980d68c912a`). Official-import adaptation:
worker-b Task `hive-request-3e98325c49b66caef94ea71d0ab8e154a9a23c51`
(UID `c6a480de-e7b4-44f8-8106-17e6d759ecc7`). Destination static transfer:
worker-b Task `hive-request-83e761635ef9fb7b8563c64cbaa53c61a6eced8b`
(UID `51aa9bf0-39a7-45b6-9dbd-6cf8bdf19217`). The one-step, coordinate
comparison and mathlib contributors retain their separate credit. Independent
destination review, native verification, acceptance and publication are
separate decisions; this guide claims none of them.
