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


For pinned dependencies, build and focused client commands, see the
[build guide](BUILDING.md). Project and third-party contributor credit is in
[credits](../CREDITS.md).
