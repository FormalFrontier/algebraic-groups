# Identity and scalar towers for unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence` (or
`AlgebraicGroups`) for the identity and tower laws of the existing
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

The proofs compare the pullback mates by their projections. The affine
comparison uses tensor congruence and
`Algebra.TensorProduct.cancelBaseChange`, together with the coordinate
equations `UnitriangularCoordinateRing.baseChange_self` and
`UnitriangularCoordinateRing.baseChange_tower`. It does not replace the pullback
group law or introduce an arbitrary isomorphism in place of canonical pullback.
The `Fin 2` client begins with a point of the **pulled-back group object** over
`Spec T`. Using `GrpObj.inv_comp`, the point equivalence's `map_inv`,
and the tower law, it proves equality of the direct and canonical iterated
`(0,1)` inverse coordinates, both read as the corresponding inverse matrix
entry. Generic and zero-ring/empty/singleton examples are also included.

This API does **not** assert arbitrary-morphism naturality, index reordering,
a general pseudofunctor, rational-map or `PartialIso` laws. It builds on the
separately documented
[one-step group-scheme comparison](UnitriangularSchemeBaseChange.md).

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.9: the field-case `U_n`
  coordinate presentation, not the arbitrary-base identity or tower laws.
- The Stacks Project, Section 26.17, Lemma 26.17.2: affine fibre products
  as spectra of tensor products. Andrew Yang's Mathlib `pullbackSpecIso` and
  projection laws (`Mathlib.AlgebraicGeometry.Pullbacks`) support the comparison
  of pullback projections.
- Yaël Dillies's `hopfSpec`, `algSpec`, `pullbackSpecIso'` and its
  monoid-homomorphism pullback instance (`Mathlib.AlgebraicGeometry.Group.Affine`)
  support the one-step comparison. Her `Functor.mapGrpNatIso`,
  `Functor.mapGrpCompIso` and `Functor.mapGrpIdIso`
  (`Mathlib.CategoryTheory.Monoidal.Grp`) lift the canonical pullback laws to
  group objects; Markus Himmel contributed to the wider group-object module.
- Christian Merten's `MvPolynomial.algebraTensorAlgEquiv`
  (`Mathlib.RingTheory.TensorProduct.MvPolynomial`) underlies the coordinate
  comparison, and his `Algebra.TensorProduct.cancelBaseChange`
  (`Mathlib.RingTheory.TensorProduct.Maps`) is used in the tower proof. Yaël
  Dillies's `AddMonoidAlgebra.scalarTensorEquiv`
  (`Mathlib.RingTheory.TensorProduct.MonoidAlgebra`) implements the polynomial
  equivalence; Antoine Chambert-Loir's earlier
  `MvPolynomial.scalarRTensorAlgEquiv` is related, not the equivalence used here.
- `Algebra.TensorProduct.lid` (`Mathlib.RingTheory.TensorProduct.Maps`) uses
  Kevin Buzzard's Mathlib4 port; Kim Morrison and Johan Commelin contributed
  to the wider tensor-product maps module.

For pinned dependencies, build and focused client commands, see the
[build guide](BUILDING.md). For project-wide authorship and third-party
notices, see [credits](../CREDITS.md).
