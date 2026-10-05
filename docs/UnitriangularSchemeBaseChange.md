# Base change of unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.UnitriangularBaseChange` (or
`AlgebraicGroups`) to use
`AlgebraicGeometry.unitriangularGroupSchemeBaseChangeIso R S ι`. For
commutative rings `R`, `S` in the same universe, `[Algebra R S]`, and a
finite linearly ordered index type `ι` in that universe, this is an
**isomorphism of group objects** between the
`Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))` of
`unitriangularGroupScheme R ι` and `unitriangularGroupScheme S ι`.
Zero rings and empty or singleton indices are allowed; there is no
nontriviality, nonempty-index, flatness, or injectivity condition.

`unitriangularGroupSchemeBaseChangeIso_hom_left` reads back its underlying
forward scheme map. It first applies `pullbackSymmetry`, then the affine
comparison `pullbackSpecIso' R S (CoordinateRing R ι)`, then `Spec.map` of
`(UnitriangularCoordinateRing.baseChangeBialgEquiv R S ι).symm` viewed as a
ring homomorphism. **The inverse** is required because `Spec` reverses
coordinate-ring arrows. The companion
`unitriangularGroupSchemeBaseChangeIso_hom_over` identifies the resulting
map to `Spec S` with the second projection of the pullback. The
first factor is group-compatible by mathlib's existing affine-pullback
instance; the second uses the unitriangular Hopf comparison.
Neither step transports a group law from an affine-space isomorphism.

The ordinary-import
`AlgebraicGroupsTest.GroupScheme.UnitriangularBaseChange` client takes two
points of the **pulled-back group object** over a commutative `S`-algebra
`T`, whose images under the group isomorphism correspond to unitriangular
`Fin 3` matrices `a` and `b`. It maps their product through the
isomorphism, then reads its `(0,2)` entry as
`a₀₂ + b₀₂ + a₀₁ * b₁₂`; this cross term is derived from their
multiplication, not assumed. The same client checks the generic comparison
and zero-ring `Fin 0`/`Fin 1` cases. No all-morphism naturality,
index-reordering, classification, or geometric promotion follows.

## References

- James S. Milne, *Algebraic Groups* (2017), items 2.8 (the matrix-entry
  coproduct) and 2.9 (the field-case `U_n` coordinates). Neither states this
  group-object comparison over arbitrary commutative rings.
- The Stacks Project, Section 26.17, Lemma 26.17.2: affine fibre products
  as spectra of tensor products. Andrew Yang's Mathlib `pullbackSpecIso` and
  projection laws (`Mathlib.AlgebraicGeometry.Pullbacks`) formalize this case.
- Christian Merten's `MvPolynomial.algebraTensorAlgEquiv`
  (`Mathlib.RingTheory.TensorProduct.MvPolynomial`) supplies the coordinate
  scalar extension; Yaël Dillies's `AddMonoidAlgebra.scalarTensorEquiv`
  (`Mathlib.RingTheory.TensorProduct.MonoidAlgebra`) implements it. Antoine
  Chambert-Loir's earlier `MvPolynomial.scalarRTensorAlgEquiv` is a related
  equivalence, not the one used in this comparison.
- Yaël Dillies's Mathlib `hopfSpec`, `algSpec`, `pullbackSpecIso'` and its
  monoid-homomorphism pullback instance (`Mathlib.AlgebraicGeometry.Group.Affine`)
  support the group-object comparison. Christian Merten, Michał Mrugała and
  Andrew Yang contributed to the wider affine group-scheme formalization.
- The underlying Hopf comparison uses Amelia Livingston and Andrew Yang's
  tensor structures (`Mathlib.RingTheory.Bialgebra.TensorProduct` and
  `Mathlib.RingTheory.HopfAlgebra.TensorProduct`), and Yaël Dillies's
  `BialgEquiv.ofAlgEquiv` (`Mathlib.RingTheory.Bialgebra.Equiv`) and convolution
  lemmas `AlgHom.convMul_comp_bialgHom_distrib`
  (`Mathlib.RingTheory.Bialgebra.Convolution`) and `AlgHom.antipode_id_cancel`
  (`Mathlib.RingTheory.HopfAlgebra.Convolution`). Michał Mrugała and Yunzhou
  Xie contributed to the wider Hopf-algebra convolution formalization.

For pinned dependencies, build and focused client commands, see the
[build guide](BUILDING.md). For project-wide authorship and third-party
notices, see [credits](../CREDITS.md).
