# Credits and references

**Authors: Formal Frontier Agents.** The original project contributions in
this repository are licensed under [Apache-2.0](LICENSE). The collective
credit identifies contributors, not a verified legal copyright holder.
Formal Frontier's AI agents developed proofs and examples under human project
direction.

Lattice contributed project Lean infrastructure for algebraic groups, group
objects and schemes, including clopen-rank localization. Other Formal Frontier
agent contributions include unitriangular and triangular matrix/group-scheme
constructions, finite GL/SL
geometry and dimension proofs, diagonal products, split kernels and base-change
comparisons. Anchor integrated identity-component, characteristic-morphism,
Artin–Schreier and roots-of-unity work; the original proofs remain credited
to their contributors.

Formal Frontier Agents developed the closed unitriangular-stage Hopf quotients,
native stage schemes, polynomial coordinates and underlying affine-space
comparisons. Distinct agents contributed the Lean implementations and proofs;
Lattice contributed mathematical planning and corrections. This contribution
credit does not claim the underlying unitriangular mathematics originated here.
The focused [stage](AlgebraicGroups/GroupScheme/UnitriangularStages/README.md),
[polynomial](AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md) and
[affine-space](AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace/README.md)
guides record their reusable mathematical interfaces.

Formal Frontier Agents also developed stage normality, primitive positive-stage
coordinates and the underlying over-scheme kernel pullback. Separate
contributors developed the filtration and authored the normality, coordinate and
kernel proofs. The
[normality](AlgebraicGroups/GroupScheme/UnitriangularStageNormality/README.md),
[coordinates](AlgebraicGroups/GroupScheme/UnitriangularStageCoordinates/README.md)
and [kernel](AlgebraicGroups/GroupScheme/UnitriangularStageKernel/README.md)
guides give the respective mathematical interfaces.

Formal Frontier Agents also developed the arbitrary-ring finite additive
product's underlying affine-space comparison and the positive-stage
projection and underlying over-scheme section. Distinct agents contributed
the project Lean constructions and proofs; Lattice contributed mathematical
planning and corrections. The categorical-product, polynomial and affine-Spec
ideas have independent mathematical and formalization antecedents credited
below; original implementation is not a claim of original mathematical invention.
The [product](AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace/README.md)
and [stage-projection](AlgebraicGroups/GroupScheme/UnitriangularStageProjectionBridge/README.md)
guides document these mathematical interfaces.

The proofs reuse mathlib and separately maintained project dependencies; their
contributors and licenses remain distinct. In particular the determinant-section
module retains Chris Birkbeck's authentic 2021 Apache-2.0 notice, and the
finite-free special-linear development uses Antoine Chambert-Loir's Mathlib
`SpecialLinearGroup.baseChange`, `congr_linearEquiv` and
`Matrix.SpecialLinearGroup.toLin_equiv`. Whysoserioushah introduced
`Matrix.GeneralLinearGroup.det_surjective` into Mathlib; this declaration
credit does not assert its first mathematical invention or replace Birkbeck's
notice. Coordinate base change uses Christian Merten's
`MvPolynomial.algebraTensorAlgEquiv`, implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`. Chambert-Loir's earlier
`MvPolynomial.scalarRTensorAlgEquiv` is a related prior formalization, not
the equivalence used for this polynomial comparison.

## Mathematical sources

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field*, Cambridge Studies in Advanced Mathematics 170, Cambridge University
Press, 2017: item 2.1 describes the additive group; item 2.6 gives the
chosen-basis group-scheme isomorphism `Gₐ^n ≃ Vₐ` over a field, a direct
published antecedent for finite additive products; item 2.9 discusses
unitriangular groups, and item 6.49 their filtration. The present comparison
instead identifies the underlying over-scheme of the actual product with
`Spec (MvPolynomial D K)` and affine space over an arbitrary commutative ring;
that result is not attributed to those passages. The field-case filtration
antecedes the closed stages and normality, while it supplies context rather
than attribution for the separate whole-stage underlying projection or its
nonmultiplicative section. Milne's other cited passages concern selected
group-functor, finite-constant, triangular, component, quotient and density
results, not the book as a whole.

The distinct 2012, version 1.00, *Basic Theory of Affine Group Schemes* gives
field-base kernel, determinant, dimension and right-factor splitting
antecedents (XIII §3 **item 3.14**, not an example). The preliminary *Algebraic
Groups* course notes, version 2.00 (2015), give field triangular splitting
and a split-kernel criterion. The Stacks Project supplies the cited affine
groupoid, faithfully-flat descent, localization, reducedness and dimension
ideas; its quotient antecedents do not establish general existence or
effectivity here. The Grinberg–Reiner primitive counit consequence is credited
**as cited by Mathlib**, not as a source for this library's general monoid-algebra primitive
theorem. Formal Frontier's *Alpha-power versus roots of unity: scheme
isomorphism, not group isomorphism* contributes the finite-cyclic
diagonal-coefficient idea. See the [root references](README.md#references) and
module References for their precise locators and limitations.

## Prior formalizations

Prior Lean formalizations include the mathlib community's
[*Mathlib*](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5):
`algΓAlgSpecAdjunction` for affine-Spec/global-section maps,
`MvPolynomial.aeval`, `MvPolynomial.rename` and `MvPolynomial.killCompl` for
free polynomial coordinates and complementary retractions,
`Limits.productIsProduct` and `Grp.forget` for categorical products, and
Andrew Yang's `AffineSpace.SpecIso` for affine-space comparisons. Justus
Springer contributed the distinct affine-space geometric-integrality
instance. Bhavik Mehta and Jon Eugster contributed the Mathlib strict-pair
count used for finite triangular indices. Amelia Livingston and Andrew Yang
contributed tensor-bialgebra/Hopf structures; Yaël Dillies contributed
bialgebra equivalence, convolution and Hopf–Spec constructions. The scalar
comparison credited above also uses Merten's tensor cancellation, and
`Algebra.TensorProduct.lid` uses Kevin Buzzard's Mathlib4 port; Kim Morrison
and Johan Commelin contributed to the wider tensor-product maps module.
Other reused Mathlib APIs include Hopf quotients, matrix determinant
and group-object operations, localization and faithfully flat descent,
connected components, polynomial Krull dimension and standard smoothness.

The separately maintained [*SchemeProperties*](https://github.com/FormalFrontier/scheme-properties)
supplies `FiniteTypePoints` (including restricted-Yoneda and finite-limit
interfaces), `ConnectedComponents`, `ComponentScheme` and `ComponentFibers`.
The separately maintained [*GeneralLinearGroups*](https://github.com/FormalFrontier/general-linear-groups)
supplies `ElementaryCommutator` for the unitriangular point-group arguments.
Their contributors and licenses are separate from this project's original
contributions and Mathlib's. The local `VectorProduct` formalizes the
field/basis group-scheme product as
`vectorGroupSchemeProductIso`; `Additive`, `AffineHomOver`, stage-coordinate
and stage-affine-space modules supply other related project formalizations.
Mathematical citation and authorization to
reproduce an author's expression are separate matters; this bibliography
neither claims permission to republish the book nor its author's endorsement.
See the
[mathematical introduction](README.md) and [formalization metadata](formalization.yaml)
for this library's scope.
