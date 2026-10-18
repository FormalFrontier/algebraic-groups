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
stage schemes, polynomial coordinates and underlying affine-space
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

Formal Frontier Agents developed the field subcoalgebra carrier, restricted
coalgebra structure, bundled inclusion and homomorphism factorization, finite
subcoalgebra containment and the supported diagonal example. The finite
containment construction uses the coefficient-coalgebra and split-tensor
coordinate arguments in this library. These are project Lean implementations
of classical coalgebra mathematics, not claims of mathematical invention.

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

The idempotent principal ideal coalgebra uses Ali Ramsey and Eric Wieser’s
Mathlib coalgebra laws and Finsupp coalgebra, Christopher Hoskin’s idempotent
predicate API, and Mathlib’s ideal and tensor-product interfaces. Formal
Frontier Agents contributed its construction and characteristic formulas.
The counit surjectivity criterion for faithful scalar action and finitely
generated image uses Mario Carneiro and Kevin Buzzard’s Mathlib theorem on
idempotent finitely generated ideals, together with Mathlib’s singleton-ideal
action and faithful-action APIs; finite generation concerns the actual counit
image ideal, not the ambient module. The weak tensor range-product formula
uses Mathlib's `TensorProduct.range_map` and `Submodule.mulMap_range`; counit
surjectivity iff both factor counits are surjective uses `LinearMap.range_eq_top`,
`Ideal.isUnit_iff` and `IsUnit.mul_iff`, without coalgebra laws. For lawful
coalgebras, the faithfully flat forward criterion combines the counit-law action
with Mathlib's `Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top`; the converse
uses the CoherentModules constructor credited below.
Counit ideals under scalar extension use Amelia Livingston and Andrew Yang’s
Mathlib tensor-product coalgebra, Antoine Chambert-Loir’s tensor-range theorem,
and Mathlib’s submodule scalar-extension and ideal-image APIs.

## Mathematical sources

M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, is credited
bibliographically for the classical field coalgebra theorem and
coefficient-coalgebra method. Formal Frontier Agents developed the coalgebra
proofs and examples using Mathlib's coalgebra laws, tensor-product maps and
basis decompositions, linear extensions and finitely generated submodule APIs.
The projective-ambient-module commutative-semiring right-coideal step is distinct
from the field theorem's two-factor tensor-image closure. Its global-splitting
argument follows Formal Frontier's earlier projective-coalgebra formalization
and uses Kevin Buzzard and Antoine Labelle's Mathlib projective-module API in
place of an ambient basis.

These are selected mathematical antecedents and prior formalizations, not
claims to cover entire sources. Module References and the focused guides give
the precise passage-to-construction distinctions.

- M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969: bibliographic credit
  for classical comodules, the field coalgebra theorem and the coefficient method.
  The commutative-semiring containment results use projectivity of the coacting
  coalgebra, not of the coacted-on module. The regular case gives the
  right-coideal step, not a general two-factor semiring theorem.
- J. S. Milne, *Abelian Varieties*, version 2.0 (March 16, 2008), proof of
  Corollary 1.4, printed p. 9: the inversion criterion motivates the statement
  for arbitrary Cartesian group objects in
  `AlgebraicGroups.GroupObject.Commutative`; the arbitrary-category statement
  is a categorical extension, not a statement attributed to that source.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field*, Cambridge Studies in Advanced Mathematics 170, Cambridge
  University Press, 2017. Items 2.1 and 2.6 describe the additive group and
  the chosen-basis `Gₐ^n ≃ Vₐ` group-scheme isomorphism **over a field**, a
  direct antecedent for finite additive products; the comparison here is of
  their underlying over-scheme with affine space over an arbitrary commutative
  ring, not an additive-group-scheme or Hopf isomorphism. Item 2.3 concerns
  finite constant groups; their points here have locally constant labels, not
  unrestricted constant labels. Selected passages on group functors, matrix
  and triangular groups, components, quotients and schematic density also
  inform the corresponding modules. Items 2.9 and 6.49 describe the
  field-case unitriangular group and its finer one-entry filtration: the
  block endpoints antecede closed whole-superdiagonal stages over arbitrary
  rings, but these passages give only context for the separate whole-stage
  *underlying over-scheme* projection and its nonmultiplicative section.
  The fundamental theorem of coalgebras over a field is also a mathematical
  antecedent for the finite-containment API.
- J. S. Milne, *Basic Theory of Affine Group Schemes* (2012, version 1.00;
  [author's course-notes address](https://www.jmilne.org/math/CourseNotes/AGS.pdf),
  which may serve a later version). VII §4 Proposition 4.1 and Example 4.3
  give field-kernel/determinant antecedents, XI §16 Example 16.3 the field
  positive-rank special-linear dimension, and XIII §3 **item 3.14** a
  field-base *right*-diagonal determinant splitting. The represented
  arbitrary-ring left-normalized section-first product has a twisted group
  law, not a direct-product splitting; its kernel and scheme-level laws require
  separate arguments.
- J. S. Milne, preliminary *Algebraic Groups* course notes, version 2.00
  (2015), Definition 2.20 and Proposition 2.21: field-base triangular
  splitting and its split-kernel criterion. These locators belong to the 2015
  preliminary notes, not the 2017 book; neither source is cited here for an
  arbitrary-base group-scheme splitting.
- The Stacks Project: [tags 022W](https://stacks.math.columbia.edu/tag/022W)
  and [022X](https://stacks.math.columbia.edu/tag/022X) for general linear
  coordinates and determinant; [03BH](https://stacks.math.columbia.edu/tag/03BH),
  [03BI](https://stacks.math.columbia.edu/tag/03BI) and
  [03BM](https://stacks.math.columbia.edu/tag/03BM) for affine groupoid
  integrality, invariant rank and the setting of a conditional quotient bridge,
  not full quotient existence or effectivity. Section 26.17, Lemma 26.17.2
  concerns affine pullbacks; [03C4](https://stacks.math.columbia.edu/tag/03C4)
  finite-presentation descent, [02C8](https://stacks.math.columbia.edu/tag/02C8)
  localization,
  [033B](https://stacks.math.columbia.edu/tag/033B) reducedness,
  [056V](https://stacks.math.columbia.edu/tag/056V) dense smooth loci, and
  [00OP](https://stacks.math.columbia.edu/tag/00OP) and
  [0B7I](https://stacks.math.columbia.edu/tag/0B7I) dimension arguments.
- Darij Grinberg and Victor Reiner, *Hopf algebras in combinatorics* (2020),
  Proposition 1.4.17, **as cited by Mathlib** for the primitive counit
  consequence. The general monoid-algebra primitive-vanishing theorem is
  proved separately in [this library](AlgebraicGroups/Algebra/MonoidAlgebraPrimitive.lean).
- P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor Categories* (2015),
  as referenced by Mathlib's primitive module for skew-primitive terminology;
  this is bibliographic attribution through Mathlib, not a claim to have
  formalized a particular book passage.
- Formal Frontier, *Alpha-power versus roots of unity: scheme isomorphism,
  not group isomorphism*, § “No group-scheme isomorphism for positive
  exponent”: a finite-cyclic diagonal-coefficient argument developed further
  in the [primitive module](AlgebraicGroups/Algebra/MonoidAlgebraPrimitive.lean)
  and [client](AlgebraicGroupsTest/MonoidAlgebraPrimitive.lean). An algebra
  equivalence alone does not give an additive-group-scheme or Hopf equivalence.
- The mathlib community, [*Mathlib*](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5):
  coalgebra laws and tensor-basis decompositions, affine spectra, group objects
  and Hopf quotients, tensor and polynomial
  coordinates, categorical products, affine space, dimension and smoothness
  APIs used by the constructions here. See [credits](CREDITS.md) for specific
  interfaces and contributor roles.
- Formal Frontier's separately maintained [*SchemeProperties*](https://github.com/FormalFrontier/scheme-properties)
  for the finite-type restricted functor of points and connected-component,
  component-scheme and component-fibre APIs used here.
- Formal Frontier's separately maintained [*GeneralLinearGroups*](https://github.com/FormalFrontier/general-linear-groups)
  for `ElementaryCommutator`, used in the elementary-unit arguments for the
  unitriangular lower and derived series of **point groups**.

## Prior formalizations

The group-object trivial-kernel criterion combines Andrew Yang's Mathlib Hom-group
and postcomposition interfaces with `MonoidHom.ker_eq_bot_iff` from Kexing Ying's
kernel formalization and Mathlib's pullback and limit-comparison APIs. Its symmetric-group
example uses Kim Morrison's monoid-object construction in `Type` and Markus Himmel's
group-object extension, rather than separate group-object structures.

The Hopf coefficient matrix unit adapts Mathlib's `Coalgebra.Repr` and its
finite-sum antipode identities, using the matrix and units interfaces. Formal
Frontier Agents developed the two inverse proofs, unit construction and
integer-weight and empty-index examples on Mathlib's monoid-algebra Hopf structure.

The split-free-presentation tensor coordinates reuse Jakob von Raumer's Mathlib
`TensorProduct.equivFinsuppOfBasisRight` and its coefficient and inverse formulas,
Johannes Hölzl's Finsupp basis, and Kevin Buzzard and Antoine Labelle's
projective-module formalization. Tensoring linear maps uses Kenny Lau and Mario
Carneiro's Mathlib interfaces. The nonfree examples also use Eric Wieser's
Finsupp/DFinsupp equivalence and Mathlib's direct-sum projectivity and finiteness
criteria. Formal Frontier's earlier coefficient-coalgebra formalizations inform
the split-presentation argument and the idempotent-ideal examples. The mathematical
coefficient method is credited to M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin,
1969; these pure tensor-coordinate lemmas do not assert a coalgebra finiteness theorem.

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
Antipode involutivity uses the convolution group of algebra homomorphisms
from Mathlib's `HopfAlgebra.Convolution`, by Yaël Dillies, Michał Mrugała
and Yunzhou Xie, with Monica Omar's `WithConv` and Mathlib's group-inversion
API. Kim Morrison's categorical commutative-Hopf-object antipode identity
is a related prior formalization; the semiring algebra theorem here extracts
the identity directly from the existing convolution group. Its group-algebra
examples use Amelia Livingston's canonical Hopf instance and antipode formula.
Antipode reversal of comultiplication follows Kim Morrison's categorical
Hopf-object convolution inverse-uniqueness strategy and reuses the concrete
`LinearMap.comul_right_inv` of Dillies, Mrugała and Xie. The balanced-tensor
contraction uses Kenny Lau and Mario Carneiro's tensor maps, associators and
permutations, with Ali Ramsey and Eric Wieser's coalgebra laws.
The ordered group-like difference and ordinary-translation examples reuse
Robert Hawkins's skew-primitive formalization and Yaël Dillies and Michał
Mrugała's group-like formalization. Their monoid-algebra coalgebra and bialgebra
structures are by Amelia Livingston, Dillies and Mrugała; the module and basis
APIs are by Johannes Hölzl, Yury Kudryashov and Kim Morrison, and the non-finiteness
argument uses Johan Commelin's finite-module API.
Other reused Mathlib APIs include Hopf quotients, matrix determinant
and group-object operations, localization and faithfully flat descent,
connected components, polynomial Krull dimension and standard smoothness.

The coalgebra constructions reuse Mathlib's `Submodule`, `TensorProduct.mapIncl`,
`LinearMap.codLift`, `LinearMap.codRestrict` and `CoalgHom` interfaces. Field
freeness and tensor-inclusion injectivity use its vector-space and flat-module
APIs. The coefficient argument uses `TensorProduct.equivFinsuppOfBasisRight`
and projective free-presentation splittings; `Module.Finite.iff_fg` relates
submodule finite generation to finite dimension. The supported diagonal example
uses Mathlib's Finsupp coalgebra and `Finsupp.supportedEquivFinsupp`.

The separately maintained [*SchemeProperties*](https://github.com/FormalFrontier/scheme-properties)
supplies `FiniteTypePoints` (including restricted-Yoneda and finite-limit
interfaces), `ConnectedComponents`, `ComponentScheme` and `ComponentFibers`.
The separately maintained [*GeneralLinearGroups*](https://github.com/FormalFrontier/general-linear-groups)
supplies `ElementaryCommutator` for the unitriangular point-group arguments.
The separately maintained [*CoherentModules*](https://github.com/FormalFrontier/coherent-modules)
supplies `Module.FaithfullyFlat.of_surjective` for the converse counit
characterization of faithfully flat coalgebras. Its general module-theoretic
criterion uses Mathlib's ideal scalar-action and submodule-map interfaces,
with Mathlib's `Module.FaithfullyFlat.self` for the scalar target and the given
flatness of the source coalgebra carrier.
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
