# Integral geometry on canonical GL and SL

Import `AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral`. The proofs use the
canonical Tau Ceti GL and SL Hopf algebras and named group schemes directly. Retained
mathematics gives the SL domain result over arbitrary integral bases, total-space integrality
for GL and SL over domains, and geometrically integral structure morphisms over every
commutative base. Canonical scalar-extension APIs replace duplicate base-change presentations.
Empty ranks and zero-ring relative fibers are included; no total integrality over an arbitrary
non-domain base is claimed.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/GeneralSpecialLinearGeometricIntegral/README.md) preserves the full context.
Current APIs are described above.

* If `K` is a commutative integral domain, the existing
  `GeneralLinearCoordinateRing.CoordinateRing K n` and
  `SpecialLinearCoordinateRing.CoordinateRing K n` have `IsDomain` instances.
  The total spaces `(generalLinearGroupUnderlyingScheme K n).left` and
  `(specialLinearGroupUnderlyingScheme K n).left` have `IsIntegral` instances.
* For **every** commutative ring `K`, the genuine structure morphisms
  `(generalLinearGroupUnderlyingScheme K n).hom` and
  `(specialLinearGroupUnderlyingScheme K n).hom` have
  `GeometricallyIntegral` instances. In particular, every base change to a
  field algebra has an integral scheme as its fiber. Mathlib's native
  instances then provide geometric irreducibility and reducedness; no
  extra rank, field, domain, characteristic or nonzero-base hypothesis is
  imposed on the geometric statement.

The argument uses mathlib polynomial, localization, tensor and geometric-fiber
APIs and this library's previously defined finite coordinate rings and
normalization section. Its original project contributors are credited in the
[credits](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).

* J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field* (Cambridge University Press, 2017), §2.8, gives the finite
  field-base GL determinant localization; §2.42 proves that the coordinate
  ring of positive-rank SL over a field is a domain using a right-diagonal
  splitting. The results here additionally cover coordinate-ring domains over
  integral bases and geometric integrality of the structure morphisms over
  any commutative base, including the zero ring.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), XIII §3,
  item 3.14, gives a right-diagonal determinant splitting for positive
  rank; the algebra section used here instead follows the left normalization
  constructed in `GeneralSpecialLinearSmooth`.
* The [mathlib formalization](https://github.com/leanprover-community/mathlib4)
  supplies `Localization.Away.isDomain` for GL and
  `MvPolynomial.algebraTensorAlgEquiv` and
  `IsLocalization.Away.tensorProductEquivTMulRight` for field extension.
  `GeometricallyIntegral` and `pullbackSpecIso` identify the resulting domain
  proofs with geometric fibers. The determinant-map identity and the tensor
  splitting of SL are established explicitly here, not inferred from
  arbitrary injectivity or a generic base-change assertion.
