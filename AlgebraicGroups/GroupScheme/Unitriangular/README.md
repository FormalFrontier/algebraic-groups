# Canonical upper-unitriangular group schemes

Import `TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme`. Use
`TauCeti.UpperUnitriangular.groupScheme` and `coordinateHopfAlgebra` directly, with canonical
`pointsMulEquiv` and `schemePointsMulEquiv` for matrices. The native carrier is
`TauCeti.upperUnitriangularGroup`; entries below the diagonal vanish and diagonal entries equal
one. The canonical polynomial Hopf algebra has matrix-product coproduct, so its group law has
the genuine rank-three cross term. The former external quotient model, wrappers and import
module have been removed. Retained geometry, closed stages and base-change coherence build on
this carrier; empty ranks and zero rings remain covered.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/Unitriangular/README.md) preserves the full context.
Current APIs are described above.

* J. S. Milne, *Algebraic Groups* (2017), §§2.8–2.9: `GL_n` as a functor on
  commutative algebras over a field, and its upper-unitriangular subgroup
  with the unlocalized polynomial-quotient presentation. The group scheme
  here also admits arbitrary commutative base rings and empty indices.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` and
  `Mathlib/LinearAlgebra/Matrix/Block.lean`: matrix units and triangular
  product, inverse and determinant results;
  `Mathlib/RingTheory/HopfAlgebra/Quotient.lean` and
  `Mathlib/RingTheory/Bialgebra/Quotient.lean`: Hopf-ideal quotient machinery.
* `AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` supplies the
  localized GL coordinate algebra and its matrix laws;
  `AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean` supplies the
  earlier comparison between a GL Hopf quotient and a polynomial quotient.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
