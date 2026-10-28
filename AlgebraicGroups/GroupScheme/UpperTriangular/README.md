# Canonical upper-triangular closed group schemes

Import `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic`. Use
`TauCeti.GeneralLinear.UpperTriangular.groupScheme K N` and its coordinate Hopf algebra
directly, with canonical inclusion into `TauCeti.GeneralLinear.groupScheme K N`. Numerical rank
covers every finite rank, including zero; points use `Fin N`. The duplicate external coordinate
quotient, point packaging and scheme module have been removed. The retained split-kernel and
product modules prove the extra U-first decomposition on these canonical models. General
commutative and zero rings and nonreduced test algebras remain covered.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UpperTriangular/README.md) preserves the full context.
Current APIs are described above.

* J. S. Milne, *Algebraic Groups* (2017), §§2.8–2.9: `GL_n` and the
  upper-triangular subgroup over a field, functorially on commutative
  coefficient algebras. Here the base can be any commutative ring and the
  ordered index set can be empty.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/Block.lean`: triangular matrix
  multiplication, determinant and inverse;
  `Mathlib/RingTheory/HopfAlgebra/Quotient.lean`: the Hopf-ideal quotient;
  `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`:
  `IsClosedImmersion.spec_of_surjective` for the quotient inclusion.
* `AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` and
  `AlgebraicGroups/GroupScheme/GeneralLinear.lean` provide the localized GL
  Hopf algebra and its represented group-point comparison; the native
  triangular inverse and diagonal laws are in
  `AlgebraicGroups/GroupTheory/UpperTriangular.lean`.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
