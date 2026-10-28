# Geometry of canonical triangular groups

Import `AlgebraicGroups.GroupScheme.FiniteTriangularGeometry`. The multiplicative, split-torus
and upper-triangular models are the canonical Tau Ceti group schemes. The retained geometric
statements concern smooth structure morphisms and geometrically integral fibers over arbitrary
commutative bases, with integral total spaces over domains. Zero rings and empty ranks are
allowed in relative assertions. Total integrality is not asserted over a general base.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/FiniteTriangularGeometry/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), item 2.2: the multiplicative group;
  item 2.9: diagonal, unitriangular and upper-triangular groups over a field;
  item 2.40: field-case triangular coordinate rings and integrality. These
  passages are not cited for the arbitrary-base smoothness or geometric-fiber
  proofs here.
- J. S. Milne, preliminary *Algebraic Groups* course notes, v2.00 (2015),
  Definition 2.20 and Proposition 2.21: the triangular splitting and its
  split-kernel criterion over a field. These locators are not item 2.9 of the
  2017 book; the isomorphism used here is of underlying over-schemes, not group
  products.
- Mathlib, `Mathlib.RingTheory.Smooth.StandardSmooth` (polynomial localization),
  `Mathlib.RingTheory.TensorProduct.MonoidAlgebra` (field scalar extension),
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` and
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (geometric fibers).
  The local `DiagonalProduct`, `UnitriangularGeometry`, `UpperTriangularSplitKernel`,
  `GroupObject.SplitKernelProduct` and `Scheme.Smooth` modules provide separate
  previously formalized ingredients; see [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md) for
  their contributor credit.
