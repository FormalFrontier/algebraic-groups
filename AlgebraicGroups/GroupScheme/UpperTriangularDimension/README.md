# Native upper-triangular coordinates and dimension

Import `AlgebraicGroups.GroupScheme.UpperTriangularDimension`. For
`[CommRing K] [Fintype ι] [LinearOrder ι]`, the native
`UpperTriangularCoordinateRing.CoordinateRing K ι` is the quotient of the
**actual** determinant-localized general-linear coordinate ring by the
native ideal with generators `if j < i then matrix K ι i j else 0`.
`UpperTriangularCoordinateRing.retainedIndices ι` consists of pairs `(i, j)`
with `¬ j < i`; `ideal_eq_localizedCoordinateIdeal` proves *both inclusions*
between that native ideal and the generic erased-variable ideal.

`UpperTriangularCoordinateRing.localizedPolynomialEquiv` presents the native
quotient as a localization of the polynomial ring on its retained entries:

```lean
UpperTriangularCoordinateRing.CoordinateRing K ι ≃ₐ[K]
  Localization.Away (MvPolynomial.eraseCoordinates K
    (UpperTriangularCoordinateRing.retainedIndices ι)
    (GeneralLinearCoordinateRing.determinant K ι))
```

The `[simp]` lemmas `localizedPolynomialEquiv_entry` and
`localizedPolynomialEquiv_symm_entry` identify the native quotient of each
retained GL entry and its localized polynomial variable in **both** directions.
This presentation needs no field, nonzero determinant image, or positive rank:
zero rings and empty indices are included. It specializes this library's
existing generic coordinate-elimination result rather than redefining it.

`erasedDeterminant_eval_one` evaluates retained diagonal entries at one and
strictly upper entries at zero, producing the identity matrix and determinant
value one. Over a field, this is a *supplied nonvanishing evaluation point*;
the existing finite polynomial-localization theorem then gives
`AlgebraicGeometry.upperTriangularCoordinateRing_ringKrullDim` and
`AlgebraicGeometry.upperTriangularGroupUnderlyingScheme_topologicalKrullDim`:

```lean
((Fintype.card ι + (Fintype.card ι).choose 2 : ℕ) : WithBot ℕ∞)
```

The latter is the dimension of the native affine `Spec`, for **every field**
(including finite fields) and finite ordered `ι` (including `Fin 0`). No
arbitrary-base dimension, generic product-dimension formula or identity-stalk
theorem is asserted. The [producer](../UpperTriangularDimension.lean) and
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularDimension.lean)
exercise zero/empty coordinates and finite- and infinite-field dimensions.
The [index module](../../LinearAlgebra/Matrix/UpperTriangularIndices/README.md)
is separately importable and supplies only its index equivalences and counts.

From this repository's root, install the pinned toolchain and successfully
fetch its matching mathlib cache before the focused build:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices \
  AlgebraicGroups.GroupScheme.UpperTriangularDimension \
  AlgebraicGroupsTest.GroupScheme.UpperTriangularDimension
```

Formal Frontier agents developed this native specialization; the generic
localization and existing GL and upper-triangular presentations retain their
own original authorship.
