# Dimension of canonical general and special linear groups

Import `AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension`. The canonical carriers are
`TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)` and
`TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)`. Over every field their ring
and scheme dimensions are `N ^ 2` and `N ^ 2 - 1`, with natural subtraction before casting and
rank zero treated explicitly. The retained SL polynomial hypersurface presentation and canonical
Mathlib/Tau Ceti height and localization results supply the proofs; the removed local
rational-point-height helper is not an import API.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/GeneralSpecialLinearDimension/README.md) preserves the full context.
Current APIs are described above.

* J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field* (Cambridge University Press, 2017), §2.8, gives the finite
  field-base determinant-localized GL presentation and mentions SL; it does
  not supply this proof of dimensions for all fields, including rank zero.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), XI §16,
  Example 16.3, computes the positive-rank field-base dimension of SL.
* The [mathlib formalization](https://github.com/leanprover-community/mathlib4)
  supplies `Polynomial.height_eq_height_add_one` and
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` in
  `RingTheory/KrullDimension/Polynomial`,
  `Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors` in
  `RingTheory/KrullDimension/Regular`, and the prime-spectrum dimension
  bridge. This library's `MvPolynomial.height_ker_eval` specializes those
  height ingredients; `GeneralLinearCoordinateRing.quotientEquiv` and
  `SpecialLinearCoordinateRing.polynomialEquiv` identify the actual rings.
