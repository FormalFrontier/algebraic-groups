# Dimensions of finite general and special linear group schemes

`AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension` (also available
through `AlgebraicGroups`) computes the Krull
dimensions of the *actual* finite-rank general and special linear coordinate
rings supplied by `AlgebraicGroups`, and the topological Krull dimensions of
their affine underlying schemes. The separate
`AlgebraicGroups.Algebra.PolynomialRationalPointHeight` module proves a reusable
evaluation-kernel height formula.

## Hypotheses and results

For an arbitrary field `K`, finite type `n` with decidable equality, and
`N = Fintype.card n`:

| Object | Dimension (`WithBot ℕ∞`) |
| --- | --- |
| `GeneralLinearCoordinateRing.CoordinateRing K n` | `N ^ 2` |
| `SpecialLinearCoordinateRing.CoordinateRing K n` | `N ^ 2 - 1` |
| `(generalLinearGroupUnderlyingScheme K n).left` | `N ^ 2` |
| `(specialLinearGroupUnderlyingScheme K n).left` | `N ^ 2 - 1` |

Subtraction occurs **in natural numbers before casting**: when `N = 0`, both
coordinate rings and both schemes have dimension zero. The statements do not
assume algebraic closure, characteristic zero or positive rank. In the helper,
`K : Type u` and `σ : Type v` may have different universes; only `[Field K]`
and `[Fintype σ]` are required, not `[DecidableEq σ]`:

```lean
MvPolynomial.height_ker_eval K σ (a : σ → K) :
  (RingHom.ker (MvPolynomial.eval a)).height = (Fintype.card σ : ℕ∞)
```

The public theorems are
`AlgebraicGeometry.generalLinearCoordinateRing_ringKrullDim`,
`AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim`,
`AlgebraicGeometry.generalLinearGroupUnderlyingScheme_topologicalKrullDim`,
and `AlgebraicGeometry.specialLinearGroupUnderlyingScheme_topologicalKrullDim`.

## Proof outline

Finite induction on variables transports evaluation ideals through
`MvPolynomial.renameEquiv` and `MvPolynomial.optionEquivLeft`. The maximal
ideal of an evaluation at one additional variable lies over the previous
maximal ideal, so `Polynomial.height_eq_height_add_one` calculates its height.
In zero variables the polynomial ring is equivalent to the field.

At the identity matrix, the generic determinant evaluates to one, producing
a full-height maximal ideal containing the hypersurface equation. For GL the
equation `det * X - 1` is nonzero even in rank zero (evaluate `X` at zero);
for positive-rank SL the equation `det - 1` is nonzero (evaluate the matrix
at zero). The conditional nonzerodivisor hypersurface theorem then computes
each quotient dimension. The rank-zero SL proof is separate: its determinant
is one and its defining ideal is bottom, so its coordinate ring has the same
dimension as the field. The existing `quotientEquiv` and
`polynomialEquiv` transfer those calculations to the genuine localized GL
and Hopf-quotient SL coordinate rings. The prime-spectrum dimension theorem
then gives the actual underlying-scheme dimensions.

## Usage

```lean
import AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension

example (K : Type) [Field K] :
    ringKrullDim (SpecialLinearCoordinateRing.CoordinateRing K (Fin 2)) =
      (3 : WithBot ℕ∞) := by
  simpa using AlgebraicGeometry.specialLinearCoordinateRing_ringKrullDim K (Fin 2)
```

With the pinned Lean toolchain and dependencies, first fetch the matching
precompiled mathlib cache, then build these focused targets:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build AlgebraicGroups.Algebra.PolynomialRationalPointHeight
LEAN_NUM_THREADS=1 lake build AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension
LEAN_NUM_THREADS=1 lake build AlgebraicGroupsTest.GeneralSpecialLinearDimension
```


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).

## References

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
