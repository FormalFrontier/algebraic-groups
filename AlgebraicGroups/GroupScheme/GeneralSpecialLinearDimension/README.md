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
dimension as the field. The existing published `quotientEquiv` and
`polynomialEquiv` transfer those calculations to the genuine localized GL
and Hopf-quotient SL coordinate rings. The prime-spectrum dimension theorem
then gives the actual underlying-scheme dimensions.

## Usage and status

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

The incubator origin and original source-only transfer were independently
reviewed. The combined 130-module destination graph is now accepted on main
after fresh affected review and successful native job 533 default build and
complete private-inclusive standard-axiom audit. The documentation-only
release candidate retains those checked inputs but is unaccepted and
unpublished. Public-import client examples cover arbitrary fields, ranks
zero/one/two and `ZMod 2`. No source-coverage decision follows.

## Provenance and rights

Original code and documentation by Formal Frontier Agents, Apache-2.0.
Author: Hive Task `hive-request-020720d1eb5fc515621730cc4e303793d7178919`
(UID `add4b4bc-9720-4317-9f70-308e77b22c36`, Forgejo worker-b).
The earlier API investigation and proof plan were contributed by Hive Task
`hive-request-495409ddb864bb2a4c42d577e7ee9d2b19e474d5`
(UID `b4c67a11-087b-42ac-bfa7-55dcc856c070`). A separate Worker B
execution prepared this destination import and client-namespace transfer without
changing the proofs. The implementation was accepted in the incubator and now
uses this library's existing GL/SL coordinate presentations, Lean
`leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`.
Underlying mathlib and existing AlgebraicGroups work retains its own
Apache-2.0 attribution. No source-specific passage or coverage claim is made.
