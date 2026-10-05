# Diagonal and strict upper-triangular coordinates

Import `AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices` directly.
This independent module imports only mathlib and defines equivalences in
namespace `Matrix` for any `[LinearOrder ι]`, without finiteness or
nonemptiness. `upperTriangularIndicesEquiv ι` splits weakly ordered pairs
`{p : ι × ι // p.1 ≤ p.2}` into diagonal indices `ι` and strictly ordered
pairs `{p : ι × ι // p.1 < p.2}`. Its diagonal/strict forward and symmetric
`[simp]` laws and `upperTriangularIndicesEquiv_coordinates` preserve the
underlying coordinate pair.

`upperTriangularRetainedEquiv ι` identifies the retained-entry condition
`¬ p.2 < p.1` with `p.1 ≤ p.2` without changing the pair; its forward and
symmetric `val` laws make this explicit. Composing the equivalences yields
`upperTriangularRetainedIndicesEquiv ι` and symmetric diagonal/strict
coordinate laws. With the additional `[Fintype ι]` assumption,
`card_upperTriangularIndices` and `card_upperTriangularRetainedIndices` count
both index types as `Fintype.card ι + (Fintype.card ι).choose 2`, using mathlib's
strict-pair enumeration. These statements alone assert no coordinate-ring or
scheme dimension; see the separate [native dimension
module](../../../GroupScheme/UpperTriangularDimension/README.md).

The [producer](../UpperTriangularIndices.lean) and [ordinary-import
client](../../../../AlgebraicGroupsTest/LinearAlgebra/Matrix/UpperTriangularIndices.lean)
exercise forward/inverse laws, generic empty indices, and `Fin 0`, `Fin 1`
and `Fin 3`. From this repository's root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices \
  AlgebraicGroupsTest.LinearAlgebra.Matrix.UpperTriangularIndices
```

## References

Lattice introduced the coordinate-preserving indexing equivalences in this
project. The finite strict-pair count reuses Mathlib's
`Fintype.card_product_filter_lt` by Bhavik Mehta and Jon Eugster in
`Mathlib/Data/Fintype/Prod.lean`, which
derives it from `Finset.card_product_filter_lt` in
`Mathlib/Data/Finset/Prod.lean`; the sum count uses `Fintype.card_sum` in
`Mathlib/Data/Fintype/Sum.lean`. None of these cardinality results is needed
for the order-only equivalences.
