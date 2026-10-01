# Unitriangular coordinate base-change coherence

Import `AlgebraicGroups.Algebra.UnitriangularBaseChangeCoherence` for two
equations about `UnitriangularCoordinateRing.baseChange`, the equivalence for the
**actual determinant-localized GL quotient** `CoordinateRing`, not a replacement
polynomial algebra. Both equations are equalities of algebra equivalences.

For a commutative ring `R` and same-universe finite linearly ordered `ι`,
`baseChange_self R ι` identifies extension along the identity with the algebra
tensor unit:

```lean
UnitriangularCoordinateRing.baseChange R R ι =
  Algebra.TensorProduct.lid R (UnitriangularCoordinateRing.CoordinateRing R ι)
```

For arbitrary commutative rings `R`, `S`, `T`, with `[Algebra R S]`,
`[Algebra S T]`, `[Algebra R T]`, `[IsScalarTower R S T]` and the same
finite linearly ordered `ι`, `baseChange_tower R S T ι` equates the two
`T`-algebra equivalences from a scalar-extended double tensor to
`CoordinateRing T ι`:

```lean
(Algebra.TensorProduct.cancelBaseChange R S T T
    (UnitriangularCoordinateRing.CoordinateRing R ι)).trans
    (UnitriangularCoordinateRing.baseChange R T ι) =
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : T ≃ₐ[T] T)
      (UnitriangularCoordinateRing.baseChange R S ι)).trans
    (UnitriangularCoordinateRing.baseChange S T ι)
```

The proofs compare polynomial representatives using the published `freeEquiv`
and `baseChange_tmul_freeEquiv` and mathlib's tensor unit, congruence and
scalar-tower cancellation. Neither law needs flatness, injectivity,
`Nontrivial`, nonempty indices, nor distinct or nonzero base rings. The ordinary
`AlgebraicGroupsTest.Algebra.UnitriangularBaseChangeCoherence` client contains
six examples: both generic equivalence equations; identity over `ZMod 1` and
`Fin 0`; identity over `ℤ` and `Fin 1`; tower through `ZMod 1` at `Fin 1`;
and the nonzero `ℤ → ℚ → ℚ` tower at `Fin 2`.

This module asserts no more general naturality or Hopf, scheme, point or
source-coverage comparison. It builds on the independently importable
[base-change equivalence](../UnitriangularBaseChange/README.md). From this
repository's root, install its pinned Lean toolchain, fetch the matching
mathlib cache successfully, then build both normal library and client targets:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

Formal Frontier Agents and Lattice contributed the quotient comparison;
the existing coordinate presentation retains its own authorship. The proof
reuses mathlib's tensor scalar-extension APIs and the
`MvPolynomial.algebraTensorAlgEquiv` used by the preceding base-change module;
that equivalence is credited there to Antoine Chambert-Loir. External
contributors and licenses remain distinct.
