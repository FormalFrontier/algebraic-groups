# Base change for unitriangular coordinate algebras

Import `AlgebraicGroups.Algebra.UnitriangularBaseChange` to extend scalars in
the **actual determinant-localized GL quotient** defining the unitriangular
coordinate algebra. For commutative rings `R`, `S` with `[Algebra R S]` and a
finite linearly ordered index type `ι`, all in the same universe, the comparison
is an `S`-algebra equivalence:

```lean
UnitriangularCoordinateRing.baseChange R S ι :
  S ⊗[R] UnitriangularCoordinateRing.CoordinateRing R ι ≃ₐ[S]
    UnitriangularCoordinateRing.CoordinateRing S ι
```

The equivalence transports mathlib's `MvPolynomial.algebraTensorAlgEquiv`
through the strict-upper polynomial presentation of this quotient; it does not
replace the quotient with a new definition. `baseChange_presentation` describes
the presentation square, and `baseChange_tmul_freeEquiv` gives the formula on
polynomial representatives. `baseChange_tmul_one` and
`baseChange_symm_algebraMap` describe coefficients. `baseChange_tmul_entry` and
`baseChange_symm_entry` cover every quotient matrix entry, including diagonal
and lower entries. No flatness, injectivity, nontriviality or nonempty-index
assumption is needed.

This is an algebra comparison, not Hopf or scheme base change, tower coherence,
geometry or a dimension statement. The [producer](../UnitriangularBaseChange.lean)
and [ordinary-import client](../../../AlgebraicGroupsTest/Algebra/UnitriangularBaseChange.lean)
include `Fin 0`, `Fin 1`, lower entries and `ZMod 1` cases.

From this repository's root, install the pinned toolchain and fetch the matching
mathlib cache successfully before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups AlgebraicGroupsTest
```

Formal Frontier Agents and Lattice contributed the comparison; the existing
coordinate presentation retains its own authorship. The reused mathlib
scalar-extension equivalence was contributed by Antoine Chambert-Loir.
