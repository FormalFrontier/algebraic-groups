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

This module alone proves an algebra comparison, not Hopf or scheme base change,
geometry or a dimension statement. Identity and scalar-tower coherence for this
comparison are in the separate [coherence module](../UnitriangularBaseChangeCoherence/README.md).
The [producer](../UnitriangularBaseChange.lean)
and [ordinary-import client](../../../AlgebraicGroupsTest/Algebra/UnitriangularBaseChange.lean)
include `Fin 0`, `Fin 1`, lower entries and `ZMod 1` cases.

From this repository's root, install the pinned toolchain and fetch the matching
mathlib cache successfully before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

Formal Frontier Agents and Lattice contributed the comparison; the existing
coordinate presentation retains its own authorship. The reused mathlib
`MvPolynomial.algebraTensorAlgEquiv` was contributed by Christian Merten; its
current implementation uses Yaël Dillies's `AddMonoidAlgebra.scalarTensorEquiv`.
Antoine Chambert-Loir contributed the related earlier
`MvPolynomial.scalarRTensorAlgEquiv`.

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.9: the polynomial
  presentation of `U_n` over a field is the coordinate antecedent, not a
  statement of this arbitrary-base scalar-extension equivalence.
- Antoine Chambert-Loir, Mathlib,
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`:
  the related earlier `MvPolynomial.scalarRTensorAlgEquiv`.
- Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`:
  `MvPolynomial.algebraTensorAlgEquiv` and its entry lemmas supply the
  scalar-extension step.
- Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`:
  `AddMonoidAlgebra.scalarTensorEquiv` underlies the polynomial equivalence.
