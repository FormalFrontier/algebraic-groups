# Base change for canonical unitriangular coordinates

Import `AlgebraicGroups.Algebra.UnitriangularBaseChange`. For arbitrary same-universe
commutative rings `R → S` and finite linearly ordered `ι`,
`UnitriangularCoordinateRing.baseChange` identifies `S ⊗[R]
TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι` with
`TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι` as `S`-algebras. The canonical coordinate
algebra is already polynomial on strict upper pairs; there is no duplicate GL quotient or
comparison to an old coordinate model. Coefficient, presentation and all-entry formulas include
empty indices and zero rings. Hopf and scheme comparisons and their identity/tower laws are
separate modules.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/Algebra/UnitriangularBaseChange/README.md) preserves the full context.
Current APIs are described above.

The equivalence transports mathlib's `MvPolynomial.algebraTensorAlgEquiv`
through the strict-upper polynomial presentation of this quotient; it does not
replace the quotient with a new definition. `baseChange_presentation` describes
the presentation square, and `baseChange_tmul_freeEquiv` gives the formula on
polynomial representatives. `baseChange_tmul_one` and
the general `AlgEquiv.commutes` law describe coefficients in both directions. `baseChange_tmul_entry` and
`baseChange_symm_entry` cover every quotient matrix entry, including diagonal
and lower entries. No flatness, injectivity, nontriviality or nonempty-index
assumption is needed.

Formal Frontier Agents and Lattice contributed the comparison; the existing
coordinate presentation retains its own authorship. The reused mathlib
`MvPolynomial.algebraTensorAlgEquiv` was contributed by Christian Merten; its
current implementation uses Yaël Dillies's `AddMonoidAlgebra.scalarTensorEquiv`.
Antoine Chambert-Loir contributed the related earlier
`MvPolynomial.scalarRTensorAlgEquiv`.

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
