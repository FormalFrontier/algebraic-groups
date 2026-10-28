# Hopf base change for canonical unitriangular coordinates

Import `AlgebraicGroups.Algebra.UnitriangularHopfBaseChange`.
`UnitriangularCoordinateRing.baseChangeBialgEquiv` upgrades the algebra comparison on
`TauCeti.UpperUnitriangular.coordinateHopfAlgebra` to the canonical tensor coalgebra structures.
The counit, matrix-product coproduct and antipode formulas are preserved over arbitrary
commutative bases, including empty indices and zero rings. The genuine `Fin 3` product cross
term remains; these are unitriangular groups rather than additive coordinate groups.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/Algebra/UnitriangularHopfBaseChange/README.md) preserves the full context.
Current APIs are described above.

The comparison reuses Christian Merten's mathlib
`MvPolynomial.algebraTensorAlgEquiv`, now implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir contributed the
related earlier `MvPolynomial.scalarRTensorAlgEquiv`. See
[credits](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md) for the distinct project and dependency contributions.

- James S. Milne, *Algebraic Groups* (2017), items 2.8–2.9: the field-case
  matrix-entry coproduct and `U_n` presentation; the Hopf base-change
  comparison here works over arbitrary commutative rings.
- Antoine Chambert-Loir, Mathlib,
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`:
  the related earlier `MvPolynomial.scalarRTensorAlgEquiv`.
- Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`:
  `MvPolynomial.algebraTensorAlgEquiv` supplies the underlying scalar extension.
- Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`:
  `AddMonoidAlgebra.scalarTensorEquiv` implements the polynomial equivalence.
- Amelia Livingston and Andrew Yang, Mathlib,
  `Mathlib.RingTheory.Bialgebra.TensorProduct` and
  `Mathlib.RingTheory.HopfAlgebra.TensorProduct`: the independently defined
  tensor structures on the source.
- Yaël Dillies, Mathlib, `Mathlib.RingTheory.Bialgebra.Equiv`:
  `BialgEquiv.ofAlgEquiv` packages the compatible algebra equivalence.
- Yaël Dillies, Mathlib, `Mathlib.RingTheory.Bialgebra.Convolution`:
  `AlgHom.convMul_comp_bialgHom_distrib`; and
  `Mathlib.RingTheory.HopfAlgebra.Convolution`: `AlgHom.antipode_id_cancel`.
  These identities identify the antipodes. Michał Mrugała and Yunzhou Xie
  contributed to the wider Hopf-algebra convolution formalization.
