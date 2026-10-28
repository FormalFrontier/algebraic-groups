# Coherence of canonical unitriangular base change

Import `AlgebraicGroups.Algebra.UnitriangularBaseChangeCoherence`.
`UnitriangularCoordinateRing.baseChange_self` and `baseChange_tower` identify the canonical
coordinate-algebra comparison with tensor-unit and scalar-tower cancellation maps. The
statements use Tau Ceti’s polynomial unitriangular Hopf carrier directly and permit arbitrary
commutative bases, empty indices and zero rings. The group-scheme coherence theorem is in
`AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence`.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/Algebra/UnitriangularBaseChangeCoherence/README.md) preserves the full context.
Current APIs are described above.

The proofs compare polynomial representatives using the published `freeEquiv`
and `baseChange_tmul_freeEquiv` and mathlib's tensor unit, congruence and
scalar-tower cancellation. Neither law needs flatness, injectivity,
`Nontrivial`, nonempty indices, nor distinct or nonzero base rings. The ordinary
`AlgebraicGroupsTest.Algebra.UnitriangularBaseChangeCoherence` client contains
six examples: both generic equivalence equations; identity over `ZMod 1` and
`Fin 0`; identity over `ℤ` and `Fin 1`; tower through `ZMod 1` at `Fin 1`;
and the nonzero `ℤ → ℚ → ℚ` tower at `Fin 2`.

Formal Frontier Agents and Lattice contributed the quotient comparison;
the existing coordinate presentation retains its own authorship. The proof
reuses mathlib's tensor scalar-extension APIs and the
`MvPolynomial.algebraTensorAlgEquiv` used by the preceding base-change module;
Christian Merten contributed that equivalence, now implemented using Yaël
Dillies's `AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir contributed
the related earlier `MvPolynomial.scalarRTensorAlgEquiv`. External contributors
and licenses remain distinct.

- James S. Milne, *Algebraic Groups* (2017), item 2.9: the field-case `U_n`
  presentation underlying the coordinate algebra, not these tower laws.
- Antoine Chambert-Loir, Mathlib,
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`: the related earlier
  `MvPolynomial.scalarRTensorAlgEquiv`.
- Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`:
  `MvPolynomial.algebraTensorAlgEquiv` used by the underlying comparison;
  `Mathlib.RingTheory.TensorProduct.Maps`: the tensor cancellation
  `Algebra.TensorProduct.cancelBaseChange` used here.
- Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`:
  `AddMonoidAlgebra.scalarTensorEquiv` implements the polynomial equivalence.
- Kevin Buzzard, Mathlib4 port of `Algebra.TensorProduct.lid`, now in
  `Mathlib.RingTheory.TensorProduct.Maps`.
- Kim Morrison and Johan Commelin, Mathlib: contributors to the wider
  `Mathlib.RingTheory.TensorProduct.Maps` module.
