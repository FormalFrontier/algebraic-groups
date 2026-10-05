# Hopf base change for unitriangular coordinate rings

Import `AlgebraicGroups.Algebra.UnitriangularHopfBaseChange` to use the
canonical bialgebra comparison for the **actual determinant-localized
unitriangular quotient** of the general-linear coordinate ring. Let `R` and
`S` be commutative rings in the same universe, with `[Algebra R S]`, and let
`ι` be a finite linearly ordered type in that universe. The existing
`UnitriangularCoordinateRing.baseChange R S ι` is an `S`-algebra equivalence

```lean
S ⊗[R] CoordinateRing R ι ≃ₐ[S] CoordinateRing S ι
```

Both sides carry their independently defined canonical Hopf structures: the
tensor-product structure on the source and the quotient structure on the
target. This module neither transports a structure along `baseChange` nor
changes either coordinate ring.

- `UnitriangularCoordinateRing.comul_entry K ι row col` computes the quotient
  coproduct on **every** matrix entry, including diagonal and lower entries:
  `Δ(x(row,col)) = ∑ middle : ι, x(row,middle) ⊗[K] x(middle,col)`.
- `baseChange_counit R S ι` identifies the target counit composed with
  `baseChange` with the source counit as `S`-algebra homomorphisms.
- `baseChange_comul R S ι` identifies the target coproduct composed with
  `baseChange` with source coproduct followed by
  `Algebra.TensorProduct.map baseChange baseChange`, as `S`-algebra
  homomorphisms.
- `baseChangeBialgEquiv R S ι` packages the existing algebra equivalence
  and these two diagrams using `BialgEquiv.ofAlgEquiv`;
  `baseChangeBialgEquiv_apply` identifies its underlying map pointwise.
- `baseChange_antipode R S ι element` says the antipodes of those canonical
  structures intertwine with the original `baseChange` map. The proof uses
  uniqueness of convolution inverses, not a new `HopfEquiv` bundle.

The homomorphism diagrams are proved on the strict-upper polynomial
generators using the actual quotient-entry formulas. For `Fin 3`, the
`(0,2)` coproduct retains the nonprimitive middle term:
`1 ⊗ x₀₂ + x₀₁ ⊗ x₁₂ + x₀₂ ⊗ 1`. The
[ordinary-import client](../../../AlgebraicGroupsTest/Algebra/UnitriangularHopfBaseChange.lean)
checks that formula after an arbitrary ring map, the generic diagrams and
antipode, zero rings with empty/singleton indices, and a nonzero singleton
case. No flatness, injectivity, nontriviality, nonemptiness or extra
base-map compatibility hypothesis is needed. These results do not provide
represented-point or scheme base change, index-reordering or general
naturality, classification or source-specific coverage. See the
[algebra base-change guide](../UnitriangularBaseChange/README.md) for the
underlying equivalence and its entry formulas.

From the repository root, use the pinned Lean toolchain and fetch the
matching precompiled mathlib cache **successfully before** building both
default roots:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```


The comparison reuses Christian Merten's mathlib
`MvPolynomial.algebraTensorAlgEquiv`, now implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir contributed the
related earlier `MvPolynomial.scalarRTensorAlgEquiv`. See
[credits](../../../CREDITS.md) for the distinct project and dependency contributions.

## References

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
