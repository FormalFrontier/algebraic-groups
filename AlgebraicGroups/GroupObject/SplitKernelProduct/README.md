<!-- SPDX-License-Identifier: Apache-2.0 -->
# A split group-object kernel as an underlying product

`AlgebraicGroups.GroupObject.SplitKernelProduct` works in any cartesian
monoidal category `C`. It takes objects `N`, `G`, `Q`, group-object structures on
`G` and `Q`, a multiplicative morphism `q : G ⟶ Q`, a **genuine kernel square**
`hN : IsPullback i (toUnit N) q η[Q]` for `i : N ⟶ G`, and an **underlying-object**
section `e : Q ⟶ G` satisfying `he : e ≫ q = 𝟙 Q`. It requires neither a group
structure on `N` nor `IsMonHom e`.

`CategoryTheory.splitKernelProductIso i q e hN he : N ⊗ Q ≅ G` multiplies
**section first, kernel second**. Its forward arrow is
`(snd N Q ≫ e) * (fst N Q ≫ i)`; its inverse is
`lift (splitKernelRemainder i q e hN he) q`, where
`splitKernelRemainder` is the unique `hN.lift` of `(q ≫ e)⁻¹ * 𝟙 G`
and `toUnit G`. The actual category-theoretic projection triangle is
`splitKernelProductIso_hom_comp_q`:
`(splitKernelProductIso i q e hN he).hom ≫ q = snd N Q`.
The useful readbacks are `splitKernelProductIso_hom`,
`splitKernelProductIso_inv_comp_fst`,
`splitKernelProductIso_inv_comp_snd`, and
`splitKernelRemainder_comp_i`. They are morphism equalities, hence apply to
arbitrary test objects, not only geometric points.

To check the normalization, for every `f : T ⟶ G`, multiplicativity of `q`
and `he` imply `((f ≫ q ≫ e)⁻¹ * f) ≫ q = 1`. Its terminal component makes
the kernel lift. On a forward image, the quotient readback is the original
`Q` component, and left cancellation leaves the original kernel component;
`hN.hom_ext` identifies the lifts. Conversely, right after taking the inverse,
`e(q(g)) * (e(q(g))⁻¹ * g) = g` in the group `Hom(T,G)`.

**Scope.** This is an isomorphism of underlying objects, not a direct-product
group-object isomorphism. Even a multiplicative section can induce a twisted
product law, and an arbitrary section need not preserve multiplication at all.
The ordinary-import client in
`AlgebraicGroupsTest.SplitKernelProduct` checks both generic
formulas and a concrete `Type` group-object example: the terminal quotient of
`Multiplicative ℤ`, with section constantly equal to the nonidentity element
`Multiplicative.ofAdd 1`. The client *proves* this section is not `IsMonHom`.

**Existing mathematics and reuse.** The implementation reuses the pinned
mathlib `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` Hom-group laws,
`IsPullback.lift`/`hom_ext`, and `CartesianMonoidalCategory.lift`/`hom_ext`.
The related `AlgebraicGroups.GroupObject.KernelTorsor.isPullback_kernel_mul`
instead presents `N ⊗ G` as `G ×_Q G` and does not supply this section-dependent
`N ⊗ Q ≅ G`. Preadditive split-kernel biproduct results require additive
categories and do not replace this arbitrary-cartesian result. The abstract
construction does not assume or prove determinant or smoothness; the separate
`AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct` specializes it
to the finite determinant. Formalization Worker B authored the original generic
implementation; exact contribution and review records are maintained separately.

## Focused reproduction

With the repository-pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups.GroupObject.SplitKernelProduct AlgebraicGroupsTest.SplitKernelProduct
```

Both modules set `warningAsError true`; the client is registered as a persistent
default root. Passing a focused build alone does not establish complete release
review or proof-integrity verification.
