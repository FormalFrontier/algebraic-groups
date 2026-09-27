<!-- SPDX-License-Identifier: Apache-2.0 -->
# Conjugation and twisted multiplication on a split group-object kernel

Import `AlgebraicGroups.GroupObject.SplitKernelSemidirect` to work in any
cartesian monoidal category `C`, without assuming enough points or local
smallness. Fix group objects `G`, `Q`, a multiplicative `q : G ⟶ Q`, a
**genuine kernel pullback** `hN : IsPullback i (toUnit N) q η[Q]`, and a
section `e : Q ⟶ G` with `he : e ≫ q = 𝟙 Q`.

`CategoryTheory.splitKernelConj i q e hN he : Q ⊗ N ⟶ N` is the unique
pullback lift of `(e ⊗ₘ i) ≫ GrpObj.conj G`. Its inclusion readback is
`splitKernelConj_comp_i`, and `splitKernelConj_lift_comp_i` says, for
**every** test object `T` and arrows `a : T ⟶ Q`, `n : T ⟶ N`,

```
(lift a n ≫ splitKernelConj i q e hN he) ≫ i
  = (a ≫ e) * (n ≫ i) * (a ≫ e)⁻¹.
```

Neither definition nor readback requires `[GrpObj N]`, `[IsMonHom i]`, or
`[IsMonHom e]`. Its unique terminal projection is
`splitKernelConj_comp_toUnit`. In particular, no product-group structure
is smuggled into the arbitrary-section result in
`AlgebraicGroups.GroupObject.SplitKernelProduct`.

With `[GrpObj N] [IsMonHom i]`, `splitKernelConj_map_mul` and
`splitKernelConj_map_inv` show that conjugation by **each fixed** section
value preserves kernel multiplication and inversion. These statements still
need *no* multiplicativity of `e`. With `[IsMonHom e]`,
`splitKernelConj_one` and `splitKernelConj_mul` express the left-action unit
and composition on arbitrary Hom sets; those two proofs do not require
`[GrpObj N]` or `[IsMonHom i]`. These Hom formulas are natural in every test
object by precomposition, and arise from equalities of actual morphisms.

For the product law additionally assume `[GrpObj N] [IsMonHom i]
[IsMonHom e]`. The underlying-object iso
`F := splitKernelProductIso i q e hN he : N ⊗ Q ≅ G` is **section first**:
`F(n,a) = e(a)*i(n)`. Let `alpha(a,n)` denote restricted conjugation.
`splitKernelProductIso_mul_lift` proves, simultaneously for any four
arrows `n,n' : T ⟶ N`, `a,a' : T ⟶ Q`, that the actual product is

```
F((alpha(a'⁻¹,n)*n'), a*a') = F(n,a)*F(n',a').
```

`splitKernelTwistedMul` is the explicit arrow
`(N ⊗ Q) ⊗ (N ⊗ Q) ⟶ N ⊗ Q` given by those coordinates.
`splitKernelTwistedMul_comp_hom` proves its **morphism-level** compatibility
with the multiplication of `G`, by taking the universal pair of `N ⊗ Q`
coordinates as the test object. This arrow is *not* the canonical
direct-product multiplication `μ[N ⊗ Q]`; the module neither adds a global
transported `GrpObj (N ⊗ Q)` instance nor claims that `F` is an iso of
group objects with the direct-product structure. A caller wishing to
transport a group structure can do so locally with native `GrpObj.ofIso`.

The alternative **kernel-first** convention `K(n,a)=i(n)*e(a)` has
`(n,a)*(n',a')=(n*alpha(a,n'),a*a')`. It is not the coordinate order of
this `F`; do not substitute this formula into
`splitKernelTwistedMul`.

The ordinary-import client
`AlgebraicGroupsTest.SplitKernelSemidirect` checks the
public readbacks. For a real nonabelian case it takes
`H = Equiv.Perm (Fin 3)`, `G = H × H`, `N = Q = H`,
`i(n)=(n,1)`, `q(g₁,g₂)=g₂`, and `e(a)=(a,a)`. It proves the
kernel square using the native Type-pullback criterion and constructs all
three multiplicative arrows using native cartesian projections/lifts. Two
noncommuting swaps show that multiplying the forward images of `(n,1)`
and `(1,a)` is *not* the forward image of their naive direct-product pair
`(n,a)`.

The proof reuses the pinned mathlib `GrpObj.conj`,
`GrpObj.lift_conj_eq_mul_mul_inv`, Hom-group identities, cartesian lifts,
and `IsPullback.lift`/`hom_ext`. The existing
`GrpObj.isPullback_kernel_mul` is a *kernel-pair* result with a different
domain and conclusion; it is not duplicated here. For ordinary Type group
extensions, mathlib already has a kernel-first semidirect-product
equivalence. Future clients may specialize these generic Hom readbacks
without adding a second extension framework. Finite determinant, source
correspondence and coverage are outside this module.

Formalization Worker B authored the original conjugation and twisted-product
implementation and its ordinary-import client. Exact origin and review records
are maintained separately from this mathematical guide.

For a pinned checkout, fetch the matching mathlib cache before checking the
producer and persistent client:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupObject.SplitKernelSemidirect AlgebraicGroupsTest.SplitKernelSemidirect
```

A focused build alone does not establish the complete destination check. The
accepted 125-module destination graph passed its actual default build and
private-inclusive standard-axiom audit (native job 530), with fresh independent
affected review and owner code acceptance. This documentation-only release
candidate keeps those checked inputs but remains unaccepted and unpublished.
