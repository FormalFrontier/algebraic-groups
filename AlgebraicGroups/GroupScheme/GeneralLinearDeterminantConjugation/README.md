# Diagonal conjugation of the finite determinant-one group

For any commutative base ring `K`, finite decidable matrix index type `n` and
chosen `pivot : n`, `AlgebraicGeometry.generalLinearDeterminantConj K n pivot`
is an **actual arrow in** `Over (Spec (.of K))`:

```lean
multiplicativeGroupUnderlyingScheme K ⊗ specialLinearGroupUnderlyingScheme K n ⟶
  specialLinearGroupUnderlyingScheme K n
```

It restricts conjugation by the one-pivot determinant section to the genuine
determinant-one kernel. Its definition uses the existing
`specialLinearDeterminantSquare_isPullback_over` and
`generalLinearDeterminantSectionSchemeHom` with the generic
`splitKernelConj`. The pullback, rather than a characterization only on affine
points, defines this arrow for arbitrary test schemes. The generic
`splitKernelConj_one`, `splitKernelConj_mul` and `splitKernelConj_map_mul`
describe its internal left-action behavior; no new action framework is needed.

For every commutative `K`-algebra `R`, unit `t : Rˣ` and native
`A : Matrix.SpecialLinearGroup n R`, theorems
`generalLinearDiagonalConjSL_toGL` and `generalLinearDeterminantConj_point`
identify its affine point with the native determinant-one conjugate whose GL
readback is `D(t) * toGL(A) * D(t)⁻¹`. This comparison uses the existing
`multiplicativeGroupMulEquivPoints`, `specialLinearGroupMulEquivPoints`,
`generalLinearGroupMulEquivPoints`, `generalLinearDeterminantSection_point`
and `specialLinearInclusion_point` for **every** coefficient algebra. Equality
of points at `R = K` alone would not establish a morphism equality; the arrow
has already been defined using the categorical pullback. The construction does
not assume enough points or replace the genuine kernel by a pointwise one.

Set `dᵢ(t) = t` if `i = pivot` and `1` otherwise, *in* `Rˣ`, as implemented by
`generalLinearConjDiagonalUnit`. The native entry theorem
`generalLinearDiagonalConjSL_apply` states, for any indices `i,j`, that

```text
conjSL(t, A)ᵢⱼ = (↑dᵢ(t) : R) * Aᵢⱼ * (↑(dⱼ(t)⁻¹) : R).
```

The inverse is formed in `Rˣ` **before** coercing to `R`. Its proof uses the
diagonal section and its inverse through `generalLinearDiagonalHom`
as a monoid hom, plus `Matrix.diagonal_mul` and `Matrix.mul_diagonal`. No
field, domain, nontriviality, characteristic, or reducedness assumption is
required. Rank one and the zero ring remain valid; an explicit pivot excludes
rank zero, whose determinant has no such arbitrary-base diagonal section.

The separate product trivialization `generalLinearDeterminantProductIso` uses
**section-first** coordinates `F(s,t) = D(t) * toGL(s)` and is an isomorphism
of underlying schemes, not of canonical direct-product group objects. The
generic `splitKernelProductIso_mul_lift` gives its twisted multiplication:

```text
F(s,t) * F(s',t') = F(alpha(t'⁻¹,s) * s', t*t')
```

Here `alpha` is the present conjugation action; the factor is neither
`alpha(t,s')` nor the ordinary direct-product law. The ordinary-import
`AlgebraicGroupsTest.GeneralLinearDeterminantConjugation` client uses
the rank-two upper unipotent over `ZMod 5`: the column pivot with `t = 2`
scales its upper-right entry by the inverse `3`, while the row pivot scales
it by `2`.

The APIs reuse pinned mathlib and this library's determinant section, actual
kernel, product and split-kernel constructions. Formalization Worker B authored
the original conjugation implementation and ordinary-import client. Exact origin
and review records are maintained separately from this mathematical guide.

With the exact pinned toolchain and manifest, fetch the matching mathlib cache
first, then run the two focused warning-fatal targets:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation
LEAN_NUM_THREADS=1 lake --wfail build AlgebraicGroupsTest.GeneralLinearDeterminantConjugation
```

A focused build alone does not establish the complete destination check. The
accepted 125-module destination graph passed its actual default build and
private-inclusive standard-axiom audit (native job 530), with fresh independent
affected review and owner code acceptance. This documentation-only release
candidate keeps those checked inputs but remains unaccepted and unpublished.
