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

## References

- J. S. Milne, [*Basic Theory of Affine Group Schemes*, XIII §3,
  item 3.14](https://www.jmilne.org/math/CourseNotes/AGS.pdf):
  a field-base decomposition using a right-hand diagonal factor. The
  section-first conjugation action and twisted law above have a different
  factor order and are formulated on the arbitrary-base scheme kernel.
- J. S. Milne, *Algebraic Groups*, §§2.8, 2.10(a): field-base GL coordinates
  and mentions of SL, not an all-algebras conjugation formula.
- [SplitKernelSemidirect](../../GroupObject/SplitKernelSemidirect.lean) supplies
  the generic kernel conjugation and section-first twisted multiplication;
  [SpecialLinearKernel](../SpecialLinearKernel.lean) gives the pullback, and
  [GeneralLinearDeterminantSection](../GeneralLinearDeterminantSection.lean)
  supplies the one-pivot section. Mathlib's
  `CategoryTheory/Monoidal/Cartesian/Grp.lean` provides group-object
  conjugation and `Data/Matrix/Mul.lean` its matrix diagonal readbacks.

With the exact pinned toolchain and manifest, fetch the matching mathlib cache
first, then run the two focused warning-fatal targets:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation
lake build AlgebraicGroupsTest.GeneralLinearDeterminantConjugation
```

For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
