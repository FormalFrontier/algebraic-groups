# Common zeros over an algebraically closed field

Import `AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero`. All three theorems are
in `MvPolynomial`, accept independent universes for a field `K`, finite variable
type `σ` and finite equation type `ι`, and assume `[Field K] [IsAlgClosed K]`
and `[Fintype σ] [Fintype ι]`. Equations are an arbitrary family
`f : ι → MvPolynomial σ K`; a zero is a **K-valued tuple** `x : σ → K`.
There is no required decidable equality, distinctness or nonzero equation.

* `card_le_card_of_unique_common_zero f a` assumes
  `∀ x, (∀ i, eval x (f i) = 0) ↔ x = a` and proves
  `Fintype.card σ ≤ Fintype.card ι`. It needs no homogeneity.
* `exists_common_zero_ne f a` assumes `Fintype.card ι < Fintype.card σ`
  and `∀ i, eval a (f i) = 0`, and yields one tuple `x ≠ a` satisfying
  **all** equations. The known point is essential for arbitrary equations:
  a nonzero constant equation can have no zeros at all.
* `exists_nonzero_common_zero_of_isHomogeneous f d` assumes the same strict
  cardinality bound, `d : ι → ℕ`, `∀ i, 0 < d i` and
  `∀ i, (f i).IsHomogeneous (d i)`. It yields a nonzero common zero.
  The positive labels may differ and need not equal the actual `totalDegree`
  for zero polynomials, which are allowed.

The proof uses the strong affine Nullstellensatz to identify the radical of
the family's ideal with the vanishing ideal of its singleton zero locus.
That prime is **minimal over the original ideal**, not merely a prime containing
it. Krull's height theorem bounds its height by the cardinality of the finite
image of `f`, and the existing `height_ker_eval` identifies its height with the
number of variables. The second result contradicts uniqueness; positive
homogeneous polynomials vanish at the origin, so the third follows from the
second. The height helper is reused from
`AlgebraicGroups.Algebra.PolynomialRationalPointHeight`, not redeveloped here.

Zero variables satisfy the first inequality; the strict bound in the other
two then cannot hold. With no equations and at least one variable, both
existence results apply. Duplicates and identically zero equations are harmless.
The strict inequality is sharp: the coordinate equations `X i`, one per
variable, have only the origin as a common zero. No lower bound on the
dimension of a zero locus or assertion over non-algebraically-closed fields is
provided.


The [ordinary-import client](../../../AlgebraicGroupsTest/AlgebraicallyClosedCommonZero.lean)
illustrates the theorems; see the [build guide](../../../docs/BUILDING.md)
for pinned dependencies and cache-first commands.
