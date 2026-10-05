# Finite polynomial localization dimension

`MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero` calculates the
Krull dimension of the localization of `MvPolynomial σ K` away from `f` when
`K` is a field, `σ` is finite and an explicitly supplied `a : σ → K` has
`MvPolynomial.eval a f ≠ 0`. The answer is `Fintype.card σ`, including the
empty-variable case. No infinitude or algebraic closure hypothesis is required.

The nonvanishing witness rules out `f = 0`: localization away from zero is a
zero ring, so it cannot have the asserted dimension. Merely assuming `f ≠ 0`
does not supply such a witness over a finite field. For example,
`X ^ 2 - X` is nonzero in `𝔽₂[X]` but evaluates to zero at both `𝔽₂`-points.

The proof presents the localization as the quotient by `f * X - 1` in one
extra polynomial variable, uses a maximal evaluation ideal of full height,
and cancels the dimension drop from the regular hypersurface relation. The
height-of-evaluation theorem is reused from
`AlgebraicGroups.Algebra.PolynomialRationalPointHeight`.

Import `AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension` independently
of the diagonal group-scheme module. From this repository's root, with its pinned
Lean toolchain and dependency graph, fetch the matching mathlib cache first:

```sh
lake exe cache get
lake build AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension
lake build AlgebraicGroupsTest.Algebra.FinitePolynomialLocalizationDimension
```

## References

- The Stacks Project, [Lemma 10.114.1](https://stacks.math.columbia.edu/tag/00OP)
  for polynomial maximal-ideal height, and
  [Lemma 10.60.13](https://stacks.math.columbia.edu/tag/00KW) for the local
  nonzerodivisor dimension-drop principle. The latter is not the same statement
  as this global localization formula with its explicit rational-point witness.
- The mathlib community, [*Mathlib*](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5),
  `Mathlib.RingTheory.Localization.Away.AdjoinRoot` (`awayEquivAdjoin`),
  `Mathlib.RingTheory.KrullDimension.Regular`
  (`Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors`), and
  `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.RingTheory.KrullDimension.Field` for the dimension computations.
