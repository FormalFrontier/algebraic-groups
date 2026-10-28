# Dimension of polynomial localizations

Use the canonical `TauCeti.ringKrullDim_localization_away` theorem. The local duplicate module
has been removed. Over a field with finitely many variables, its nonzero-denominator criterion
computes the localization dimension; a supplied nonvanishing evaluation is a sufficient way to
prove the denominator nonzero. Such a point need not exist over every finite field. The
historical supplied-point argument is credited below.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/Algebra/FinitePolynomialLocalizationDimension/README.md) preserves the full context.
Current APIs are described above.

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
