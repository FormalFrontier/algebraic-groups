# Actual lower central series of finite unitriangular groups

Import `AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

The retained elementary-generation and commutator arguments identify the lower central series
exactly with the canonical superdiagonal stages, beyond the shared nilpotency upper bound.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md) preserves the full context.
Current APIs are described above.

The module imports this library's native superdiagonal filtration and its
coordinate homomorphisms (`UnitriangularSuperdiagonalQuotients`) and its native
ordered elementary commutator (`UnitriangularNilpotencyClass`). The latter uses
the separately authored official GeneralLinearGroups elementary commutator.
Each root `E_ij(a)` of distance `d + 1` lies in `γ_d` by induction on `d`,
using `⁅E_ik(a), E_kj(1)⁆ = E_ij(a)` in that order. The filtration's
commutator bound proves `γ_t ≤ F_(t+1)`.

- Mathlib contributors, `Mathlib.GroupTheory.Nilpotent` (the lower central
  series and its successor/antitone laws) and
  `Mathlib.GroupTheory.QuotientGroup.Defs` (the quotient API used by the
  preceding coordinate module).
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (ordered elementary-unit relation used by the preceding exact-class module).
  The equality here also uses the point-group coordinate elimination described
  above; it is not an algebraic subgroup-scheme equality.
