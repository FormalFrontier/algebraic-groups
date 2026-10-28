# Successive superdiagonal quotients of unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

The whole-superdiagonal coordinate homomorphism has successor filtration as kernel and is
surjective at positive stage. It identifies the successive quotient with the additive
superdiagonal coordinate group and respects arbitrary coefficient maps.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularSuperdiagonalQuotients/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), §6.49, proves one-entry
  algebraic-group quotients isomorphic to the additive group, published
  antecedents for one-coordinate point-group cases such as `n = 2`, `r = 1`
  over a field.
  The whole-superdiagonal quotient here is derived independently for arbitrary
  commutative rings; no group-scheme quotient or formal source correspondence
  is asserted.
- Mathlib contributors, `Mathlib.GroupTheory.QuotientGroup.Defs` and
  `Mathlib.GroupTheory.QuotientGroup.Basic` (`QuotientGroup.liftEquiv` and
  `QuotientGroup.map`), and `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`
  (matrix units used for coordinate lifts). The stage filtration comes from
  `AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration`.
