# Exact class of finite unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

Elementary matrices and iterated commutators make the nilpotency upper bound sharp over
nontrivial coefficient rings. The retained exact-class theorem handles the separate subsingleton
boundary explicitly; no field or characteristic assumption is added.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md) preserves the full context.
Current APIs are described above.

This module is a point-group class result; the separate
[lower-central-series module](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md)
now identifies every lower central stage with its superdiagonal filtration
stage. Neither module asserts a quotient/group-scheme theorem. The Lean
development is credited to Formal Frontier Agents; the General Linear Groups
dependency retains its distinct contributors and license.

- J. S. Milne, *Algebraic Groups* (2017), Example 6.36 and §6.49, for
  unitriangular algebraic-group nilpotence via a central series. Passing to
  point groups gives a field-based nilpotence antecedent; the exact `n-1`
  point-group class over nontrivial commutative rings (including `n=0`), and
  class zero for the zero ring, require the separate arguments above.
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (`Matrix.GeneralLinearGroup.elementaryUnit_commutator`); Mathlib contributors,
  `Mathlib.GroupTheory.Nilpotent` (lower central series and the class criterion).
