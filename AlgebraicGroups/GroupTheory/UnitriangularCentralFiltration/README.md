# Central filtration of unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

The canonical superdiagonal filtration and nilpotency upper bound come from Tau Ceti. The
retained module adds stage zero, normality, a descending-central-series witness and arbitrary
coefficient-map preservation. Write `superdiagonalSubgroup (n := n) (R := R) r`;
`mem_superdiagonalSubgroup_iff` compares entries with the identity matrix.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md) preserves the full context.
Current APIs are described above.

- J. S. Milne, *Algebraic Groups* (2017), Definition 6.34 and Remark 6.35
  (central-series criterion), Example 6.36 and §6.49 (unitriangular
  algebraic-group nilpotence via a central series). Passing to point groups
  gives nilpotence in Milne's field-based setting, a published special-case
  antecedent. Milne removes individual entries through algebraic subgroups;
  the coarser whole-superdiagonal point-group filtration here covers arbitrary
  commutative rings, `Fin 0` and the zero ring. Its `n-1` class upper bound
  does not follow from a numerical claim attributed to Milne; no algebraic
  subgroup-scheme correspondence is asserted here.
- Mathlib contributors, `Mathlib.GroupTheory.Nilpotent` (descending central
  series, lower central series and nilpotency class) and
  `Mathlib.GroupTheory.Commutator.Basic` (subgroup commutators). The underlying
  unitriangular group and coefficient map are supplied by this library's
  `AlgebraicGroups.GroupScheme.Unitriangular`.
