<!-- SPDX-License-Identifier: Apache-2.0 -->

Import `AlgebraicGroups.GroupTheory.UnitriangularExponent`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

The retained prime-characteristic power and sharpness results compute the appropriate
prime-power exponent bounds under their explicit coefficient and matrix-size conditions.
Nilpotence of strict upper matrices supplies the power bound; positive witnesses establish
sharpness.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularExponent/README.md) preserves the full context.
Current APIs are described above.

- Mathlib contributors, `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
  (`Matrix.charpoly_of_isUpperTriangular` and Cayley–Hamilton via
  `Matrix.aeval_self_charpoly`), `Mathlib.Algebra.CharP.Lemmas`
  (`Commute.add_pow_prime_pow_eq'`) and `Mathlib.GroupTheory.Exponent`
  (`Monoid.exponent_dvd_iff_forall_pow_eq_one`). The consecutive-shift witness
  is a point-group construction, not a group-scheme exponent statement.
