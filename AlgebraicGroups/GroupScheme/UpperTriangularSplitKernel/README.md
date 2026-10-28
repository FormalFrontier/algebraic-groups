# The canonical upper-triangular split kernel

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel`. The diagonal projection from
`TauCeti.GeneralLinear.UpperTriangular.groupScheme K N` targets the canonical split torus, with
canonical diagonal section. The retained pullback identifies its actual scheme-theoretic
identity fiber with the canonical unitriangular group scheme. Point formulas work over every
commutative coefficient algebra, including zero and nonreduced rings; numerical rank includes
zero. These are genuine scheme/group-scheme identities rather than geometric-point tests.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md) preserves the full context.
Current APIs are described above.

* J. S. Milne, *Algebraic Groups* (2017), §2.9 describes `T_n`, `D_n` and
  `U_n` over a field and commutative coefficient algebras. Milne,
  *Algebraic Groups* (course notes, version 2.00), §§2.20–2.21 gives the
  field-base split triangular semidirect product; neither cited passage is
  the arbitrary-base `CommRingCat` pushout or group-scheme kernel proof.
* Mathlib, `Mathlib/AlgebraicGeometry/Pullbacks.lean`:
  `isPullback_SpecMap_of_isPushout` converts the coordinate pushout to the
  scheme pullback; `Mathlib/CategoryTheory/Limits/Constructions/Over/Connected.lean`
  and `Mathlib/CategoryTheory/Monoidal/Cartesian/GrpLimits.lean` supply the
  connected-limit and group-object limit creation used to lift the square.
* `AlgebraicGroups/GroupTheory/UpperTriangular.lean` defines native
  diagonal and section maps. The Hopf quotients and point comparisons in
  `AlgebraicGroups/GroupScheme/UpperTriangular.lean`,
  `AlgebraicGroups/GroupScheme/Diagonal.lean` and
  `AlgebraicGroups/GroupScheme/Unitriangular.lean` are the represented inputs.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
