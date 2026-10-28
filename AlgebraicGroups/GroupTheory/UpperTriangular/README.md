# Native upper-triangular matrix groups

Import `AlgebraicGroups.GroupTheory.UpperTriangular`. The canonical carriers are
`TauCeti.upperTriangularGroup ι R` and `TauCeti.upperUnitriangularGroup ι R`,
with the shared maps and diagonal API in `TauCeti.UpperTriangularGroup`.
The diagonal projection `diag` targets `ι → Rˣ`, and `diagonalHom` is its
section. The U inclusion is `Subgroup.inclusion` for the canonical subgroup
containment, rather than a second embedding definition.

The retained `kernelEquiv` identifies U with the kernel of `diag`.
`diagonalAction` is conjugation by a unit tuple; its entry formula is
`dᵢ uᵢⱼ dⱼ⁻¹`. `unipotentPart` uses column normalization, and `semidirEquiv`
gives U-first coordinates `U ⋊ (ι → Rˣ) ≃* T`. The multiplication is the
semidirect law, not direct-product multiplication. The retained coefficient
naturality results cover every ring map, including noninjective maps.

Finite linearly ordered indices, arbitrary commutative rings, empty ranks,
zero rings and nonreduced rings remain allowed. The native regression client
retains the dual-number conjugation and noninjective-map examples. Scheme
splitting on canonical numerical-rank models is a separate result in
`AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UpperTriangular/README.md) preserves the full context.
Current APIs are described above.

Milne, *Algebraic Groups* (2017), item 2.9, p. 42, describes `T_n`, `U_n`
and `D_n` as subgroup functors of `GL_n` on commutative algebras; item 2.8,
p. 41, supplies the GL context. The arbitrary-ring U-first point-group
splitting here is a separate result, not a theorem ascribed to that item.
Mathlib's `Matrix.GeneralLinearGroup` and coefficient maps come from
`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`; triangular
inversion and determinants come from `Mathlib/LinearAlgebra/Matrix/Block.lean`.
The kernel, normalizer-conjugation and transported automorphism use
`Mathlib/Algebra/Group/Subgroup/Ker.lean`,
`Mathlib/GroupTheory/Subgroup/Centralizer.lean` and
`Mathlib/Algebra/Group/End.lean`. The U-first multiplication and natural
coordinate map use `SemidirectProduct.lift` and Thomas Browning's
`SemidirectProduct.map` from `Mathlib/GroupTheory/SemidirectProduct.lean`.
The [diagonal](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/Diagonal.lean)
and [unitriangular](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupScheme/Unitriangular.lean) producers supply
the previously constructed groups.

Contributor and third-party credit appears in [CREDITS](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md).
