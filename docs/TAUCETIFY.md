# Canonical foundations

The library imports Mathlib and Tau Ceti and develops its additional mathematics
on their existing types and constructions. There is no compatibility layer for
the removed foundation modules.

| Subject | Canonical API |
| --- | --- |
| Subcoalgebras and restricted coalgebras | `TauCeti.Subcoalgebra`, `D.toSubmodule`, `D.coalgebra` |
| Group-like spans and finite containment | `TauCeti.Subcoalgebra.groupLikeSetSpan` and Tau Ceti's finite-subcoalgebra results |
| Comodules and subcomodules | `TauCeti.Comodule`, `TauCeti.Subcomodule` |
| Bialgebra maps on group-like elements | `TauCeti.GroupLike.map` |
| Symmetric-algebra Hopf structure and points | `TauCeti.SymmetricAlgebra`, `TauCeti.AdditiveGroup.pointsMulEquiv` |
| Projective characteristic polynomials | `LinearMap.projectiveCharpolyRev` |
| Additive group | `TauCeti.AdditiveGroup.groupScheme` |
| Multiplicative group | `TauCeti.DiagonalizableGroup.multiplicativeGroupScheme` |
| Diagonal groups | `TauCeti.SplitTorus.groupScheme` |
| Upper-triangular groups | `TauCeti.GeneralLinear.UpperTriangular.groupScheme` |
| General and special linear groups | `TauCeti.GeneralLinear`, `TauCeti.SpecialLinear` |
| Upper-unitriangular group | `TauCeti.upperUnitriangularGroup`, `TauCeti.UpperUnitriangular` |
| Finite constant groups | `TauCeti.ConstantGroup` |
| Roots of unity | `TauCeti.RootsOfUnity` |

Retained results include arbitrary finite matrix-index relabelling, coefficient
coalgebras and projective-ambient comodule containment, arbitrary-source point
classifications, closed unitriangular stages, base-change coherence, triangular
extensions, and geometry beyond the shared foundations. Their statements and
proofs use the canonical carriers. Polynomial/localization presentations express
additional mathematics about those carriers rather than comparing a second copy
of the same group or Hopf algebra.

Upper-triangular scheme results use a natural-number rank. This covers every
finite ordered index type through its order isomorphism with `Fin n`. The
arbitrary-source and scalar-ring hypotheses of the retained results are
preserved.

Subcoalgebra subtypes are written `D.toSubmodule`. This supplies the inherited
module structure explicitly; the set-like coercion of `D` alone is insufficient.
A specified comodule coaction is installed as a local instance when a proof
compares more than one coaction on the same underlying module.

## Scope and validation

The production sources under `AlgebraicGroups/` contain 188 modules and 41,457
lines, down from 206 modules and 50,003 lines at
`91a72166fbd0703b83831f490c4f0d9c18bfc4b7`: 18 modules removed and 8,546 net
lines cut (17.1%). Of the surviving production modules, 113 were updated. Counts
include comments and blank lines and exclude the aggregate module, tests and
dependencies. All 148 original test modules and 1,087 regression assertions are
retained.

Validation passed for `lake build AlgebraicGroups AlgebraicGroupsTest` (9,372
jobs), all 15 configured environment linters over every production and test
module, declaration-ownership checks, and a transitive axiom audit including
private and generated declarations. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`. Every formalization-metadata declaration was
checked against its compiled source ownership, and retained attribution notices
were compared with the original revision.

## Dependency branches

These changes use Lean `v4.36.0-rc1` and Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`. The supporting changes are published
on these branches:

- [coherent-modules: taucetify/mathlib-alignment](https://github.com/FormalFrontier/coherent-modules/tree/taucetify/mathlib-alignment), commit
  `2ade813e288fe643aa156961bbc8e8185a18bac0`.
- [scheme-properties: taucetify/mathlib-alignment](https://github.com/FormalFrontier/scheme-properties/tree/taucetify/mathlib-alignment), commit
  `3853f0d1b21c53f3fb4d99a7104d40a4e3d9b844`.
- [TauCeti: refactor/expose-group-scheme-presentations](https://github.com/TauCetiProject/TauCeti/tree/refactor/expose-group-scheme-presentations), commit
  `31e387c73506f4de0ba05e251d2905c46bea1419`. This refactors existing
  constructors to expose their canonical Hopf-spectrum presentations for direct
  elaboration by downstream clients.

The manifest records the exact dependency commits, which Lake can fetch from
the repositories above. The development checkout's `.lake/packages` links point
to the corresponding local working copies.

## Attribution

All author, contributor, copyright and license notices in retained Lean files
are preserved. [CREDITS.md](../CREDITS.md#foundation-reuse-and-retained-attribution)
records the removed modules' original notices and links to their source at the
pre-refactor revision.
