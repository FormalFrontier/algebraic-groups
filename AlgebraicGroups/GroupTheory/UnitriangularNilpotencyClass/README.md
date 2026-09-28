# Exact class of finite unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass` for the native
`Matrix.UnitriangularGroup (Fin n) R`, with `n : ℕ`, `R : Type` and `[CommRing R]`.
The index and coefficient types share a universe in this native provider. This
module uses the [central filtration](../UnitriangularCentralFiltration/README.md)
and the official `GeneralLinearGroups.ElementaryCommutator` API; it defines no
replacement matrix group or group scheme.

For `i < j`, `Matrix.UnitriangularGroup.elementary n R i j hij a` is the
native unit with matrix `1 + Matrix.single i j a`, even when `a : R` is not
invertible. `elementary_gl` and `elementary_coe` identify its general-linear
and matrix images. If `i < j < k`, `elementary_commutator` identifies
`⁅elementary(i,j,a), elementary(j,k,b)⁆` with `elementary(i,k,a*b)` in the
native subgroup. The ordered commutator is `x*y*x⁻¹*y⁻¹`; its matrix identity
comes from the official general-linear-groups library.

For `1 ≤ k < n`, the elementary unit in position `(0,k)` with coefficient
`1` lies in the **actual** lower central series at stage `k-1`: start at
`γ₀ = ⊤` and take successive commutators with adjacent elementary units.
When `[Nontrivial R]`, the `(0,n-1)` unit is nonidentity for `n ≥ 2`, making
the existing `nilpotencyClass_le` upper bound sharp. Thus
`Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial n R` gives
`Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) = n - 1` for
**every** `n`, including `n = 0, 1`. With `[Subsingleton R]`, the distinct
`nilpotencyClass_eq_zero_of_subsingleton n R` gives class zero for every `n`.
In particular, nontriviality cannot be dropped for `n ≥ 2` (consider the zero
ring). No field, domain, reducedness or characteristic assumption is needed.

```lean
import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass

example (R : Type) [CommRing R] [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 4) R) = 3 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_eq_of_nontrivial 4 R
```

The ordinary-import regression client
`AlgebraicGroupsTest.UnitriangularNilpotencyClass` exercises elementary
coercions and commutators, dimensions `0`–`4`, `ZMod 1/2/4` and nonreduced
coefficients. From this repository's pinned Lean/Lake project, obtain the
matching mathlib cache before building the focused producer and client:

```sh
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass AlgebraicGroupsTest.UnitriangularNilpotencyClass
```

This is a point-group class result, not an identification of every lower
central stage with the superdiagonal filtration or a quotient/group-scheme
theorem. The original proof and client were authored by Formal Frontier Agents
in the incubator, reviewed independently there, and transferred here with only
module-import and client-namespace substitutions. The official GLG dependency
retains its own authorship and license.

On 2026-09-28, the transferred code at
`172234b1ae20be037a781f0a105ae88dfbe3e856` passed fresh independent
destination review and native job 843, followed by maintainer acceptance and
integration. That run checked both default targets and the complete 141-module,
36-root, 13-package graph after a successful matching-cache fetch. Its complete
transitive audit enumerated 3585 module-origin declarations, including 1082
private-named origins and all generated origins, permitting only `propext`,
`Classical.choice` and `Quot.sound`. It includes this producer's 31 origins and
the regression client's 12. The current documentation-only preparation changes
none of those computational inputs. Exact release acceptance and publication
are recorded separately; the older published filtration/quotient release does
not contain this sharpness result. See [build guidance](../../../docs/BUILDING.md).
