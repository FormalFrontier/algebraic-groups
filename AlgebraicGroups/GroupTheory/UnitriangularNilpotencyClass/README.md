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

This K-only module is a point-group class result; the separate accepted
[lower-central-series module](../UnitriangularLowerCentralSeries/README.md)
now identifies every lower central stage with its superdiagonal filtration
stage. Neither module asserts a quotient/group-scheme theorem. The original
proof and client were authored by Formal Frontier Agents
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
the regression client's 12. The documentation-only I7 preparation at
`28a4dd05b2f2f2c1aae5e2161338b953b454b762` changed none of those
computational inputs; the subsequent lower-central-series producer and client
change the graph and have their own original native job 865 destination checks:
both default targets built on 143 modules/37 regression roots/13 packages;
the complete transitive audit covered 3,634 module-origin declarations, including
1,128 private-named and all generated origins, under only the standard three
axioms. Fresh independent exact-H destination review and Lattice's code
acceptance/protected integration cover
`d3c455d9adac06b5a873828ea7de57d5501c42f4`. L was subsequently
published at official P8 `441817ab159b20bb7c9c855b05d49abfa3d85c92`.
Original native run 895 built both targets and audited all 3,679 actual
module-origin pairs (including 1,168 private-named and all generated origins)
across 145 **total** Lean modules (107 production, 38 tests) on accepted
development main `a77d4e4d19f6dc366eb9a40f16503f5855421cf3`, allowing
only the standard three axioms. Fresh independent destination review and
maintainer code acceptance/protected integration are complete for its
generation/derived addition; that addition's own release review, acceptance
and verified publication remain pending. Sharpness is published at official
P7 `f49141f0cd92a101d587a344eb3e2bd5bf4331d8`; the older
filtration/quotient P6 does not contain it. See
[build guidance](../../../docs/BUILDING.md).
