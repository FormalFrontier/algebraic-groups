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
lake build AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass AlgebraicGroupsTest.UnitriangularNilpotencyClass
```

This module is a point-group class result; the separate
[lower-central-series module](../UnitriangularLowerCentralSeries/README.md)
now identifies every lower central stage with its superdiagonal filtration
stage. Neither module asserts a quotient/group-scheme theorem. The Lean
development is credited to Formal Frontier Agents; the General Linear Groups
dependency retains its distinct contributors and license.


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).

## References

- J. S. Milne, *Algebraic Groups* (2017), Example 6.36 and §6.49, for
  unitriangular algebraic-group nilpotence via a central series. Passing to
  point groups gives a field-based nilpotence antecedent; the exact `n-1`
  point-group class over nontrivial commutative rings (including `n=0`), and
  class zero for the zero ring, require the separate arguments above.
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (`Matrix.GeneralLinearGroup.elementaryUnit_commutator`); Mathlib contributors,
  `Mathlib.GroupTheory.Nilpotent` (lower central series and the class criterion).
