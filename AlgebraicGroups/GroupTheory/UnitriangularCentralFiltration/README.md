# Central filtration of unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration` for the
native matrix group `Matrix.UnitriangularGroup (Fin n) R`, with `n : ℕ`,
`R : Type` and `[CommRing R]`. The native provider couples the universes of
the matrix indices and coefficients, so this API does not assert a general
`R : Type*` version. It needs no field, nonzero-ring, dimension, characteristic,
reducedness or domain assumption.

## Stages and central series

Write `F_r := Matrix.UnitriangularGroup.superdiagonalSubgroup n R r`.
Membership means that the `(i,j)` entry of the native matrix `g - 1` vanishes
whenever `j.val < i.val + r`; `mem_superdiagonalSubgroup` gives the precise iff.
For any `r,s : ℕ`:

- `superdiagonalSubgroup_zero` and `superdiagonalSubgroup_one` identify both
  `F_0` and `F_1` with `⊤`. `superdiagonalSubgroup_antitone` and
  `superdiagonalSubgroup_succ_le` give the descending stages; the native
  `superdiagonalSubgroup_normal` instance gives normality at every stage.
- `superdiagonalSubgroup_commutator` proves `⁅F_r, F_s⁆ ≤ F_(r+s)`, even when
  `r` or `s` is zero. `superdiagonalSubgroup_end` gives `F_n = ⊥`, including
  `n = 0`.
- `descendingSeries n R t = F_(t+1)` has a native
  `Subgroup.IsDescendingCentralSeries` witness and ends at `n-1`.
  `instIsNilpotent` supplies `Group.IsNilpotent`; `nilpotencyClass_le` gives
  `Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) ≤ n-1`.
  This is an **upper bound**, not an exact-class theorem.
- For arbitrary unital `f : R →+* S`, where `S : Type` and `[CommRing S]`,
  `map_mem_superdiagonalSubgroup` and `superdiagonalSubgroup_map` show that
  the native coefficient homomorphism preserves every stage. No injectivity
  or surjectivity of `f` is assumed.

The matrix argument expands a product of elements close to `1` and bounds
the support of its correction term: strict-upper factors beginning at
superdiagonals `r` and `s` multiply into stage `r+s`. Applying this to
commutators supplies the central-series witness. The final stage is trivial
because an `n × n` matrix has no positions at distance `n`. These arguments
also work for `Fin 0`, `Fin 1`, characteristic two and the zero ring.

For example:

```lean
import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration

example (R : Type) [CommRing R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin 3) R) ≤ 2 := by
  simpa using Matrix.UnitriangularGroup.nilpotencyClass_le 3 R
```

`AlgebraicGroupsTest.UnitriangularCentralFiltration` is the persistent
ordinary-import client: it checks both first stages, the endpoint, normality,
mixed commutators and coefficient change across `Fin 0/1/2/3` and
`ZMod 1/2/4`. With the repository-pinned Lean toolchain and manifest, fetch
the matching mathlib cache **before** any build:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration AlgebraicGroupsTest.UnitriangularCentralFiltration
```

This is a point-group filtration, not a construction of normal subgroup
schemes, additive quotient group schemes, or scheme nilpotence.
For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
