<!-- SPDX-License-Identifier: Apache-2.0 -->
# Prime-power exponents of native upper-unitriangular groups

Import `AlgebraicGroups.GroupTheory.UnitriangularExponent` to work with the
existing `Matrix.UnitriangularGroup (Fin n) R`, a native matrix point group.
These results require no group-scheme construction or source-specific record.

## Public API

- `Matrix.pow_card_eq_zero_of_upperTriangular_diag_zero`: for any finite
  linearly ordered `ι`, `[CommRing R]`, upper-triangular `N` with zero diagonal,
  `N ^ Fintype.card ι = 0`. Empty indices and the zero ring are included.
- `Matrix.UnitriangularGroup.pow_prime_pow_eq_one`: if `Nat.Prime p`,
  `(p : R) = 0` and `n ≤ p ^ t`, every native `g` satisfies
  `g ^ (p ^ t) = 1`, even at `n = 0` and over the zero ring.
- `Matrix.UnitriangularGroup.exists_pow_ne_one_of_pos_lt`: for `[Nontrivial R]`
  and `0 < q < n`, some native `g` satisfies `g ^ q ≠ 1`, independently of
  characteristic. The strict positive condition matters: `g ^ 0 = 1`.
- `Matrix.UnitriangularGroup.forall_pow_prime_pow_eq_one_iff` and
  `Matrix.UnitriangularGroup.exponent_dvd_prime_pow_iff`: with `[Nontrivial R]`,
  `Nat.Prime p` and `(p : R) = 0`, respectively the universal power condition
  and `Monoid.exponent (Matrix.UnitriangularGroup (Fin n) R) ∣ p ^ t` hold
  exactly when `n ≤ p ^ t`. Equality is included; trivial groups have exponent
  one. These do not claim that every element has maximal order or give a
  separate numerical exponent-equality formula.

The generic result uses the triangular characteristic polynomial and
Cayley–Hamilton. Writing a group matrix as `1 + N`, the commuting prime-power
binomial identity and the entrywise equality `(p : Matrix (Fin n) (Fin n) R) = 0`
give the bound without requiring a matrix characteristic instance for empty
indices. A consecutive superdiagonal shift witnesses sharpness via the
`(0, q)` entry of `(1 + N) ^ q`. Neither a field nor a reduced ring is needed.

## Build and examples

The destination pins Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and the official
general-linear-groups release `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`.
Use the pinned toolchain and first fetch the matching mathlib cache before
building the producer, ordinary-import client, or both default targets:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupTheory.UnitriangularExponent
lake build AlgebraicGroupsTest.UnitriangularExponent
lake build
```


The [ordinary-import client](../../../AlgebraicGroupsTest/UnitriangularExponent.lean)
checks generic signatures, empty and singleton dimensions, zero rings, sharp
thresholds and a nonzero square-zero element over `DualNumber (ZMod 2)`.

For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
