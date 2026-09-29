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

## Build and lifecycle

The destination pins Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and the official
general-linear-groups release `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`.
Use the pinned toolchain and first fetch the matching mathlib cache before
building the producer, ordinary-import client, or both default targets:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupTheory.UnitriangularExponent
lake build AlgebraicGroupsTest.UnitriangularExponent
LAKE_JOBS=2 lake build
```

The client checks generic signatures, empty/singleton dimensions, zero rings,
strict/equality thresholds and a genuinely nonzero square-zero element over
`DualNumber (ZMod 2)`. The original isolated incubator producer and client had
focused cache-first builds and complete transitive standard-axiom checks,
including private/generated origins; they received fresh independent review
and separate maintainer acceptance. The transferred producer and client are
accepted and protected-integrated on main
`45d4c5ddfcd491f298c4c968561d2e2eccf82e06`. Original native job 932
fetched the matching cache, built both default targets (3,873 jobs) and
audited all 3,700 actual module-origin pairs across 147 total Lean modules
(108 production, 39 tests), including 1,181 private-named and all generated
origins, with zero rejects beyond the standard three axioms. Fresh independent
destination review and Lattice's separate code acceptance are complete;
independent release review, release acceptance, protected promotions and
verified private GitHub publication are still pending. Earlier generation/
derived-series results have their own completed official P9 release; that
release does not contain the new exponent results.

Original mathematical proofs and client: Formal Frontier Agents, worker-a
Hive Task `hive-request-6697261957705b5abcfeb5a713d5eccb32862d84`
(UID `e8368f27-f82b-4b70-bace-14dcd33d9ac2`); separate original static
plan: worker-a Task `hive-request-889376cf6feebfa6b7c376730a80835602410a2a`
(UID `7f433e69-c1a2-4674-9746-8eac749c1675`); fresh isolated mathematical/API
review: worker-b Task `hive-request-385475f9c731526890b911886a758b3b8b1795ac`
(UID `e7141ac7-cc41-4165-9cdd-339d5b685836`). This native transfer
preserves the proof bodies; its separate author is worker-a Task
`hive-request-2d88e4cc16946512f4d88a8bb09e16456c4ff5c1`
(UID `2ec7daea-21c2-47e7-b328-a24a4956ab4e`). Upstream mathlib and
general-linear-groups retain their own authorship and licenses. Provenance
and source-specific coverage records stay in their respective private records.
Fresh destination review was by worker-b Task
`hive-request-cca37fd56496938e743a795f5e0c4437da7e1a46` (UID
`449865e3-164c-48fa-9984-3f66c772f898`). This documentary release
preparation is by worker-a Task
`hive-request-bba7de9a57c7bb5762f49449e85c53ea5bd9e370` (UID
`a61157f1-2a86-4729-a099-c70066ae2502`), not its release review.
