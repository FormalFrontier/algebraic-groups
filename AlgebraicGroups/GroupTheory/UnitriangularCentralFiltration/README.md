# Current publication and verification context (2026-09-29)

Official P9 `8fdf180d3b56c6bfb4a5fe8c63204ad9a7abf827` includes the
generation/derived results described below. Accepted development main
`45d4c5ddfcd491f298c4c968561d2e2eccf82e06` additionally includes
the native point-group exponent transfer, checked in original destination
job 932 and independently reviewed; its own release is still pending.
The 2026-09-28 context below is dated history, not a current count or
publication status; the filtration statements themselves are unchanged.

## Dated publication context (2026-09-28; historical)

This central-filtration API and its successive-quotient companion are
published in official release `38b7ebdcb38bd0d1b3c9a72e266162718f4647c2`.
Native job 811 verified their earlier 139-module, 35-root, 12-package
graph. The accepted sharpness transfer at
`172234b1ae20be037a781f0a105ae88dfbe3e856` passed native job 843 and
fresh independent destination review on the 141-module, 36-root, 13-package
graph, which additionally imports official `general-linear-groups`.
The [sharpness guide](../UnitriangularNilpotencyClass/README.md) describes
the exact class over nontrivial rings. Both default builds and the complete
private/generated-inclusive standard-three audit passed; see
[current build guidance](../../../docs/BUILDING.md). The G/Q release and
sharpness P7 have since been independently accepted and published; their
release decisions are distinct from accepted-code evidence. The all-stage
native point-group lower-central equality was separately published at official
P8 `441817ab159b20bb7c9c855b05d49abfa3d85c92`, after original native
job 865 checked its older 143-module graph. Development main
`a77d4e4d19f6dc366eb9a40f16503f5855421cf3` adds positive-stage
generation, exact commutators and the native derived series: original run 895
built both targets and audited 3,679 module-origin pairs across 145 **total**
Lean modules (107 production, 38 tests), including 1,168 private-named and
all generated origins under only the standard three axioms. Fresh independent
destination review and maintainer code acceptance are complete; the new
addition's own release review, acceptance and publication remain pending.
The original guide below, including then-pending publication language, is
retained as dated history, not as the current lifecycle report.

---

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
LAKE_JOBS=2 lake build AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration AlgebraicGroupsTest.UnitriangularCentralFiltration
```

This is a point-group filtration, not a construction of normal subgroup
schemes, additive quotient group schemes, or scheme nilpotence. The original
mathematical exposition, Lean implementation and independent isolated-code
review were separate agent contributions; their source-specific provenance
is recorded in the internal owning records, not needed to use this module.
The destination transfer passed fresh independent review and the complete
cache-first both-root native build/transitive standard-three audit, and was
accepted at `535d623443808796af231ed5761f837c13934cdd`. The documentation-only
release preparation preserves those computational inputs. Independent release
acceptance and verified publication remain separate, still-pending steps.
