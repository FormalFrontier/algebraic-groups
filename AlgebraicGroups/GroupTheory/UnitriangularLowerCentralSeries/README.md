# Actual lower central series of finite unitriangular groups

Import `AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries` to identify
the lower central series of the native matrix point group
`Matrix.UnitriangularGroup (Fin n) R`, for every `n : ℕ`, `R : Type`, and
`[CommRing R]`. The index and coefficient types use the same universe in the
underlying native group. No field, domain, nonzero-ring, reducedness,
characteristic, or invertibility hypothesis is needed.

Write `γ_t = (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries t`
and `F_r = Matrix.UnitriangularGroup.superdiagonalSubgroup n R r`.
The stage `F_r` consists of matrices whose difference from the identity
vanishes at `(i,j)` whenever `j.val < i.val + r`. Thus `F_1 = ⊤` and
`F_n = ⊥`. The series starts at `γ_0 = ⊤`, so the shift is **`γ_t = F_(t+1)`**
for *every* `t`, including `n = 0,1`, late stages, and the zero ring.

## Public API

- `elementary_mem_lowerCentralSeries_of_distance n R i j hij a d hd`:
  the unit `E_ij(a)` lies in `γ_d` whenever `i < j` and
  `hd : j.val = i.val + d + 1`.
- `elementary_mem_superdiagonalSubgroup n R i j hij a r hr`:
  `E_ij(a)` lies in `F_r` whenever `hr : i.val + r ≤ j.val`.
- `superdiagonalSubgroup_le_of_elementary_mem n R d hd H hroot`:
  for `hd : 1 ≤ d`, any subgroup `H` containing every `E_ij(a)` at
  distance **at least** `d` contains `F_d`. Neither normality of `H` nor
  nontriviality of `R` is required; one exact-distance diagonal is not enough.
- `lowerCentralSeries_eq_superdiagonalSubgroup n R t`: `γ_t = F_(t+1)`.

```lean
import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries

example (R : Type) [CommRing R] :
    (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin 4) R)).lowerCentralSeries 1 =
      Matrix.UnitriangularGroup.superdiagonalSubgroup 4 R 2 :=
  Matrix.UnitriangularGroup.lowerCentralSeries_eq_superdiagonalSubgroup 4 R 1
```

## Mathematics and dependencies

The module imports this library's native superdiagonal filtration and its
coordinate homomorphisms (`UnitriangularSuperdiagonalQuotients`) and its native
ordered elementary commutator (`UnitriangularNilpotencyClass`). The latter uses
the separately authored official GeneralLinearGroups elementary commutator.
Each root `E_ij(a)` of distance `d + 1` lies in `γ_d` by induction on `d`,
using `⁅E_ik(a), E_kj(1)⁆ = E_ij(a)` in that order. The filtration's
commutator bound proves `γ_t ≤ F_(t+1)`.

For `1 ≤ r`, take an **ordered list product** of elementary roots at each
`r`-superdiagonal coordinate of `x ∈ F_r`. If `d ≤ r` and an arbitrary
subgroup `H` contains all roots at distances at least `d`, each factor is
in `H`. In particular, the appropriate roots also lie in `γ_(r-1)`;
their images under the public coordinate homomorphism add to the complete
coordinate family of `x`. Products of those native elements need not commute.
The difference `p⁻¹*x` belongs to the exact kernel `F_(r+1)` *inside* `F_r`.
Descending from `F_n = ⊥` proves the arbitrary-subgroup generation criterion;
applying it to the actual lower central series recovers `F_r ≤ γ_(r-1)`.
This also handles empty coordinate sets. The construction uses neither division nor a chosen
homomorphic section of the coordinate quotient. This is a native point-group
equality, not a group-scheme quotient or an unconditional exact-class theorem.

`AlgebraicGroupsTest.UnitriangularLowerCentralSeries` checks these APIs by
ordinary import over generic rings and arbitrary subgroups, dimensions `0,1,3,4`,
symbolic positive, early and late stages, arbitrary coefficients, characteristic-two `ZMod 2`, nonreduced
`ZMod 4`, and the zero ring `ZMod 1`. To check the focused producer and client
from the repository root with the pinned toolchain and manifest, successfully
fetch the matching mathlib cache first:

```sh
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries AlgebraicGroupsTest.UnitriangularLowerCentralSeries
```

These are reproduction instructions, **not** a new build or axiom audit.
The aggregate and both default targets passed original native job 865 on the
earlier accepted H destination graph: 143 total Lean files (106 production,
37 tests), 37 test roots and 13 whole resolved
packages. After matching-cache retrieval, that run built both targets
(3,869 jobs) and audited all 3,634 module-origin declarations (3,616 distinct
names), including 1,128 private-named and all generated origins. Only
`propext`, `Classical.choice` and `Quot.sound` occurred; zero were rejected.
That job did not check the later generation refactor or derived-series graph;
their original native destination run 895 is recorded below.

## Provenance and status

**Lifecycle update (2026-09-29).** The generation/derived addition below is
published at official P9 `8fdf180d3b56c6bfb4a5fe8c63204ad9a7abf827`.
Accepted main `45d4c5ddfcd491f298c4c968561d2e2eccf82e06` also includes
the independently reviewed native exponent transfer, checked by original
destination job 932; its own release remains pending. Older pending language
and counts below describe their dated inputs, not this 147-module graph.

The preceding L equality reached accepted main I8
`164f0310a4f641cc1d698a14b333082bbfcfe474` and separately verified
official published P8 `441817ab159b20bb7c9c855b05d49abfa3d85c92`.
On that released parent, the generation extraction and dependent derived-series
module were initially **unbuilt, unaudited, unreviewed and unaccepted** at
the dated pre-H transfer stage. Original native run 895 then fetched the
matching official cache, built both targets (3,871 jobs), and audited all
3,679 module-origin pairs across 145 total Lean modules (107 production,
38 tests), including 1,168 private-named and all generated origins; only
`propext`, `Classical.choice` and `Quot.sound` occurred. Fresh independent
destination review and Lattice's acceptance/protected integration cover
development main `a77d4e4d19f6dc366eb9a40f16503f5855421cf3`. This
addition's own fresh release review, acceptance, protected promotion and
verified publication remain pending; source correspondence is a different
decision. The generation proof-only
refactor comes from isolated incubator donor `b91db48ba6ac8dc2593fd3e478daed05657e7f37`
by worker-a Task `hive-request-a86e0cfca75b354d4aca0f4c932f1991ca9e682a`
(UID `7c231766-d3e8-4c77-a695-2887fa2be307`), independently reviewed at
`3b5837720234d3a01674dfd165dcbfd17afea2e8` and accepted in isolation
by Lattice at incubator issue #143/comment 59651. This native transfer is by
worker-a Task `hive-request-4d4e96a0baa3d9b23aa444ac8cd732106652fd12`
(UID `8b645e93-000d-4103-b452-2e97301c3880`). The prior history below
is retained as a dated I8 release-readiness snapshot, not current status.

### Dated I8 release-readiness history

The mathematical plan was written by worker-b Task
`hive-request-08edbb8fbdc5bb5e32379b4a69af04dfac86f02d` (UID
`f2f8fd24-9666-4f5c-a9a9-ff8166d473a4`) and independently reviewed by
worker-a Task `hive-request-cfbfcbd60b071114848e97d31ee85b1c95b230df`
(UID `0c09e894-af02-4221-b3e4-ab601d0f7187`). The original Lean proofs
and ordinary-import client were authored by worker-b Task
`hive-request-02bbc02d1beb7d87eee2187f81d0a717ede50302` (UID
`27684e2c-8b08-4f9f-a669-402321022c4c`), independently reviewed by
worker-a Task `hive-request-5bd1af9924377f77cf7fa9218db20a5f94e3caf9`
(UID `864bb118-3e3b-468c-88df-7e2e3f0a62c2`) and accepted as an
**isolated incubator donor**. Worker-b Task
`hive-request-f27f2e34deb59cf213206a14210f059d10d08f43` (UID
`2e83cd21-7a32-43e9-8e71-cbc13759bc45`) prepared this static
AlgebraicGroups transfer without changing the proofs.

The previous static transfer `cb38a25616f9759e6d0410a7d5e2e8e820aab63c`
was prepared against frozen sharpness C while C's release was pending. This
renewal instead uses accepted I7
`28a4dd05b2f2f2c1aae5e2161338b953b454b762` as its sole parent. Sharpness
is published at verified official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8`; the earlier P6
`38b7ebdcb38bd0d1b3c9a72e266162718f4647c2` contains the filtration
and quotients but not sharpness. Neither official release contains this new
lower-central-series module. At the initial transfer renewal on 2026-09-28,
its projected 143-module, 37-test-root, 13-package destination union was
**unbuilt, unaudited, unreviewed and unaccepted**; its own actual-graph
both-target build, complete private/generated-inclusive transitive
standard-three audit, fresh independent destination review, maintainer
acceptance and reviewed official release with verified publication were
then required. The first four gates have since completed: original native
job 865 verified the actual 143-module graph, and independent exact-H review
and Lattice's acceptance/protected main integration cover commit
`d3c455d9adac06b5a873828ea7de57d5501c42f4`. This documentary candidate
has not received its own fresh release review or release acceptance, protected
promotion or verified GitHub publication. Source-specific correspondence and
coverage remain separate from this reusable library.
