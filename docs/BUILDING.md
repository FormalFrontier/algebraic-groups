# Lower-central-series transfer: current build guidance (2026-09-28)

The native lower-central-series producer and ordinary-import client were
accepted on development main `d3c455d9adac06b5a873828ea7de57d5501c42f4`
with sole released I7 parent
`28a4dd05b2f2f2c1aae5e2161338b953b454b762`.
I7's sharpness result is published at verified official P7
`f49141f0cd92a101d587a344eb3e2bd5bf4331d8`; the L result is **not yet
separately released or published**. Its actual graph has 143 Lean modules, 37
persistent regression roots and 13 resolved whole packages.
Original native job 865 (2026-09-28) fetched the matching mathlib cache,
verified readiness, built both default targets (3,869 jobs) and completed the
actual-graph transitive audit: 3,634 module-origin pairs, 3,616 distinct name
strings, 1,128 private-named origins, all generated origins and zero rejects.
Only `propext`, `Classical.choice` and `Quot.sound` occurred. Its 35 producer
and 14 client origins are included. Fresh independent exact-H destination
review and Lattice's code acceptance/protected main integration are complete.
The project retains the official `general-linear-groups` GitHub dependency at
`ad7c50a0523441116537fb1d6e3c8d2a665af1fc` to pinned mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` and Lean `v4.34.0-rc2`.
To check the changed graph, successfully fetch the matching mathlib cache
before building both default targets (`AlgebraicGroups` and `AlgebraicGroupsTest`):

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

If cache retrieval fails, diagnose it rather than rebuilding mathlib from
source. This documentary L release candidate reuses the original successful
native job 865: its Lean sources, both default targets, toolchain, resolved
dependencies and checker inputs are unchanged. The whole-165-file input digest
changes with the documents and is not reused. Separate fresh exact-release
review, maintainer release acceptance, protected promotion and verified GitHub
publication remain pending. The
[lower-central-series guide](../AlgebraicGroups/GroupTheory/UnitriangularLowerCentralSeries/README.md)
gives the focused import and regression client. At the original L transfer's
pre-check preparation on 2026-09-28, its projected counts were not successful
checks, and destination build, audit, review and acceptance were still pending;
native 865 and the subsequent acceptance supersede that candidate-time status.

Native job 843 succeeded on predecessor C
`172234b1ae20be037a781f0a105ae88dfbe3e856`: the matching cache was
fetched before both default targets were built. All 141 local modules and 36
test roots were checked. The complete transitive audit
enumerated 3585 module-origin declarations, including 1082 private-named origins
and all generated origins, and rejected none: only `propext`, `Classical.choice`
and `Quot.sound` occurred. Different modules can reuse a declaration name;
there were 3567 distinct name strings, not 3567 audited module-origin pairs.
Fresh independent destination review and maintainer acceptance followed.
The documentation-only I7 release preparation preserved all C computational
inputs, and the sharpness result reached official P7. The present L producer,
client, aggregate import and explicit test root change those inputs: neither
job 843 nor its 141-module scope certifies the projected 143-module L union.

G/Q are already published at official commit
`38b7ebdcb38bd0d1b3c9a72e266162718f4647c2`; their native job 811
certifies its earlier **139-module, 35-root, 12-package** graph only.
The [sharpness guide](../AlgebraicGroups/GroupTheory/UnitriangularNilpotencyClass/README.md)
and ordinary-import `AlgebraicGroupsTest.UnitriangularNilpotencyClass` client
describe the additions. The remainder of this guide is the unmodified dated
I6 build/resource snapshot: its then-pending G/Q publication, counts,
measurements and job references are historical, not the L graph's checks.

---

# Build and resource guidance

This guide describes the checked-in library and its build inputs. Use the
repository's `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` together.
The current Lean version is `v4.34.0-rc2`, with mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The project dependencies use
official published GitHub release commits listed in the README and manifest.
The GitHub repositories are currently private and require authorized access.
The checked-in tree includes 139 modules with 35 regression roots selected by the
no-target default build. Build and audit requirements are described below;
exact-version checks and release decisions are recorded separately.

## Build the declared targets

From the project root, fetch the matching precompiled mathlib cache successfully
before building:

```sh
lake exe cache get && lake build
```

If cache retrieval fails, diagnose that failure before continuing. Do not replace
it with an accidental full mathlib source rebuild. Fetch again after changing
Lean/mathlib pins or replacing `.lake`. Dependency caches do not substitute for
compiling the selected library sources. An existing successful build may be
reused when Lean, source and build/dependency inputs are unchanged; a
documentation-only change does not require another build.

The default targets are the production aggregate and all 35 registered regression
roots, reaching all 139 local Lean modules: 104 production files including the
aggregate, and 35 test files. Every checked-in Lean file declares the module system;
the default build checks all regression examples, including anonymous examples.
The axiom audit covers every retained named, private and generated compiled
declaration; a module may contain checked examples without retaining constants.
An applicable ordinary Lean build checks proofs. Native job 530 covers the
separately accepted 125-module, 29-root semidirect predecessor; native job 533
successfully built both default targets of the accepted 130-module, 31-root
snapshot (3,468 jobs). The earlier native job 477 applies only to its
121-module predecessor, not either successor. The additional computational
release check is a transitive
axiom audit covering repository declarations, including private declarations and
dependencies reached from them, using ordinary `#print axioms` or
`Lean.collectAxioms`. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed; `sorryAx` and every additional axiom fail. A source grep is insufficient.
Native job 533 completed this private-inclusive audit for its 130 modules and
3,268 module-origin declarations (944 private-prefix), using only those allowed
axioms. Its exact checked Lean, build, dependency and checker inputs were
unchanged in the predecessor's documentation-only release preparation. The
additional producers, aggregate imports and test root changed the graph.
Native job 682 (2026-09-28) successfully built both configured default targets
(3,471 jobs) and audited all 133 modules: 3,404 module-origin declarations,
including 955 private-named declarations, with only the three allowed axioms.
Independent destination review and maintainer code acceptance cover exact
snapshot `7ad131de3c5a7696df678e944aaa20c1defbb397`. Its documentation-only
preparation changed four of its 150 recorded file tuples, all documentation or
metadata. All Lean, toolchain, build, dependency and checker inputs and all
twelve resolved packages remained unchanged; that predecessor subsequently received
separate release acceptance and verified private GitHub publication. The later
geometry transfer added a producer, client, aggregate import and 33rd test root.
Neither job 682 nor the isolated geometry check certifies those changed inputs.
Native job 718 (2026-09-28, exact accepted main
`31492d5a182c21f40af029121718ceca8085568a`) successfully fetched the
matching mathlib cache, built both configured default targets (3,473 jobs),
and audited all 135 modules and 3,419 actual-origin declarations, including
956 private-named declarations, with only the three allowed axioms. The fifteen
actual geometry declarations include generated and private names; the twelve
selected metadata rows are not its complete audit. Independent non-author
transfer review and maintainer code acceptance/protected main integration are
complete. Geometry subsequently received independent release acceptance and
verified official publication at
`183bbbcebf0693df849ad6f5781df4c97d33364f`. That geometry-release preparation
preserved its checked Lean, build, dependency and checker inputs; the original
whole-153-file input digest describes that earlier destination, not this tree.

The later central-filtration and successive-quotient transfer added four Lean
modules, including two regression roots. Native job 811 (2026-09-28, exact
accepted main `535d623443808796af231ed5761f837c13934cdd`) fetched and verified
the matching mathlib cache, built both default targets (3,480 jobs), and audited
all 139 project modules and 3,542 actual-origin declarations, including 1,048
private-named origins and all generated origins. Only the three permitted
axioms occurred. Neither job 718 nor isolated donor checks certify the added
G/Q graph; job 811 is its complete destination pass. Fresh independent
destination review and maintainer acceptance/protected integration are complete.
This documentation-only release preparation preserves all checked computational
inputs, but not the original whole-file input digest. Independent G/Q release
acceptance and verified publication remain separate, still-pending steps; the
published geometry release named above does not contain G/Q.

Start a downstream client with `import AlgebraicGroups`, or use a focused import
such as `AlgebraicGroups.GroupScheme.Additive` or
`AlgebraicGroups.GroupScheme.Vector` or
`AlgebraicGroups.GroupScheme.Unitriangular`. Its ordinary-import client
`AlgebraicGroupsTest.Unitriangular` is one of the original 32 test roots;
the [group guide](../AlgebraicGroups/GroupScheme/Unitriangular/README.md)
describes its precise hypotheses and boundaries. The new focused import
`AlgebraicGroups.GroupScheme.UnitriangularGeometry` and its ordinary-import
21-example client `AlgebraicGroupsTest.UnitriangularGeometry` expose the
underlying affine-space iso, relative smoothness/integrality and field-only
numeric dimensions; see the [geometry guide](../AlgebraicGroups/GroupScheme/UnitriangularGeometry/README.md).
For the point-group central series and positive-stage successive quotients, use
`AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration` and
`AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients`; their two
ordinary-import clients are included in the 35 regression roots. The
[filtration guide](../AlgebraicGroups/GroupTheory/UnitriangularCentralFiltration/README.md)
and [quotient guide](../AlgebraicGroups/GroupTheory/UnitriangularSuperdiagonalQuotients/README.md)
state the exact hypotheses and distinguish these APIs from scheme quotients.
After a successful matching cache fetch, reproduce the focused clients and
both default targets with:

```sh
lake exe cache get
lake build AlgebraicGroupsTest.Unitriangular
lake build AlgebraicGroupsTest.UnitriangularGeometry
lake build
```

These commands are reproduction guidance; native job 811 supplies applicable
destination build and audit evidence for the unchanged computational inputs.
That evidence does not by itself accept or publish the G/Q release. Job 718 is
retained above as evidence for the earlier, now-published geometry destination.
Representative clients are in `AlgebraicGroupsTest/`. Some generated auxiliary
names have changed during the native-module migration; use the authored APIs
described in the README.

## Measured development baseline

The following observations are from the independently reviewed development
revision `dde1583ebf4ad6df11b53fcbad526f7d1d9ff6e4` on 2026-09-26. It precedes
the infinitesimal-additive test changes and final official dependency
selection. It is useful planning context, **not** a cold full-release benchmark
or a measurement of the current final candidate.

| Workload | Observed wall time | Context |
| --- | ---: | --- |
| Successful matching mathlib cache retrieval | 51 s | 8,892 files decompressed; network/cache-dependent. An earlier thread-creation failure is not counted as a success. |
| 53 staged/root/default build invocations plus two ordinary clients | 593 s total | Pinned development graph, dependency cache available, serial compiler dispatch; longest invocation 100 s. This total includes the warm default below. |
| Final warning-fatal default build | 4 s | 3,402 Lake jobs after the staged work; most outputs already existed. Not a clean-build time. |
| Existing MatrixEndAdditive / MatrixEndScheme ordinary clients | 6 s / 5 s | Included in the 593 s total, after their dependencies were built. |

That Linux worker had a 15 GiB aggregate memory cap, a 12 GiB virtual-address limit
per compiler process, and actual serial Lean dispatch (`-j1`, runtime thread
count 1). These are execution limits, **not measured peak resident memory** or a
portable minimum-RAM promise. Memory-limit pressure events were recorded; do not
infer an absence of pressure from successful completion. CPU model, disk and
network throughput are not standardized by this baseline. Two earlier author
default attempts on different preparation states timed out after 240 s each.

Plan for dependency/cache preparation and several minutes of source compilation
on a comparable warm-dependency, serial setup, with additional time for all
shipped tests and the complete transitive axiom audit. This is an
estimate based on the development observations, not a bound. A cold or changed
dependency graph can take substantially longer. The final official-pin build
on 2026-09-26 used matching cached dependencies and retained warm outputs through
three diagnosed source corrections. Its final successful stage took 18.351 s,
including the remaining affected chain and no-target default. This is not the
total compilation time or a cold-build benchmark; all 102 applicable module
builds and all 19 regression roots were covered across that sequence.

A separate successful pinned native run on 2026-09-27 (job 533) measured
42.817 s for its matching mathlib cache retrieval and 290.620 s for its
both-default-target build of 3,468 jobs. These are stages of that actual run,
not a cold total-time benchmark, a peak-memory measurement or a resource
guarantee; they do not replace the dated development baselines above.

## What a build does not establish

Neither a build nor an axiom audit establishes the accuracy of documentation,
API and source-correspondence claims, metadata, licensing and attribution, file
hygiene, official dependency identities or release history. These require
lightweight inspection and independent substantive review. Existing documentation
and applicable evidence are reused, with concrete inaccuracies corrected.

Separate exhaustive stored-proof replay, fresh expensive API-documentation
generation, runtime/cache-equivalence reconstruction and repeated compilation as
both an internal and a GitHub consumer are not release prerequisites. Actual
publication still requires the accepted artifact and independent public history,
the intended private destination and exact mirrored commit/ref verification.
