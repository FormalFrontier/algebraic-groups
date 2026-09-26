# Build and resource guidance

This guide describes the checked-in library and its build inputs. Use the
repository's `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` together.
The current Lean version is `v4.34.0-rc2`, with mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The project dependencies use
official published GitHub release commits listed in the README and manifest.
The GitHub repositories are currently private and require authorized access.
The checked-in tree ships 113 modules with 23 regression roots selected by the
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

The default targets are the production aggregate and all 23 registered regression
roots, reaching all 113 local Lean modules: 90 production files including the
aggregate, and 23 test files. Every shipped Lean file declares the module system;
the default build checks all regression examples, including anonymous examples.
The axiom audit covers every retained named, private and generated compiled
declaration; a module may contain checked examples without retaining constants.
The ordinary Lean build checks proofs. The additional
computational release check is a transitive
axiom audit covering repository declarations, including private declarations and
dependencies reached from them, using ordinary `#print axioms` or
`Lean.collectAxioms`. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed; `sorryAx` and every additional axiom fail. A source grep is insufficient.

Start a downstream client with `import AlgebraicGroups`, or use a focused import
such as `AlgebraicGroups.GroupScheme.Additive` or
`AlgebraicGroups.GroupScheme.Vector`. Representative clients are in
`AlgebraicGroupsTest/`. Some generated auxiliary names have changed during the
native-module migration; use the authored APIs described in the README.

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
