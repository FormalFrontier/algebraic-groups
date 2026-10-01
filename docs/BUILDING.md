# Building algebraic-groups

Use the pinned Lean toolchain in [lean-toolchain](../lean-toolchain) and the
exact official GitHub revisions in [lakefile.toml](../lakefile.toml) and
[lake-manifest.json](../lake-manifest.json). The frozen graph has 13 resolved
packages and three direct requirements: mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, scheme-properties
`c3ce429677a7c4a342b134a881f99cacfc62f71e`, and
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`.
Access to not-yet-public GitHub dependencies may be required. Use the matching
precompiled mathlib cache before any build; a failed cache fetch is not a reason
to rebuild mathlib from source silently.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

The first target aggregates the library; the second builds its ordinary-import
clients and examples, including zero-ring and empty-index cases. For a focused
producer and matching client after fetching the cache, for example:

```sh
lake build AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSchemeProduct
```

Other producer/client pairs are linked from the [README](../README.md) and
[focused mathematical guides](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md).
These commands are reproduction instructions, not a claim of a new build or
axiom audit. Build success alone does not establish semantic review or source
coverage; a complete release proof check also audits transitive axioms of
all declarations, including private/generated declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`.

## Expected cost

With the matching mathlib cache available, budget several minutes for compiling
the library and tests, plus dependency preparation and the complete axiom audit.
This is a planning estimate, not a bound or a portable minimum-resource promise.
The following existing measurements give workload context; none is a fresh
benchmark of this candidate.

| Workload | Observed wall time | Cache and scope |
| --- | ---: | --- |
| Earlier development compilation on September 26, 2026 | 593 s total | 53 staged/root/default invocations and two ordinary clients with cached dependencies and serial compiler dispatch; the final mostly warm default invocation alone took 4 s. |
| Native library-and-test build on September 27, 2026 | 290.620 s | 3,468 Lake jobs after a successful 42.817 s matching-cache retrieval; not a cold end-to-end benchmark. |
| Native library-and-test build on September 30, 2026 | 506.519 s | 3,917 Lake jobs after successful matching-cache retrieval; before the canonical finite-type-points import cleanup. This is the build stage only, excluding the separate axiom audit. |

The September 26 Linux worker had a 15 GiB aggregate memory cap, a 12 GiB
virtual-address limit per compiler process, and serial Lean dispatch. These are
execution limits, **not measured peak resident memory**. Memory-pressure events
occurred, and two earlier attempts on different preparation states timed out
after 240 s. CPU model, storage and network throughput were not standardized.
Later timings do not establish a lower memory requirement. Cold or changed
dependencies and higher parallelism can substantially increase time and memory
needs; do not silently rebuild mathlib from source when cache preparation fails.
