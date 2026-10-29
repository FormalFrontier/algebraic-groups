# Building algebraic-groups

Use the pinned Lean toolchain in [lean-toolchain](../lean-toolchain) and the
exact GitHub revisions in [lakefile.toml](../lakefile.toml) and
[lake-manifest.json](../lake-manifest.json). The resolved dependency graph has 14 resolved
packages and five direct requirements: mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, scheme-properties
`c3ce429677a7c4a342b134a881f99cacfc62f71e`,
general-linear-groups `8b3b07bf2744a870b53934542e4c5ed383765bd6`,
[coherent-modules](https://github.com/FormalFrontier/coherent-modules.git)
`1112034c447b07049c12402ce0f3f25c4cffb5e4`, and
[groupTheory](https://github.com/FormalFrontier/group-theory.git)
`29001ecda5eff8e37c9ddb712f8abb509c31461d`.
The dependency sources are publicly available on GitHub. Use the matching
precompiled mathlib cache before any build; a failed cache fetch is not a reason
to rebuild mathlib from source silently.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

The first target aggregates the library; the second builds its ordinary-import
clients and examples, including zero-ring and empty-index cases. To build a
single library module and its corresponding test module after fetching the
cache, for example:

```sh
lake build AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
lake build AlgebraicGroupsTest.GroupScheme.UpperTriangularSchemeProduct
```

Other library/test pairs are linked from the [README](../README.md) and
[focused mathematical guides](../AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel/README.md).
Build success alone does not establish semantic review or source coverage.
A complete proof-integrity check also enumerates every shipped module and
declaration in the built environment, including private and generated
declarations, and audits the axioms transitively used by those declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

## Expected cost

With the matching mathlib cache available, budget several minutes for compiling
the library and tests, plus dependency preparation and the complete axiom audit.
This is a planning estimate, not a bound or a portable minimum-resource promise.
The following rounded measurements are observations of individual cached
library-and-test build stages, not end-to-end benchmarks. They exclude dependency
preparation, cache retrieval and the separate axiom audit. The builds used
different library scopes and cache states, so these figures are workload context,
not portable bounds or a fresh benchmark.

| Build stage | Observed wall time (cache/audit excluded) | Cache and workload |
| --- | ---: | --- |
| Library and tests | 291 s | 3,468 Lake jobs; successful matching-cache retrieval took 43 s separately. |
| Library and tests | 507 s | 3,917 Lake jobs; matching cache retrieved successfully. |

Recorded resource settings include a 15 GiB aggregate memory cap, a 12 GiB
virtual-address limit per compiler process, and serial Lean compiler dispatch.
These are configured execution limits, **not measured peak resident memory** or
portable minimum requirements. Memory pressure was observed under constrained
settings. CPU model, storage and network throughput were not standardized, and
these timings do not establish a lower memory requirement. Cold or changed
dependencies and higher parallelism can substantially increase time and memory
needs; do not silently rebuild mathlib from source when cache preparation fails.
