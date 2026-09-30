# Native base change of unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.UnitriangularBaseChange` (or
`AlgebraicGroups`) to use
`AlgebraicGeometry.unitriangularGroupSchemeBaseChangeIso R S ι`. For
commutative rings `R`, `S` in the same universe, `[Algebra R S]`, and a
finite linearly ordered index type `ι` in that universe, this is an
**isomorphism of actual group objects** between the native
`Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))` of
`unitriangularGroupScheme R ι` and `unitriangularGroupScheme S ι`.
Zero rings and empty or singleton indices are allowed; there is no
nontriviality, nonempty-index, flatness, or injectivity condition.

`unitriangularGroupSchemeBaseChangeIso_hom_left` reads back its underlying
forward scheme map. It first applies `pullbackSymmetry`, then the affine
comparison `pullbackSpecIso' R S (CoordinateRing R ι)`, then `Spec.map` of
`(UnitriangularCoordinateRing.baseChangeBialgEquiv R S ι).symm` viewed as a
ring homomorphism. **The inverse** is required because `Spec` reverses
coordinate-ring arrows. The companion
`unitriangularGroupSchemeBaseChangeIso_hom_over` identifies the resulting
map to `Spec S` with the second projection of the native pullback. The
first factor is group-compatible by mathlib's existing affine-pullback
instance; the second uses the published unitriangular Hopf comparison.
Neither step transports a group law from an affine-space isomorphism.

The ordinary-import
`AlgebraicGroupsTest.GroupScheme.UnitriangularBaseChange` client takes two
points of the **actual pulled-back group** over a commutative `S`-algebra
`T`, whose images under the group isomorphism correspond to unitriangular
`Fin 3` matrices `a` and `b`. It maps their native product through the
isomorphism, then reads its `(0,2)` entry as
`a₀₂ + b₀₂ + a₀₁ * b₁₂`; this cross term is derived from the actual
multiplication, not assumed. The same client checks the generic comparison
and zero-ring `Fin 0`/`Fin 1` cases. No all-morphism naturality,
index-reordering, classification, geometric promotion, or source-specific
coverage follows.

This repository pins `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`, and
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`:
13 resolved packages and 3 direct requirements. From its root, after
installing the pinned toolchain, a future authorized verifier must fetch
the matching precompiled mathlib cache successfully **before** building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build AlgebraicGroups AlgebraicGroupsTest
```

These commands do not impose a strict limit on concurrent compiler processes.

The producer/client mathematics was authored by worker-b Hive Task
`hive-request-c40cd5bb6871cfc2115117cb21f9d78a5aee869d` (UID
`28adbb76-eddd-457f-afde-a58666e8d21f`); this destination-only static
preparation is by separate worker-b Task
`hive-request-26588c9f7acea2845592c20813ff60f338e95b0f` (UID
`ffd35190-20bc-44bb-82ec-489771fac380`), without proof authorship.
The existing Hopf comparison's original Formal Frontier/worker-b authors
and mathlib's affine construction/contributors retain their distinct credit
and rights. This 2026-09-30 preparation is not a destination build,
standard-axiom audit, independent review, acceptance, or publication.
