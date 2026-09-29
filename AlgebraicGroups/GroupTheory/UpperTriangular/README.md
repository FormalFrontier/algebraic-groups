# Native upper-triangular matrix groups

Import `AlgebraicGroups.GroupTheory.UpperTriangular` for the native subgroup of
invertible upper-triangular matrices. The public aggregate `AlgebraicGroups`
also imports it; the independent ordinary-import client is
[`AlgebraicGroupsTest.UpperTriangular`](../../../AlgebraicGroupsTest/UpperTriangular.lean).
See the [producer](../UpperTriangular.lean) and
[build guidance](../../../docs/BUILDING.md).

**Accepted combined native/represented code (2026-09-29; own release pending).**
This native producer and client join the represented [closed subgroup scheme](../../GroupScheme/UpperTriangular/README.md)
on accepted, protected-integrated main `8640f487fa1296f0ce34fb29fdf86f146fe6f1ba`,
the child of assembly `2923211dd75f01986f381c8f91211c898ab8127d` on
released common-zero preparation parent `cb9fec27155722c2749aa03471ed40c73d3e1276`.
Both are imported by the aggregate and selected as ordinary test roots.
Original native run 1031 on that exact 13-package destination successfully
built both default targets and audited all 158 Lean modules and 4,037 actual
origins transitively, including private/generated declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. Fresh independent code review
4881 and separate Lattice acceptance preceded protected main integration.
The original isolated 26-package donor checks are distinct; the former
native-only transfer from older I11 is historical, not this code's parent or
a shipping check. This documentary preparation changes the whole-file digest,
not computational inputs. Final release review/acceptance, protected stages,
verified private publication and source coverage remain separate and pending.

## Groups and coordinates

Let `ι` be finite and linearly ordered, and let `R` be a commutative ring.
`Matrix.upperTriangularSubgroup ι R` is the literal subgroup of native
`Matrix.GeneralLinearGroup ι R` with zero entries below the diagonal;
`Matrix.UpperTriangularGroup ι R` abbreviates that subgroup. The results
include empty and singleton indices, the zero ring and nonreduced rings.
They require neither a field, a nonzero ring nor injective coefficient maps.
Triangular inversion uses the invertibility of the GL element, not a claim
that every nonzero diagonal scalar is a unit. The producer's `inclusion`,
`ext`, `map`, `map_apply`, `map_id`, `map_comp` and `inclusion_map` supply the
ambient embedding and coefficient-change API.

The existing [native diagonal group](../Diagonal.lean) `D` and published
[native unitriangular group](../../GroupScheme/Unitriangular.lean) `U` are
reused, not redefined. `UpperTriangularGroup.isUnit_entry` witnesses the
*units* on the diagonal. `diagonal : T →* D` projects to these units,
`diagonalSection : D →* T` is a multiplicative section, and
`diagonal_section`, `diagonal_surjective`, `diagonal_apply_diag`,
`diagonal_apply`, `diagonal_map` and `diagonalSection_map` give their
entrywise, splitting and naturality laws.

`UnitriangularGroup.inUpperTriangular : U →* T` is injective. The precise
`UpperTriangularGroup.range_unitriangular` equality is
`range inUpperTriangular = diagonal.ker`, **as subgroups of T**;
`kernelEquiv : U ≃* diagonal.ker` identifies the existing published U with
this kernel. This is not equality with a differently typed subgroup of GL.

`diagonalAction : D →* MulAut U` transports conjugation inside T. Its entry
weight is `dᵢ * uᵢⱼ * dⱼ⁻¹` (`diagonalAction_apply`); no normality of U in
all of GL is asserted. `unipotentPart t` is the unique U coordinate of
`t : T`: its `(i,j)` entry is **column normalized** as
`tᵢⱼ * dⱼ⁻¹` (`unipotentPart_apply`), not normalized by the row unit.

`semidirEquiv : U ⋊[diagonalAction] D ≃* T` uses **U-first** coordinates:
`(u,d) ↦ inUpperTriangular u * diagonalSection d`, with inverse
`t ↦ (unipotentPart t, diagonal t)`. Here `unipotentPart t` is represented
inside T by `t * diagonalSection (diagonal t)⁻¹`. Both inverse triangles,
the `inl`/`inr` readbacks and the multiplication law
`(u,d)(v,e) = (u * (d ⋅ v), d * e)` follow from `semidirEquiv`,
`semidirEquiv_symm_left`, `semidirEquiv_symm_right`,
`semidirEquiv_inl`, `semidirEquiv_inr` and `semidirEquiv_mul_formula`.

For **every** `R →+* S`, `UpperTriangularGroup.map`,
`UnitriangularGroup.inUpperTriangular_map`, `diagonal_map`,
`diagonalSection_map`, `diagonalAction_map` and `unipotentPart_map`
commute with coefficient change. `semidirMap` maps U-first coordinates;
`semidirEquiv_map` and `semidirEquiv_symm_map` give both forward and inverse
naturality. This is pointwise ring-map naturality, **not** a scheme-level
base-change theorem. The ordinary-import client checks the general
signatures and `Fin 0`/`Fin 1`/`Fin 2`, `ZMod 1`, a proved noninjective map
`ℤ →+* ZMod 1`, and a genuine `DualNumber ℤ` conjugation in which the
nonzero epsilon coefficient survives.

## Reproduction and credit

Use the root `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) and
`lake-manifest.json` (mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
general-linear-groups `ad7c50a0523441116537fb1d6e3c8d2a665af1fc`,
scheme-properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`).
After installing the pinned toolchain, an **authorized future check** must
first successfully fetch the matching precompiled mathlib cache:

```sh
lake exe cache get
LAKE_JOBS=2 lake build
```

The two default targets include the aggregate producer and ordinary-import client;
optional focused targets, **after the same cache fetch**, are
`AlgebraicGroups.GroupTheory.UpperTriangular` and
`AlgebraicGroupsTest.UpperTriangular`. These are reproduction instructions;
the applicable original destination result is run 1031 as described above,
not an additional check on this documentary successor.

Formal Frontier Agents authored the original project proofs, with AI
assistance under human project direction. Original isolated producer/client
author: worker-a Hive Task
`hive-request-25f51b74b10b8dad373582505576ba2ee692138e` (UID
`e1fa8608-993f-4c79-92e6-2d46a0ecda49`); separate independent isolated
reviewer: worker-b Task `hive-request-48ae663a907928d79698d7d71bc33d72d954db33`
(UID `cc2aa9a6-ab6e-47b1-96f7-2c1b1a314e27`); Lattice separately
accepted that exact *isolated* code. The static map was prepared by worker-a
Task `hive-request-7425085f1ce1dadd8f564b8e9045f49a6f89a78c` (UID
`e773905b-633e-4f57-bedb-576c9b86907d`). Import/header/namespace-only
destination transfer: worker-a Task
`hive-request-4a6283117df2506e6bc05448db523ad686a78e1d` (UID
`0f55a7c3-f8f1-4ba1-bd94-d97109e0991f`), **not** the proof author or
destination reviewer. Current combined destination assembly (not original
mathematics or review): worker-a Task
`hive-request-c9d5208b8cc04a1a8dab4d6946521d464abd124e` (UID
`78af2598-68a4-40b9-b731-bf0f6bff88da`). Independent exact-H code review
was by worker-b Task `hive-request-40fe1261db7cfb594192b5d69ac19fc5f96cc605`
(UID `b624313e-c952-46ef-b8a9-e7a5285379a0`); this guide's documentary
release preparation is by worker-a Task
`hive-request-d750315d14734904a6d83067321dccf773ef91b3` (UID
`d5aad1e2-5c4f-4a81-b7ee-7bbab31c8cae`), not mathematical authorship or
release approval. The donor files are
`Incubator/GroupTheory/UpperTriangular.lean`,
`IncubatorTest/GroupTheory/UpperTriangular.lean`, and
`Incubator/GroupTheory/UpperTriangular/README.md` at
`133d4f674bb1224730411dfd67c17bbf4601f8b7` (original Lean blobs
`9a85d047ae00a4b19e89ddf887da614bc6f9ee0a`,
`ff2ae8e3865b5f01109288cc9b039abb85508685`). The isolated evidence
and review are respectively `0e1e5bd795858cf3864179588e4c52a948f116c4`
and `7698039c7bc5af47a81d54a25b258933e5c09e58`; neither validates
this destination. The root [LICENSE](../../../LICENSE) is Apache-2.0 for
original project content. Dependencies retain their separate terms and
credits; no legal copyright holder is inferred from the authorship label.

## Dated isolated-author checkpoint (2026-09-29 07:50 UTC; historical)

The original incubator guide recorded a successful matching-cache fetch,
focused producer/client builds (both exit 0), and a 137-origin transitive
standard-three audit including private/generated declarations on the original
26-package graph. Its original cache, producer, client and audit log SHA256
values respectively are `f40016122b97fe2f70958a2a7de8e4a22a7b78a9f0f13d179472d333f898c094`,
`3369571013f0e1bc9fa5ff22b865b8ae4840263a6a73502f34360c87589dfd09`,
`fdfa4e3179ef537d49123a21ee456ff198ce7ee818220f2947d30abb4b9c9507`,
and `0bc81bd3987804fe4e15edbff245b172a1ed74a3cee06c7e75237db7a9d4165a`.
As of **that** checkpoint, fresh isolated review, Lattice's isolated
acceptance, shared registration, destination transfer, verified release and
source coverage were **then pending**. Review and isolated acceptance later
occurred at 08:02–08:04 UTC; no shared registration, destination checking,
review, integration or release follows from those isolated events.

These results do **not** establish a represented upper-triangular Hopf/group
scheme, closed scheme immersion, scheme-level semidirect splitting,
smoothness, dimension, arbitrary-base scheme change, finite-`Gₘ` product
promotion or any source-formalization decision.
