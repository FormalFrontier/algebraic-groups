# Native upper-triangular matrix groups

Import `AlgebraicGroups.GroupTheory.UpperTriangular` for the native subgroup of
invertible upper-triangular matrices. The public aggregate `AlgebraicGroups`
also imports it; the independent ordinary-import client is
[`AlgebraicGroupsTest.UpperTriangular`](../../../AlgebraicGroupsTest/UpperTriangular.lean).
See the [producer](../UpperTriangular.lean) and
[build guidance](../../../docs/BUILDING.md).

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

The existing [native diagonal group](../Diagonal.lean) `D` and
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
`kernelEquiv : U ≃* diagonal.ker` identifies the existing U with
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

## References

Milne, *Algebraic Groups* (2017), item 2.9, p. 42, describes `T_n`, `U_n`
and `D_n` as subgroup functors of `GL_n` on commutative algebras; item 2.8,
p. 41, supplies the GL context. The arbitrary-ring U-first point-group
splitting here is a separate result, not a theorem ascribed to that item.
Mathlib's `Matrix.GeneralLinearGroup` and coefficient maps come from
`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`; triangular
inversion and determinants come from `Mathlib/LinearAlgebra/Matrix/Block.lean`.
The kernel, normalizer-conjugation and transported automorphism use
`Mathlib/Algebra/Group/Subgroup/Ker.lean`,
`Mathlib/GroupTheory/Subgroup/Centralizer.lean` and
`Mathlib/Algebra/Group/End.lean`. The U-first multiplication and natural
coordinate map use `SemidirectProduct.lift` and Thomas Browning's
`SemidirectProduct.map` from `Mathlib/GroupTheory/SemidirectProduct.lean`.
The [diagonal](../Diagonal.lean)
and [unitriangular](../../GroupScheme/Unitriangular.lean) producers supply
the previously constructed groups.

For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
