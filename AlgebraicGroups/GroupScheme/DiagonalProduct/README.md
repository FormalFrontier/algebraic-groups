# Finite products of diagonal group schemes

Import `AlgebraicGroups.GroupScheme.DiagonalProduct` to identify the group scheme of
invertible diagonal matrices with the **literal categorical product** of copies
of `Gₘ`. For `K : Type u` with `[CommRing K]` and `n : Type u` with `[Fintype n]`
and `[DecidableEq n]`, use
`AlgebraicGeometry.diagonalGroupSchemeProductIso K n :
  diagonalGroupScheme K n ≅ (∏ᶜ fun _ : n => multiplicativeGroupScheme K)`
in `Grp (Over (Spec (.of K)))`. No field, domain, nonzero, reducedness,
inhabited-index, flatness, or ordering assumption is needed. In particular,
the empty index is genuinely terminal (`diagonalGroupSchemeEmptyIsTerminal`
for `PEmpty.{u+1}` with `K : Type u`, and
`diagonalGroupSchemeFin0IsTerminal` for `K : Type`), including over the zero ring.

The Hopf algebra is the diagonal quotient
`DiagonalCoordinateRing.CoordinateRing K n` of the native GL coordinate ring.
For `j : n`, `diagonalGroupProjectionCoordinateMap K n j` maps the Laurent
coordinate of `multiplicativeGroupCoordinateRing K` to the quotient's `(j,j)`
matrix entry (`diagonalGroupProjection_coordinate`). Its counit is `1` and its
comultiplication is the tensor square: after mapping the GL matrix coproduct
through the quotient, every other summand vanishes because one factor is
off-diagonal. `diagonalGroupProjectionBialgHom` packages the actual Hopf map,
and `diagonalGroupProjection K n j` is the induced group-object morphism,
not merely a pointwise group homomorphism. Its underlying left scheme map is
the `Spec.map` of the coordinate ring hom (`diagonalGroupProjection_left`).
For an affine test algebra `R`, `diagonalGroupProjection_point` reads off the
native unit at `j`, including for nonreduced and zero rings.

For an **arbitrary** test scheme `X : Over (Spec (.of K))`, not necessarily
affine, `diagonalGroupHomUnits K n X` identifies morphisms to the diagonal
scheme with tuples of units in the global sections
`((algΓ (.of K)).obj X).unop`; `multiplicativeGroupHomUnits K X` does the
same for `Gₘ` with a single unit. A local CommRing adjunction helper translates
morphisms to affine targets into algebra maps on global sections without a
field assumption. `diagonalGroupProjection_globalUnit K n j X hom` proves
composition with the genuine projection reads exactly the `j`-th unit.
`diagonalGroupProductFan K n` and
`diagonalGroupProductFan_forget_isLimit K n` use this classification to
construct the universal lift and prove its uniqueness for **every** `X`.
`diagonalGroupProductFan_isLimit K n` reflects the limit from underlying
schemes through `Grp.forget`, producing the product iso. Both projection
triangles are available as simp lemmas
`diagonalGroupSchemeProductIso_hom_π` and
`diagonalGroupSchemeProductIso_inv_projection`. Affine point equivalence alone
would not establish this nonaffine universal property.

The ordinary-import client `AlgebraicGroupsTest.DiagonalProduct` checks
the polymorphic global-sections law and product triangles, `Fin 0/1/2`, the
zero ring `ZMod 1`, and both independent projections for the nonreduced
dual-number algebra `DualNumber ℤ` with unit `1 + ε` (inverse `1 - ε`).
The construction does not assert an explicit multi-Laurent algebra
presentation, dimension/smoothness, base change, a semidirect decomposition,
or source coverage.


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
