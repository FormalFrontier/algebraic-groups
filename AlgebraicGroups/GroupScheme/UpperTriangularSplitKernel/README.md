# Upper-triangular diagonal split kernel

Import `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel` (also publicly
imported by `AlgebraicGroups`). For a commutative base ring `K` and finite
linearly ordered index `n`, this module uses the existing closed
upper-triangular group scheme `T`, diagonal group scheme `D`, unitriangular
group scheme `U` and ambient general-linear scheme. There is no field,
nonzero-ring, nonempty-index, reducedness, flatness or injectivity assumption.
The [producer](../UpperTriangularSplitKernel.lean) and
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSplitKernel.lean)
are available via ordinary imports.

## Mathematical API

* `AlgebraicGeometry.upperTriangularDiagonalProjection K n : T ⟶ D` and
  `AlgebraicGeometry.upperTriangularDiagonalSection K n : D ⟶ T` split in the
  order section followed by projection equals `𝟙 D`, by
  `upperTriangularDiagonal_section`. This does not assert that projection
  followed by section is the identity of `T`.
* `AlgebraicGeometry.unitriangularToUpperTriangular K n : U ⟶ T` is a closed
  immersion on underlying schemes. Its compatibility with the inclusion
  `T ⟶ GL` and that of the diagonal section are given by the separate
  `unitriangularToUpperTriangular_inclusion` and
  `upperTriangularDiagonalSection_inclusion` equalities.
* `upperTriangularDiagonalSquare_isPushout` proves a genuine coordinate
  `CommRingCat` pushout using arbitrary compatible ring maps, the entire
  existing U Hopf ideal and quotient surjectivity. The contravariant `Spec`
  square and connected-limit preservation/creation then give actual
  `upperTriangularDiagonalSquare_isPullback` (schemes),
  `upperTriangularDiagonalSquare_isPullback_over` (schemes over `Spec K`) and
  `upperTriangularDiagonalSquare_isPullback_group` (group schemes). Thus `U`
  is the identity-fiber kernel of `T ⟶ D`, not merely a field-point kernel.
* The three coordinate maps and `*_point` formulas identify the represented
  arrows with native matrix `diagonal`, `diagonalSection` and
  `inUpperTriangular` on every commutative `K`-algebra `R`. Existing native
  fixed-base naturality also covers noninjective coefficient maps.

The client checks typed maps and pullbacks, splitting, closedness, both GL
comparisons, all-algebra point formulas and fixed-base naturality. Its
examples include `Fin 0`, `Fin 1`, an independent-diagonal-units `Fin 2` shear,
`ZMod 1`, a nonzero square-zero dual-number shear and noninjective reduction.
The native U-first point-group semidirect decomposition is a different result:
no group-scheme semidirect or direct-product theorem, normality in GL,
arbitrary-base-change theorem, smoothness/dimension or source coverage is
claimed here.


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
