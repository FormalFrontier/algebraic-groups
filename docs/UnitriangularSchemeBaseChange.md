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


For pinned dependencies, build and focused client commands, see the
[build guide](BUILDING.md). Project and third-party contributor credit is in
[credits](../CREDITS.md).
