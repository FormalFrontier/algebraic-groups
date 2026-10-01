# Geometry of upper-unitriangular group schemes

Import `AlgebraicGroups.GroupScheme.UnitriangularGeometry` (or the aggregate
`AlgebraicGroups`) to use the geometry of the existing
`AlgebraicGeometry.unitriangularGroupUnderlyingScheme K ι` over `Spec K`.
The general results assume `[CommRing K] [Fintype ι] [LinearOrder ι]`,
with no field, nontriviality or positive-rank requirement. The coordinate
algebra `UnitriangularCoordinateRing.CoordinateRing K ι` is the
**determinant-localized** GL Hopf quotient from
`AlgebraicGroups.GroupScheme.Unitriangular`, not a new presentation.

`AlgebraicGeometry.unitriangularUnderlyingAffineSpaceIso K ι` is an isomorphism
**in `Over (Spec K)`** with actual
`AffineSpace (UnitriangularCoordinateRing.StrictUpperPair ι) (Spec K)`.
The forward pullback sends polynomial `X p` to the quotient of GL's `(p.1,p.2)`
matrix entry (`unitriangularUnderlyingAffineSpaceIso_preimage_variable`);
the inverse pullback sends a coordinate-algebra element through
`(UnitriangularCoordinateRing.freeEquiv K ι).symm`
(`unitriangularUnderlyingAffineSpaceIso_preimage_inverse`). Both lemmas read
the maps induced by the actual scheme isomorphism after composing with
`AffineSpace.SpecIso`, rather than defining a second point functor.

For arbitrary `CommRing K`, the coordinate algebra is standard smooth, smooth,
flat and finitely presented over `K`. The **actual structure morphism** has
`Smooth`, `Flat`, `LocallyOfFinitePresentation` and
`GeometricallyIntegral` instances. In particular these relative assertions
remain valid for `K = ZMod 1`; relative geometric integrality there is
vacuous because the base spectrum is empty, and is **not** an absolute
integrality or nonemptiness assertion. Under `[IsDomain K]` separately,
`IsIntegral` holds for the underlying scheme.

Only under `[Field K]`, the ring Krull dimension and the underlying scheme's
topological Krull dimension equal `((Fintype.card ι).choose 2 : WithBot ℕ∞)`.
The `Fin n` topological corollary exposes `n.choose 2`; ranks `0,1,2,3`
have dimensions `0,0,1,3`. There is no unconditional numerical absolute
dimension formula for an arbitrary commutative base. The affine-space
isomorphism is **not** an additive group-scheme isomorphism: the existing
[`AlgebraicGroupsTest.Unitriangular`](../../../AlgebraicGroupsTest/Unitriangular.lean)
rank-three example records the `s 0 1 * t 1 2` cross term in the `(0,2)`
product; see also the [group-scheme guide](../Unitriangular/README.md).

For ordinary downstream use, import the producer and `infer_instance` for
structural smoothness, flatness or geometric integrality; use the named
isomorphism and readbacks for geometric coordinates. For example:

```lean
import AlgebraicGroups.GroupScheme.UnitriangularGeometry

open AlgebraicGeometry UnitriangularCoordinateRing

example (K : Type) [CommRing K] (ι : Type) [Fintype ι] [LinearOrder ι] :
    Smooth (unitriangularGroupUnderlyingScheme K ι).hom := inferInstance

example : GeometricallyIntegral
    (unitriangularGroupUnderlyingScheme (ZMod 1) (Fin 0)).hom := inferInstance
```

The ordinary-import [21-example regression client](../../../AlgebraicGroupsTest/UnitriangularGeometry.lean)
also checks both pullbacks, absolute integrality under `IsDomain`, the zero
ring, ranks zero and one, and field dimensions at ranks zero through three.
With the repository's pinned Lean toolchain and dependencies, reproduce the
focused checks from the repository root (fetch the matching cache **before**
building):

```sh
lake exe cache get
lake build AlgebraicGroups.GroupScheme.UnitriangularGeometry
lake build AlgebraicGroupsTest.UnitriangularGeometry
lake build
```


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
