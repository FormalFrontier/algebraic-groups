# Represented U-first upper-triangular product

Import `AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct`. For an
arbitrary commutative `K` and finite linearly ordered same-universe `n`, the
categorical product `U ⊗ D` over fixed `Spec K` is isomorphic as an underlying
scheme to the upper-triangular scheme `T`. The actual maps are inclusion
`i : U ⟶ T`, diagonal projection `q : T ⟶ D` and section `e : D ⟶ T`;
`upperTriangularUFirstIso` sends `(u,d)` to `i(u)e(d)`. Its inverse uses
`q(t)` and right-column normalization to extract the unitriangular factor.
The `U` here is the scheme-theoretic identity fiber, not merely a pointwise
kernel. `upperTriangularDiagonalConj` restricts represented diagonal
conjugation to `U`, and `upperTriangularUFirstTwistedMul_comp_hom` identifies
the arbitrary-test multiplication diagram. In U-first coordinates,
`(u,d)*(u',d') = (u*α(d,u'), d*d')`; this is **not** the canonical
direct-product group law, and no global transported `GrpObj` is asserted.

For every commutative `K`-algebra `R`, including zero and nonreduced rings,
the point readbacks recover the native action with entries
`α(d,u)ᵢⱼ = dᵢ*uᵢⱼ*dⱼ⁻¹`, the U-first forward map and its inverse. Empty
indices and noninjective coefficient maps remain in scope. The
[producer](../UpperTriangularSchemeProduct.lean),
[ordinary-import client](../../../AlgebraicGroupsTest/GroupScheme/UpperTriangularSchemeProduct.lean),
[split guide](../UpperTriangularSplitKernel/README.md),
[generic section-first product](../../GroupObject/SplitKernelProduct/README.md)
and [diagonal-product guide](../DiagonalProduct/README.md) give the declarations,
hypotheses and examples. No arbitrary-base-scheme change, `GL` normality,
smoothness/dimension result or source-coverage conclusion follows.

## Mathematical interface

The diagonal section `e : D ⟶ T` and inclusion `i : U ⟶ T` define represented
conjugation `α : D ⊗ U ⟶ U`. The readback
`upperTriangularDiagonalConj_lift_comp_inclusion` identifies its inclusion
with `e(d) * i(u) * e(d)⁻¹` for **every** test scheme over `Spec K`.
The generic split-kernel action and section-first product already
supply the action laws and `F(v,d) = e(d)i(v)`; this module specializes that
product as `upperTriangularSectionFirstIso`. The distinct categorical
`upperTriangularCoordinateChange` is
`H(u,d) = (α(d⁻¹,u),d)`, with inverse `(v,d) ↦ (α(d,v),d)`.
Consequently `upperTriangularUFirstIso = H ≪≫ F : U ⊗ D ≅ T` has forward
arrow `K(u,d) = i(u)e(d)`. Both inverse triangles hold categorically, not
just on points. Its forward readbacks include `upperTriangularUFirstIso_hom`
and `upperTriangularUFirstIso_hom_comp_diagonal`; inverse readbacks include
`upperTriangularUFirstIso_inv_comp_snd` and
`upperTriangularUFirstIso_inv_fst_comp_inclusion`. The latter is right-column
normalization `i(v(t)) = (𝟙 T) * (q(t) ≫ e)⁻¹` as an arrow **out of `T`**:
`𝟙 T` here denotes the identity **arrow**, not the constant group identity.

For arbitrary arrows `u,d,u',d'` out of an arbitrary test object over `Spec K`,
`upperTriangularUFirstIso_mul_lift` proves
`K(u,d) * K(u',d') = K(u * α(d,u'), d*d')`.
`upperTriangularUFirstTwistedMul` realizes the right-hand coordinates as an
arrow `(U ⊗ D) ⊗ (U ⊗ D) ⟶ U ⊗ D`, and
`upperTriangularUFirstTwistedMul_comp_hom` gives the represented multiplication
diagram. This is **not** a direct-product group law or a global transported
group-object instance. For every commutative `K`-algebra `R`, the native
point-formula theorems give

```text
α_R(d,u)ᵢⱼ = (↑dᵢ : R) * uᵢⱼ * (↑(dⱼ⁻¹) : R)
v(t)ᵢⱼ   = tᵢⱼ * (↑(diagonal(t)ⱼ⁻¹) : R)
K_R(u,d)ᵢⱼ = uᵢⱼ * (↑dⱼ : R).
```

The diagonal entries are units; inversion precedes coercion to `R`. The
ordinary-import client exercises `Fin 0`, `Fin 1`, independent-unit/sign
shear over `Fin 2`, zero ring (`ZMod 1`), a nonzero square-zero dual-number
shear, and a noninjective coefficient reduction map. No arbitrary
**base-scheme** change, normality of `U` in `GL`, smoothness/dimension, or
source-specific mathematical correspondence is asserted.


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
