/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineHomOver
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The finite product of additive group schemes as affine space

For any commutative ring `K` and finite index type `D`, the underlying over-scheme
of the actual categorical product of copies of the additive group scheme is
`Spec (MvPolynomial D K)`, hence affine `D`-space over `Spec K`.
The product universal property is proved for all schemes over `Spec K`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (D : Type u) [Fintype D]

/-- Pullback of the additive coordinate along the `d`-th affine projection. -/
def additiveProductCoordinateAlgHom (d : D) :
    additiveGroupCoordinateRing K →ₐ[K] MvPolynomial D K :=
  SymmetricAlgebra.lift
    ((LinearMap.ringLmapEquivSelf K K (MvPolynomial D K)).symm (MvPolynomial.X d))

omit [Fintype D] in
@[simp]
theorem additiveProductCoordinateAlgHom_coordinate (d : D) :
    additiveProductCoordinateAlgHom K D d (additiveGroupCoordinate K) =
      MvPolynomial.X d := by
  simp [additiveProductCoordinateAlgHom, additiveGroupCoordinate]

/-- The candidate affine scheme, equipped with its structure map to `Spec K`. -/
abbrev additiveGroupAffineProductScheme : Over (Spec (.of K)) :=
  (Spec (.of (MvPolynomial D K))).asOver (Spec (.of K))

/-- A genuine morphism of schemes over the base, induced by the coordinate map. -/
def additiveGroupAffineProductProjection (d : D) :
    additiveGroupAffineProductScheme K D ⟶ additiveGroupUnderlyingScheme K :=
  (algSpec (.of K)).map (CommAlgCat.ofHom (additiveProductCoordinateAlgHom K D d)).op

/-- The global additive coordinate of a map from any over-scheme to `Gₐ`. -/
def additiveGroupGlobalCoordinate (T : Over (Spec (.of K)))
    (h : T ⟶ additiveGroupUnderlyingScheme K) : ((algΓ (.of K)).obj T).unop :=
  additiveGroupHomOverEquiv K T h

/-- The global `d`-th coordinate of a map into the polynomial affine scheme. -/
def additiveGroupAffineProductGlobalCoordinate (d : D)
    (T : Over (Spec (.of K)))
    (h : T ⟶ additiveGroupAffineProductScheme K D) :
    ((algΓ (.of K)).obj T).unop :=
  (affineSpecHomOverEquiv K T (MvPolynomial D K) h) (MvPolynomial.X d)

omit [Fintype D] in
/-- Projection extracts the `d`-th global polynomial coordinate, even for a
nonaffine test scheme. -/
theorem additiveGroupAffineProductProjection_globalCoordinate
    (d : D) (T : Over (Spec (.of K)))
    (h : T ⟶ additiveGroupAffineProductScheme K D) :
    additiveGroupGlobalCoordinate K T
      (h ≫ additiveGroupAffineProductProjection K D d) =
      additiveGroupAffineProductGlobalCoordinate K D d T h := by
  change (LinearMap.ringLmapEquivSelf K K ((algΓ (.of K)).obj T).unop)
      (SymmetricAlgebra.lift.symm
        (affineSpecHomOverEquiv K T (additiveGroupCoordinateRing K)
          (h ≫ (algSpec (.of K)).map
            (CommAlgCat.ofHom (additiveProductCoordinateAlgHom K D d)).op))) = _
  erw [affineSpecHomOverEquiv_comp]
  rw [LinearMap.ringLmapEquivSelf_apply]
  rw [AffineHomOver.symmetricAlgebra_lift_symm_ι K K]
  change (affineSpecHomOverEquiv K T (MvPolynomial D K) h)
      (additiveProductCoordinateAlgHom K D d (additiveGroupCoordinate K)) = _
  rw [additiveProductCoordinateAlgHom_coordinate]
  rfl

/-- The affine candidate cone over all underlying additive group schemes. -/
def additiveGroupAffineProductFan :
    Limits.Fan (fun _ : D => (additiveGroupScheme K).X) :=
  Limits.Fan.mk (additiveGroupAffineProductScheme K D)
    (additiveGroupAffineProductProjection K D)

/-- The affine cone is a product in the category of schemes over `Spec K`.
Its universal property includes every nonaffine test over-scheme. -/
def additiveGroupAffineProductFan_isLimit :
    Limits.IsLimit (additiveGroupAffineProductFan K D) := by
  classical
  refine Limits.Fan.IsLimit.mk _ (fun s ↦
    (affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).symm
      (MvPolynomial.aeval (fun d ↦ additiveGroupHomOverEquiv K s.pt (s.proj d)))) ?_ ?_
  · intro s d
    apply (additiveGroupHomOverEquiv K s.pt).injective
    change additiveGroupGlobalCoordinate K s.pt
      ((affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).symm
        (MvPolynomial.aeval (fun d ↦ additiveGroupHomOverEquiv K s.pt (s.proj d))) ≫
          additiveGroupAffineProductProjection K D d) =
        additiveGroupGlobalCoordinate K s.pt (s.proj d)
    erw [additiveGroupAffineProductProjection_globalCoordinate]
    simp only [additiveGroupAffineProductGlobalCoordinate,
      additiveGroupGlobalCoordinate, Equiv.apply_symm_apply, MvPolynomial.aeval_X]
  · intro s m hm
    apply (affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).injective
    apply MvPolynomial.algHom_ext
    intro d
    have hfac : m ≫ additiveGroupAffineProductProjection K D d = s.proj d := hm d
    have hcoord := congrArg (additiveGroupHomOverEquiv K s.pt) hfac
    change additiveGroupGlobalCoordinate K s.pt
      (m ≫ additiveGroupAffineProductProjection K D d) =
        additiveGroupGlobalCoordinate K s.pt (s.proj d) at hcoord
    erw [additiveGroupAffineProductProjection_globalCoordinate] at hcoord
    simpa only [additiveGroupAffineProductGlobalCoordinate,
      additiveGroupGlobalCoordinate, Equiv.apply_symm_apply, MvPolynomial.aeval_X] using hcoord

/-- The cone obtained by forgetting the actual group-object product. -/
def additiveGroupProductUnderlyingFan :
    Limits.Fan (fun _ : D => (additiveGroupScheme K).X) :=
  Limits.Fan.mk ((∏ᶜ fun _ : D => additiveGroupScheme K).X)
    (fun d => (Limits.Pi.π (fun _ : D => additiveGroupScheme K) d).hom.hom)

/-- Forgetting group structure preserves the actual group-object product cone. -/
def additiveGroupProductUnderlyingFan_isLimit :
    Limits.IsLimit (additiveGroupProductUnderlyingFan K D) := by
  classical
  change Limits.IsLimit ((Grp.forget (Over (Spec (.of K)))).mapCone
    (Limits.Fan.mk _ (Limits.Pi.π (fun _ : D => additiveGroupScheme K))))
  exact Limits.isLimitOfPreserves (Grp.forget (Over (Spec (.of K))))
    (Limits.productIsProduct (fun _ : D => additiveGroupScheme K))

/-- The underlying scheme of the literal finite group-scheme product is
the spectrum of the polynomial coordinate ring, over any commutative ring. -/
def additiveGroupProductUnderlyingSpecIso :
    (∏ᶜ fun _ : D => additiveGroupScheme K).X ≅
      additiveGroupAffineProductScheme K D :=
  (additiveGroupProductUnderlyingFan_isLimit K D).conePointUniqueUpToIso
    (additiveGroupAffineProductFan_isLimit K D)

/-- The spectrum comparison preserves each genuine group-product projection. -/
@[simp]
theorem additiveGroupProductUnderlyingSpecIso_hom_projection (d : D) :
    (additiveGroupProductUnderlyingSpecIso K D).hom ≫
        additiveGroupAffineProductProjection K D d =
      (Limits.Pi.π (fun _ : D => additiveGroupScheme K) d).hom.hom :=
  (additiveGroupProductUnderlyingFan_isLimit K D).conePointUniqueUpToIso_hom_comp
    (additiveGroupAffineProductFan_isLimit K D) ⟨d⟩

/-- The polynomial affine scheme is canonically affine space over the base. -/
def additiveGroupAffineProductSpecToSpaceIso :
    additiveGroupAffineProductScheme K D ≅
      (AffineSpace D (Spec (.of K))).asOver (Spec (.of K)) := by
  unfold additiveGroupAffineProductScheme Scheme.asOver OverClass.asOver
  refine Over.isoMk (AffineSpace.SpecIso D (.of K)).symm ?_
  exact AffineSpace.SpecIso_inv_over (.of K)

/-- The actual finite product of additive group schemes has underlying over-scheme
affine `D`-space; this does not assert a group-scheme isomorphism. -/
def additiveGroupProductUnderlyingAffineSpaceIso :
    (∏ᶜ fun _ : D => additiveGroupScheme K).X ≅
      (AffineSpace D (Spec (.of K))).asOver (Spec (.of K)) :=
  additiveGroupProductUnderlyingSpecIso K D ≪≫
    additiveGroupAffineProductSpecToSpaceIso K D

/-- Transporting the affine-space comparison back to the polynomial spectrum
and reading its coordinate equals the actual group-product projection's additive
coordinate. -/
theorem additiveGroupProductUnderlyingAffineSpaceIso_coordinate
    (d : D) (T : Over (Spec (.of K)))
    (h : T ⟶ (∏ᶜ fun _ : D => additiveGroupScheme K).X) :
    additiveGroupGlobalCoordinate K T
        (h ≫ (Limits.Pi.π (fun _ : D => additiveGroupScheme K) d).hom.hom) =
      additiveGroupAffineProductGlobalCoordinate K D d T
        (h ≫ (additiveGroupProductUnderlyingAffineSpaceIso K D).hom ≫
          (additiveGroupAffineProductSpecToSpaceIso K D).inv) := by
  rw [additiveGroupProductUnderlyingAffineSpaceIso, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← additiveGroupProductUnderlyingSpecIso_hom_projection K D d]
  simpa only [Category.assoc] using
    (additiveGroupAffineProductProjection_globalCoordinate K D d T
      (h ≫ (additiveGroupProductUnderlyingSpecIso K D).hom))

end AlgebraicGeometry
