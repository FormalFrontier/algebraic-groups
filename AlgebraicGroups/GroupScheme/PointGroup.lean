/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Convolution
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The group functor of algebra-valued points of a Hopf algebra

For a commutative Hopf algebra `A` over `K`, `pointGroupFunctor K A` sends a
commutative `K`-algebra `R` to `WithConv (A →ₐ[K] R)` with the named convolution
group structure. Its morphisms are postcomposition. The universes of `K`, `A`
and `R` are independent: the point group lives in `max a r` for `A : Type a`
and `R : Type r`. No coalgebra structure on a test algebra is used.

For same-universe spectra, the geometric comparison remains Mathlib's
`Spec.mapMulEquiv`, without replacing its map or inverse. The equations below
supply its antipode-inverse and coefficient-map readbacks. They do not assert
that a fixed universe of schemes contains spectra of algebras of every size.

## References

* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `RingTheory/HopfAlgebra/Convolution`: convolution and the antipode.
* Yaël Dillies, Christian Merten, Michał Mrugała and Andrew Yang, Mathlib,
  `AlgebraicGeometry/Group/Affine`: `Spec.mapMulEquiv` and the group structure
  on affine geometric points.
* Mathlib, `Algebra/Category/CommAlgCat/Basic` and
  `Algebra/Category/Grp/Basic`: the bundled categories used here.
-/

@[expose] public section

noncomputable section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

universe u a r

namespace AlgebraicGeometry

section Functor

variable (K : Type u) [CommRing K] (A : Type a) [CommRing A] [HopfAlgebra K A]

/-- The group-valued functor of algebra maps from a commutative Hopf algebra.
The object group is the named convolution group on Mathlib's unchanged carrier;
coefficient algebra maps act by postcomposition. -/
def pointGroupFunctor : CommAlgCat.{r, u} K ⥤ GrpCat.{max a r} where
  obj R :=
    { carrier := WithConv (A →ₐ[K] R)
      str := AlgHom.convolutionGroup K A R }
  map {R S} q :=
    @GrpCat.ofHom (WithConv (A →ₐ[K] R)) (WithConv (A →ₐ[K] S))
      (AlgHom.convolutionGroup K A R) (AlgHom.convolutionGroup K A S)
      (AlgHom.convolutionPostcomp q.hom)
  map_id R := by
    apply GrpCat.ext
    intro f
    apply ofConv_injective
    ext x
    rfl
  map_comp q p := by
    apply GrpCat.ext
    intro f
    apply ofConv_injective
    ext x
    rfl

/-- The point functor has exactly the convolution algebra-map carrier. -/
theorem pointGroupFunctor_obj_coe (R : CommAlgCat.{r, u} K) :
    ((pointGroupFunctor K A).obj R : Type (max a r)) = WithConv (A →ₐ[K] R) := rfl

/-- The object uses the named convolution group value, not a competing instance. -/
theorem pointGroupFunctor_obj_group (R : CommAlgCat.{r, u} K) :
    ((pointGroupFunctor K A).obj R).str = AlgHom.convolutionGroup K A R := rfl

/-- At a target bialgebra with its canonical algebra, the object group value
is Mathlib's original convolution group, including all operation data. -/
theorem pointGroupFunctor_obj_group_eq_convGroup (R : Type r)
    [CommRing R] [Bialgebra K R] :
    ((pointGroupFunctor K A).obj (CommAlgCat.of K R)).str =
      (AlgHom.convGroup : Group (WithConv (A →ₐ[K] R))) :=
  AlgHom.convolutionGroup_eq_convGroup K A R

/-- The coordinate of the unit point is the counit followed by the coefficient map. -/
@[simp] theorem pointGroupFunctor_one_ofConv (R : CommAlgCat.{r, u} K) :
    (1 : (pointGroupFunctor K A).obj R).ofConv =
      (Algebra.ofId K R).comp (Bialgebra.counitAlgHom K A) := rfl

/-- Evaluation of the unit point. -/
theorem pointGroupFunctor_one_apply (R : CommAlgCat.{r, u} K) (x : A) :
    (1 : (pointGroupFunctor K A).obj R).ofConv x =
      algebraMap K R (Coalgebra.counit x) := rfl

/-- Multiplication is precisely Mathlib's existing convolution multiplication. -/
theorem pointGroupFunctor_mul_ofConv (R : CommAlgCat.{r, u} K)
    (f g : (pointGroupFunctor K A).obj R) :
    (f * g).ofConv = ((toConv f.ofConv * toConv g.ofConv) :
      WithConv (A →ₐ[K] R)).ofConv := rfl

/-- Evaluation of a product is the tensor pairing against source comultiplication. -/
theorem pointGroupFunctor_mul_apply (R : CommAlgCat.{r, u} K)
    (f g : (pointGroupFunctor K A).obj R) (x : A) :
    (f * g).ofConv x = Algebra.TensorProduct.lift f.ofConv g.ofConv
      (fun _ _ ↦ .all ..) (Coalgebra.comul x) :=
  AlgHom.convMul_apply f g x

/-- The inverse point has coordinate given by antipode precomposition. -/
@[simp] theorem pointGroupFunctor_inv_ofConv (R : CommAlgCat.{r, u} K)
    (f : (pointGroupFunctor K A).obj R) :
    (f⁻¹).ofConv = f.ofConv.comp (HopfAlgebra.antipodeAlgHom K A) :=
  AlgHom.convolutionInverse_ofConv f

/-- Evaluation of the inverse point. -/
@[simp] theorem pointGroupFunctor_inv_apply (R : CommAlgCat.{r, u} K)
    (f : (pointGroupFunctor K A).obj R) (x : A) :
    (f⁻¹).ofConv x = f.ofConv (HopfAlgebra.antipode K x) := rfl

/-- The point map of a coefficient morphism is the original convolution
postcomposition monoid homomorphism. -/
theorem pointGroupFunctor_map_hom {R S : CommAlgCat.{r, u} K} (q : R ⟶ S) :
    ((pointGroupFunctor K A).map q).hom = AlgHom.convolutionPostcomp q.hom := rfl

/-- The underlying algebra map of a transported point is postcomposition. -/
@[simp] theorem pointGroupFunctor_map_ofConv {R S : CommAlgCat.{r, u} K}
    (q : R ⟶ S) (f : (pointGroupFunctor K A).obj R) :
    ((pointGroupFunctor K A).map q f).ofConv = q.hom.comp f.ofConv := rfl

/-- Evaluation of a point after a change of coefficient algebra. -/
@[simp] theorem pointGroupFunctor_map_apply {R S : CommAlgCat.{r, u} K}
    (q : R ⟶ S) (f : (pointGroupFunctor K A).obj R) (x : A) :
    ((pointGroupFunctor K A).map q f).ofConv x = q.hom (f.ofConv x) := rfl

/-- The point map preserves the unit. -/
@[simp] theorem pointGroupFunctor_map_one {R S : CommAlgCat.{r, u} K} (q : R ⟶ S) :
    (pointGroupFunctor K A).map q 1 = 1 :=
  (((pointGroupFunctor K A).map q).hom).map_one

/-- The point map preserves multiplication. -/
@[simp] theorem pointGroupFunctor_map_mul {R S : CommAlgCat.{r, u} K}
    (q : R ⟶ S) (f g : (pointGroupFunctor K A).obj R) :
    (pointGroupFunctor K A).map q (f * g) =
      (pointGroupFunctor K A).map q f * (pointGroupFunctor K A).map q g :=
  (((pointGroupFunctor K A).map q).hom).map_mul f g

/-- The point map preserves the antipode inverse. -/
@[simp] theorem pointGroupFunctor_map_inv {R S : CommAlgCat.{r, u} K}
    (q : R ⟶ S) (f : (pointGroupFunctor K A).obj R) :
    (pointGroupFunctor K A).map q f⁻¹ = ((pointGroupFunctor K A).map q f)⁻¹ :=
  _root_.map_inv ((pointGroupFunctor K A).map q).hom f

/-- Transport by the identity coefficient map fixes every point. -/
theorem pointGroupFunctor_map_id_apply (R : CommAlgCat.{r, u} K)
    (f : (pointGroupFunctor K A).obj R) :
    (pointGroupFunctor K A).map (𝟙 R) f = f := by
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Successive coefficient maps act by their composite. -/
theorem pointGroupFunctor_map_comp_apply {R S T : CommAlgCat.{r, u} K}
    (q : R ⟶ S) (p : S ⟶ T) (f : (pointGroupFunctor K A).obj R) :
    (pointGroupFunctor K A).map (q ≫ p) f =
      (pointGroupFunctor K A).map p ((pointGroupFunctor K A).map q f) := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

end Functor

section AffineComparison

variable {K A R S : Type u} [CommRing K] [CommRing A] [HopfAlgebra K A]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

/-- The existing affine-spectrum equivalence sends the counit point to the
geometric group unit, with no coalgebra structure on the coefficient algebra. -/
@[simp] theorem Spec.mapMulEquiv_convolution_one :
    Spec.mapMulEquiv (R := K) (S := A) (T := R)
      (1 : WithConv (A →ₐ[K] R)) = 1 :=
  (Spec.mapMulEquiv (R := K) (S := A) (T := R)).map_one

/-- The existing affine-spectrum equivalence sends antipode precomposition to
the geometric inverse. Its map and inverse are unchanged. -/
@[simp] theorem Spec.mapMulEquiv_convolutionInverse (f : WithConv (A →ₐ[K] R)) :
    Spec.mapMulEquiv (R := K) (S := A) (T := R) (AlgHom.convolutionInverse f) =
      (Spec.mapMulEquiv (R := K) (S := A) (T := R) f)⁻¹ := by
  let := AlgHom.convolutionGroup K A R
  exact _root_.map_inv (Spec.mapMulEquiv (R := K) (S := A) (T := R)) f

/-- The inverse affine-spectrum comparison reads geometric inversion as
precomposition of coordinates with the source antipode. -/
@[simp] theorem Spec.mapMulEquiv_symm_inv
    (f : (Spec (.of R)).asOver (Spec (.of K)) ⟶
      (Spec (.of A)).asOver (Spec (.of K))) :
    ((Spec.mapMulEquiv (R := K) (S := A) (T := R)).symm (f⁻¹)).ofConv =
      ((Spec.mapMulEquiv (R := K) (S := A) (T := R)).symm f).ofConv.comp
        (HopfAlgebra.antipodeAlgHom K A) := by
  let := AlgHom.convolutionGroup K A R
  rw [_root_.map_inv]
  exact AlgHom.convolutionInverse_ofConv _

/-- Change of coefficients on algebra-valued points is pullback along the
spectrum of the coefficient algebra map. All rings in this comparison have the
same universe, as in `Spec.mapMulEquiv`. -/
theorem Spec.mapMulEquiv_convolutionPostcomp (q : R →ₐ[K] S)
    (f : WithConv (A →ₐ[K] R)) :
    Spec.mapMulEquiv (R := K) (S := A) (T := S) (AlgHom.convolutionPostcomp q f) =
      (Spec.map (CommRingCat.ofHom q.toRingHom)).asOver (Spec (.of K)) ≫
        Spec.mapMulEquiv (R := K) (S := A) (T := R) f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (q.comp f.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)
  exact Spec.map_comp (CommRingCat.ofHom f.ofConv.toRingHom)
    (CommRingCat.ofHom q.toRingHom)

end AffineComparison

end AlgebraicGeometry
