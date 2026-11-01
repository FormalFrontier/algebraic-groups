/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.GeneralLinear
public import AlgebraicGroups.GroupScheme.AffineRepresentation
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# General linear group morphisms of based right comodules

A finite basis of a right comodule over the coordinate Hopf algebra of an affine
group scheme gives a morphism from that group scheme to the general linear group.
The source is the given group scheme, with its given group structure. The
coordinate map evaluates the determinant-localized coordinate ring at the
coefficient matrix of the given coaction.

The construction uses group-valued Yoneda on all schemes over the base. Its
components are the comodule point action, expressed in the scalar-extended basis.
The coordinate formula identifies the underlying scheme morphism with canonical
affinization followed by the spectrum of the coefficient evaluation. If the
matrix coefficients generate the coordinate algebra, this same morphism is a
closed immersion.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8: the determinant-localized
  general linear group; Chapter 4, §c: representations and comodules.
* Mathlib's group-valued Yoneda embedding, scalar-extension bases, matrix algebra
  equivalences, affine spectrum adjunction, and affine closed-immersion criterion.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u v

namespace Coalgebra.RightComodule

variable {K : Type u} [CommRing K]
variable {G : Scheme.{u}} [G.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))] [IsAffine G]
variable {U : Type v} [AddCommGroup U] [Module K U]
variable (X : RightComodule K Γ(G, ⊤) U)
variable {I : Type u} [Fintype I] [DecidableEq I] (b : Module.Basis I K U)

local instance : G.isoSpec.hom.IsOver (Spec (.of K)) :=
  affineCoordinate_isoSpec_hom_isOver (K := K) G

-- Use the monoid parent of the same coordinate Hopf algebra as the point action.
local instance :
    @CategoryTheory.IsMonHom (Over (Spec (.of K))) _ _
      (G.asOver (Spec (.of K))) ((Spec (.of Γ(G, ⊤))).asOver (Spec (.of K)))
      (inferInstance : GrpObj (G.asOver (Spec (.of K)))).toMonObj
      (@AlgebraicGeometry.instMonObjSpecAsOverSpec.{u} (.of K) (.of Γ(G, ⊤))
        (affineCoordinateHopfAlgebra (K := K) G).toHopfAlgebraStruct.toBialgebra)
      (G.isoSpec.asOver (Spec (.of K))).hom :=
  hopfSpectrum_isMonHom (K := K) (A := Γ(G, ⊤))
    (hA := affineCoordinateHopfAlgebra (K := K) G)
    (Grp.mk (G.asOver (Spec (.of K)))) (affineGroupIsoSpec (K := K) G)

-- The bundled `algΓ` algebra and its carrier have definitionally equal module
-- structures; allow their aliases to unfold only while elaborating this composite.
set_option backward.isDefEq.respectTransparency false in
/-- On any scheme over the base, the based comodule action gives a group
homomorphism to the points of the general linear group. The coefficient algebra
is the global-sections algebra furnished by `algΓ`. -/
def generalLinearGroupHomComponent (T : Over (Spec (.of K))) :
    (T ⟶ G.asOver (Spec (.of K))) →*
      (T ⟶ generalLinearGroupUnderlyingScheme K I) := by
  let R : CommAlgCat.{u, u} K := ((algΓ (.of K)).obj T).unop
  let toSpectrum : (T ⟶ G.asOver (Spec (.of K))) →*
      (T ⟶ (Spec (.of Γ(G, ⊤))).asOver (Spec (.of K))) :=
    IsMonHom.monoidHom (G.isoSpec.asOver (Spec (.of K))).hom T
  let toCoordinates : (T ⟶ (Spec (.of Γ(G, ⊤))).asOver (Spec (.of K))) →*
      WithConv (Γ(G, ⊤) →ₐ[K] R) :=
    (affineSpecHomOverMulEquiv K T Γ(G, ⊤)).toMonoidHom
  let toOperators : WithConv (Γ(G, ⊤) →ₐ[K] R) →*
      LinearMap.GeneralLinearGroup R (R ⊗[K] U) :=
    X.pointAction (A := R)
  let toMatrices : LinearMap.GeneralLinearGroup R (R ⊗[K] U) →*
      Matrix.GeneralLinearGroup I R :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).toMonoidHom
  let toGeneralLinearCoordinates : Matrix.GeneralLinearGroup I R →*
      WithConv (CoordinateRing K I →ₐ[K] R) :=
    (generalLinearGroupMulEquivAlgHom K I R).toMonoidHom
  let toPoints : WithConv (CoordinateRing K I →ₐ[K] R) →*
      (T ⟶ generalLinearGroupUnderlyingScheme K I) :=
    (affineSpecHomOverMulEquiv K T (CoordinateRing K I)).symm.toMonoidHom
  exact toPoints.comp (toGeneralLinearCoordinates.comp
    (toMatrices.comp (toOperators.comp (toCoordinates.comp toSpectrum))))

/-- The component is the given point action in the scalar-extended basis,
followed by the two representing equivalences. -/
theorem generalLinearGroupHomComponent_apply (T : Over (Spec (.of K)))
    (g : T ⟶ G.asOver (Spec (.of K))) :
    X.generalLinearGroupHomComponent b T g =
      (affineSpecHomOverMulEquiv K T (CoordinateRing K I)).symm
        (generalLinearGroupMulEquivAlgHom K I ((algΓ (.of K)).obj T).unop
          ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
            (Algebra.TensorProduct.basis ((algΓ (.of K)).obj T).unop b)).toMulEquiv)
              (X.pointAction (affineSpecHomOverMulEquiv K T Γ(G, ⊤)
                (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom))))) := rfl

/-- The entire coordinate map of a component is precomposition with the
coefficient evaluation, not just its restriction to the polynomial entries. -/
theorem generalLinearGroupHomComponent_coordinates (T : Over (Spec (.of K)))
    (g : T ⟶ G.asOver (Spec (.of K))) :
    affineSpecHomOverMulEquiv K T (CoordinateRing K I)
        (X.generalLinearGroupHomComponent b T g) =
      WithConv.toConv
        ((affineSpecHomOverMulEquiv K T Γ(G, ⊤)
          (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom)).ofConv.comp
            (X.generalLinearCoordinateHom b)) := by
  rw [generalLinearGroupHomComponent_apply, MulEquiv.apply_symm_apply]
  apply WithConv.ofConv_injective
  exact (X.generalLinearCoordinateHom_comp b
    (affineSpecHomOverMulEquiv K T Γ(G, ⊤)
      (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom)).ofConv).symm

/-- The component construction is natural for every morphism of over-schemes. -/
theorem generalLinearGroupHomComponent_naturality
    {T T' : Over (Spec (.of K))} (a : T' ⟶ T)
    (g : T ⟶ G.asOver (Spec (.of K))) :
    X.generalLinearGroupHomComponent b T' (a ≫ g) =
      a ≫ X.generalLinearGroupHomComponent b T g := by
  apply (affineSpecHomOverMulEquiv K T' (CoordinateRing K I)).injective
  rw [X.generalLinearGroupHomComponent_coordinates b T' (a ≫ g),
    affineSpecHomOverMulEquiv_naturality_source K T T' (CoordinateRing K I) a
      (X.generalLinearGroupHomComponent b T g),
    X.generalLinearGroupHomComponent_coordinates b T g]
  apply WithConv.ofConv_injective
  rw [Category.assoc,
    affineSpecHomOverMulEquiv_naturality_source K T T' Γ(G, ⊤) a
      (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom)]
  rfl

/-- The based action as a natural transformation on the full category of
schemes over the base. -/
def generalLinearGroupHomTransformation :
    yonedaGrp.obj (Grp.mk (G.asOver (Spec (.of K)))) ⟶
      yonedaGrp.obj (generalLinearGroupScheme K I) where
  app T := GrpCat.ofHom (X.generalLinearGroupHomComponent b T.unop)
  naturality {T T'} a := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact X.generalLinearGroupHomComponent_naturality b a.unop g

/-- Evaluation of the natural transformation is the specified component. -/
@[simp] theorem generalLinearGroupHomTransformation_app
    (T : Over (Spec (.of K))) (g : T ⟶ G.asOver (Spec (.of K))) :
    (X.generalLinearGroupHomTransformation b).app (op T) g =
      X.generalLinearGroupHomComponent b T g := rfl

/-- A based right comodule over the coordinate Hopf algebra defines a morphism
from the given affine group scheme to the finite general linear group. -/
def generalLinearGroupHom :
    Grp.mk (G.asOver (Spec (.of K))) ⟶ generalLinearGroupScheme K I :=
  yonedaGrpFullyFaithful.preimage (X.generalLinearGroupHomTransformation b)

/-- Postcomposition by the group morphism is the specified comodule component
on every over-scheme. -/
theorem generalLinearGroupHom_comp (T : Over (Spec (.of K)))
    (g : T ⟶ G.asOver (Spec (.of K))) :
    g ≫ (X.generalLinearGroupHom b).hom.hom =
      X.generalLinearGroupHomComponent b T g := by
  exact congrArg
    (fun (e : yonedaGrp.obj (Grp.mk (G.asOver (Spec (.of K)))) ⟶
        yonedaGrp.obj (generalLinearGroupScheme K I)) ↦ (e.app (op T)).hom g)
    (yonedaGrpFullyFaithful.map_preimage (X.generalLinearGroupHomTransformation b))

private theorem isoSpec_globalSection_coordinates :
    (affineSpecHomOverMulEquiv K (G.asOver (Spec (.of K))) Γ(G, ⊤)
      (G.isoSpec.asOver (Spec (.of K))).hom).ofConv =
        (affineCoordinateAlgEquiv (K := K) G).toAlgHom := by
  have hΓ : (Scheme.ΓSpecIso Γ(G, ⊤)).inv ≫ G.isoSpec.hom.appTop =
      𝟙 Γ(G, ⊤) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(G, ⊤)).inv_hom_id
  have h : CommRingCat.ofHom
      (affineSpecHomOverMulEquiv K (G.asOver (Spec (.of K))) Γ(G, ⊤)
        (G.isoSpec.asOver (Spec (.of K))).hom).ofConv.toRingHom =
      𝟙 (CommRingCat.of Γ(G, ⊤)) :=
    (affineSpecHomOverMulEquiv_apply_toRingHom K (G.asOver (Spec (.of K)))
      Γ(G, ⊤) (G.isoSpec.asOver (Spec (.of K))).hom).trans hΓ
  apply AlgHom.ext
  intro a
  change (affineSpecHomOverMulEquiv K (G.asOver (Spec (.of K))) Γ(G, ⊤)
    (G.isoSpec.asOver (Spec (.of K))).hom).ofConv a = a
  exact congrArg (fun f : CommRingCat.of Γ(G, ⊤) ⟶ Γ(G, ⊤) ↦ f.hom a) h

-- Comparing the component formula at `G` needs the stored localization and
-- global-sections ring parents to unfold through their canonical aliases.
set_option backward.isDefEq.respectTransparency false in
/-- The underlying scheme morphism is affinization followed by the spectrum of
coefficient evaluation. This identifies the map constructed by full Yoneda. -/
theorem generalLinearGroupHom_left :
    (X.generalLinearGroupHom b).hom.hom.left =
      G.isoSpec.hom ≫ Spec.map
        (CommRingCat.ofHom (X.generalLinearCoordinateHom b).toRingHom) := by
  have h := X.generalLinearGroupHom_comp b (G.asOver (Spec (.of K))) (𝟙 _)
  rw [Category.id_comp] at h
  have hc : X.generalLinearGroupHomComponent b (G.asOver (Spec (.of K))) (𝟙 _) =
      (affineSpecHomOverMulEquiv K (G.asOver (Spec (.of K))) (CoordinateRing K I)).symm
        (WithConv.toConv ((affineCoordinateAlgEquiv (K := K) G).toAlgHom.comp
          (X.generalLinearCoordinateHom b))) := by
    apply (affineSpecHomOverMulEquiv K (G.asOver (Spec (.of K)))
      (CoordinateRing K I)).injective
    simpa only [Category.id_comp, isoSpec_globalSection_coordinates,
      MulEquiv.apply_symm_apply] using
      X.generalLinearGroupHomComponent_coordinates b (G.asOver (Spec (.of K))) (𝟙 _)
  rw [h, hc, affineSpecHomOverMulEquiv_symm_apply_left, Scheme.isoSpec_hom]
  rfl

/-- The constructed underlying scheme map commutes with the given base maps. -/
theorem generalLinearGroupHom_over :
    (X.generalLinearGroupHom b).hom.hom.left ≫
        (generalLinearGroupUnderlyingScheme K I).hom = G ↘ Spec (.of K) :=
  (X.generalLinearGroupHom b).hom.hom.w

/-- The underlying scheme morphism is a morphism over the base. -/
instance generalLinearGroupHom_isOver :
    (X.generalLinearGroupHom b).hom.hom.left.IsOver (Spec (.of K)) where
  comp_over := X.generalLinearGroupHom_over b

/-- The underlying over-morphism preserves the given monoid structures. -/
theorem generalLinearGroupHom_isMonHom :
    IsMonHom (X.generalLinearGroupHom b).hom.hom :=
  (X.generalLinearGroupHom b).hom.isMonHom_hom

/-- The group morphism preserves the unit of the given group object. -/
theorem generalLinearGroupHom_one :
    η[G.asOver (Spec (.of K))] ≫ (X.generalLinearGroupHom b).hom.hom =
      η[generalLinearGroupUnderlyingScheme K I] :=
  IsMonHom.one_hom _

/-- The group morphism preserves multiplication in the given order. -/
theorem generalLinearGroupHom_mul :
    μ[G.asOver (Spec (.of K))] ≫ (X.generalLinearGroupHom b).hom.hom =
      ((X.generalLinearGroupHom b).hom.hom ⊗ₘ (X.generalLinearGroupHom b).hom.hom) ≫
        μ[generalLinearGroupUnderlyingScheme K I] :=
  IsMonHom.mul_hom _

/-- The group morphism commutes with inversion. -/
theorem generalLinearGroupHom_inv :
    ι[G.asOver (Spec (.of K))] ≫ (X.generalLinearGroupHom b).hom.hom =
      (X.generalLinearGroupHom b).hom.hom ≫ ι[generalLinearGroupUnderlyingScheme K I] :=
  GrpObj.inv_hom _

/-- Pullback on all global sections of the target, normalized by the spectrum
isomorphism, is the coefficient evaluation on the entire coordinate ring. -/
theorem generalLinearGroupHom_appTop :
    (Scheme.ΓSpecIso (.of (CoordinateRing K I))).inv ≫
        (X.generalLinearGroupHom b).hom.hom.left.appTop =
      CommRingCat.ofHom (X.generalLinearCoordinateHom b).toRingHom := by
  rw [generalLinearGroupHom_left, Scheme.isoSpec_hom]
  exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (X.generalLinearCoordinateHom b).toRingHom)

/-- The normalized pullback formula evaluated at an arbitrary coordinate. -/
theorem generalLinearGroupHom_appTop_apply (q : CoordinateRing K I) :
    (X.generalLinearGroupHom b).hom.hom.left.appTop
        ((coordinateSpecEquiv (K := K) (C := CoordinateRing K I)).symm q) =
      X.generalLinearCoordinateHom b q := by
  rw [coordinateSpecEquiv_symm_apply]
  exact congrArg
    (fun f : CommRingCat.of (CoordinateRing K I) ⟶ Γ(G, ⊤) ↦ f q)
    (X.generalLinearGroupHom_appTop b)

/-- Pullback of a matrix-entry coordinate is the corresponding coefficient of
the original coaction. -/
theorem generalLinearGroupHom_appTop_matrix (i j : I) :
    (X.generalLinearGroupHom b).hom.hom.left.appTop
        ((coordinateSpecEquiv (K := K) (C := CoordinateRing K I)).symm
          (matrix K I i j)) = X.coefficient (b.coord i) (b j) := by
  rw [generalLinearGroupHom_appTop_apply, generalLinearCoordinateHom_matrix]

/-- Pullback of the inverse-determinant coordinate is the inverse determinant
of the coefficient-matrix unit. -/
theorem generalLinearGroupHom_appTop_detInverse :
    (X.generalLinearGroupHom b).hom.hom.left.appTop
        ((coordinateSpecEquiv (K := K) (C := CoordinateRing K I)).symm
          (detInverse K I)) =
      (↑((Matrix.GeneralLinearGroup.det
        (HopfAlgebra.coefficientMatrixUnit (R := K)
          (fun i j : I ↦ X.coefficient (b.coord i) (b j))
          (X.comul_coefficient_basis b) (X.counit_coefficient_basis b)))⁻¹) : Γ(G, ⊤)) := by
  rw [generalLinearGroupHom_appTop_apply, generalLinearCoordinateHom_detInverse]

/-- Postcomposition at every geometric algebra point gives precisely the matrix
of the original comodule point action. -/
theorem generalLinearGroupHom_point (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    g ≫ (X.generalLinearGroupHom b).hom.hom =
      generalLinearGroupMulEquivPoints K I R
        ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
          (Algebra.TensorProduct.basis R b)).toMulEquiv)
            (X.pointAction (affinePointMulEquiv G R g))) := by
  let g0 : Spec (.of R) ⟶ G := g.left
  let φ : WithConv (Γ(G, ⊤) →ₐ[K] R) := affinePointMulEquiv G R g
  let Φ : CommRingCat.of (CoordinateRing K I) ⟶ Γ(G, ⊤) :=
    CommRingCat.ofHom (X.generalLinearCoordinateHom b).toRingHom
  let ψ : Γ(G, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom φ.ofConv.toRingHom
  let M : Matrix.GeneralLinearGroup I R :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv (X.pointAction φ)
  have hφ : Spec.map ψ = g0 ≫ G.isoSpec.hom :=
    affinePointMulEquiv_spec_map G R g
  have hc : Φ ≫ ψ = CommRingCat.ofHom
      (generalLinearGroupMulEquivAlgHom K I R M).ofConv.toRingHom :=
    congrArg (fun f : CoordinateRing K I →ₐ[K] R ↦ CommRingCat.ofHom f.toRingHom)
      (X.generalLinearCoordinateHom_comp b φ.ofConv)
  have hp : g0 ≫ G.isoSpec.hom ≫ Spec.map Φ =
      (generalLinearGroupMulEquivPoints K I R M).left := by
    have hmap : Spec.map (Φ ≫ ψ) =
        (generalLinearGroupMulEquivPoints K I R M).left :=
      (congrArg
        (fun f : CommRingCat.of (CoordinateRing K I) ⟶ CommRingCat.of R ↦ Spec.map f)
        hc).trans (generalLinearGroupMulEquivPoints_apply_left K I R M).symm
    exact (Category.assoc g0 G.isoSpec.hom (Spec.map Φ)).symm.trans
      ((congrArg (fun k : Spec (.of R) ⟶ Spec Γ(G, ⊤) ↦ k ≫ Spec.map Φ) hφ.symm).trans
        ((Spec.map_comp Φ ψ).symm.trans hmap))
  apply Over.OverMorphism.ext
  change g0 ≫ (X.generalLinearGroupHom b).hom.hom.left = _
  exact (congrArg (fun f : G ⟶ Spec (.of (CoordinateRing K I)) ↦ g0 ≫ f)
    (X.generalLinearGroupHom_left b)).trans hp

/-- Decoding a postcomposed geometric point returns the same automorphism on
`R ⊗[K] U` as evaluation of the given comodule. -/
theorem generalLinearGroupHom_point_operator
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        ((generalLinearGroupMulEquivPoints K I R).symm
          (g ≫ (X.generalLinearGroupHom b).hom.hom)) =
      X.pointAction (affinePointMulEquiv G R g) := by
  rw [generalLinearGroupHom_point, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

/-- On every tensor, the decoded geometric operator is evaluation of the
given coaction on the same scalar-extended module. -/
theorem generalLinearGroupHom_point_val
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        ((generalLinearGroupMulEquivPoints K I R).symm
          (g ≫ (X.generalLinearGroupHom b).hom.hom))).val =
      X.evaluate (affinePointMulEquiv G R g).ofConv.toLinearMap := by
  rw [generalLinearGroupHom_point_operator]
  exact X.pointAction_val
    (affinePointMulEquiv G R g : WithConv (Γ(G, ⊤) →ₐ[K] R))

/-- The pure-tensor formula of the geometric operator retains the specified
coaction, with the coalgebra factor moved to the coefficient side. -/
theorem generalLinearGroupHom_point_tmul
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (s : R) (x : U) :
    ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        ((generalLinearGroupMulEquivPoints K I R).symm
          (g ≫ (X.generalLinearGroupHom b).hom.hom))).val (s ⊗ₜ[K] x) =
      s • _root_.TensorProduct.map (affinePointMulEquiv G R g).ofConv.toLinearMap
        (LinearMap.id : U →ₗ[K] U)
        (TensorProduct.comm K U Γ(G, ⊤) (X.coaction x)) := by
  rw [generalLinearGroupHom_point_val, evaluate_tmul]

/-- Every change of geometric test algebra intertwines the decoded operators
on all tensors. No injectivity of the tensor comparison is needed. -/
theorem generalLinearGroupHom_point_naturality
    {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (q : R →ₐ[K] R')
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : R ⊗[K] U) :
    _root_.TensorProduct.map q.toLinearMap (LinearMap.id : U →ₗ[K] U)
        (((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
          (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
            ((generalLinearGroupMulEquivPoints K I R).symm
              (g ≫ (X.generalLinearGroupHom b).hom.hom))).val z) =
      ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Algebra.TensorProduct.basis R' b)).toMulEquiv).symm
          ((generalLinearGroupMulEquivPoints K I R').symm
            (((Spec.map (CommRingCat.ofHom q.toRingHom)).asOver (Spec (.of K)) ≫ g) ≫
              (X.generalLinearGroupHom b).hom.hom))).val
        (_root_.TensorProduct.map q.toLinearMap (LinearMap.id : U →ₗ[K] U) z) := by
  rw [X.generalLinearGroupHom_point_val b R g,
    X.generalLinearGroupHom_point_val b R'
      ((Spec.map (CommRingCat.ofHom q.toRingHom)).asOver (Spec (.of K)) ≫ g)]
  have hc :
      (affinePointMulEquiv G R'
        ((Spec.map (CommRingCat.ofHom q.toRingHom)).asOver (Spec (.of K)) ≫ g)).ofConv.toLinearMap =
      q.toLinearMap.comp (affinePointMulEquiv G R g).ofConv.toLinearMap := by
    apply LinearMap.ext
    intro a
    exact congrArg (fun p : WithConv (Γ(G, ⊤) →ₐ[K] R') ↦ p.ofConv a)
      (AlgebraicGeometry.affinePointMulEquiv_naturality (K := K) G q g)
  rw [hc]
  exact X.evaluate_naturality_apply (affinePointMulEquiv G R g).ofConv.toLinearMap q z

/-- The decoded operator agrees with the existing geometric
representation–comodule correspondence. -/
theorem generalLinearGroupHom_point_geometricRepresentation
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        ((generalLinearGroupMulEquivPoints K I R).symm
          (g ≫ (X.generalLinearGroupHom b).hom.hom)) =
      ((GeometricRepresentation.rightComoduleEquiv (G := G) (V := U)).symm X).app R
        (ULift.up g) := by
  rw [generalLinearGroupHom_point_operator,
    GeometricRepresentation.rightComoduleEquiv_symm_app]

/-- The decoded operator agrees with the geometric action of the coordinate
representation reconstructed from the same coaction. -/
theorem generalLinearGroupHom_point_affineRepresentation
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Algebra.TensorProduct.basis R b)).toMulEquiv).symm
        ((generalLinearGroupMulEquivPoints K I R).symm
          (g ≫ (X.generalLinearGroupHom b).hom.hom)) =
      AffineRepresentation.geometricAction
        (PointRepresentation.ofRightComodule.{u, u, v, 0} X) R g := by
  rw [generalLinearGroupHom_point_operator, AffineRepresentation.geometricAction_apply,
    PointRepresentation.pointAction_ofRightComodule]

/-- A group morphism is determined by the specified components on all
over-schemes. -/
theorem generalLinearGroupHom_unique
    (ρ : Grp.mk (G.asOver (Spec (.of K))) ⟶ generalLinearGroupScheme K I)
    (hρ : ∀ (T : Over (Spec (.of K))) (g : T ⟶ G.asOver (Spec (.of K))),
      g ≫ ρ.hom.hom = X.generalLinearGroupHomComponent b T g) :
    ρ = X.generalLinearGroupHom b := by
  apply Grp.hom_ext
  have h := (hρ (G.asOver (Spec (.of K))) (𝟙 _)).trans
    (X.generalLinearGroupHom_comp b (G.asOver (Spec (.of K))) (𝟙 _)).symm
  simpa only [Category.id_comp] using h

/-- The matrix formula on all algebra-valued geometric points uniquely
determines the bundled group morphism. -/
theorem generalLinearGroupHom_unique_of_points
    (ρ : Grp.mk (G.asOver (Spec (.of K))) ⟶ generalLinearGroupScheme K I)
    (hρ : ∀ (R : Type u) [CommRing R] [Algebra K R]
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
      g ≫ ρ.hom.hom = generalLinearGroupMulEquivPoints K I R
        ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv
          (Algebra.TensorProduct.basis R b)).toMulEquiv)
            (X.pointAction (affinePointMulEquiv G R g)))) :
    ρ = X.generalLinearGroupHom b := by
  apply Grp.hom_ext
  apply (cancel_epi (G.isoSpec.asOver (Spec (.of K))).inv).1
  exact (hρ Γ(G, ⊤) (G.isoSpec.asOver (Spec (.of K))).inv).trans
    (X.generalLinearGroupHom_point b Γ(G, ⊤)
      (G.isoSpec.asOver (Spec (.of K))).inv).symm

/-- If the matrix coefficients generate the affine coordinate algebra, the
same general linear group morphism is a closed immersion. The sufficient
hypothesis concerns coefficients only; no generation condition is imposed on
the inverse-determinant coordinate. -/
theorem generalLinearGroupHom_isClosedImmersion
    (hgen : Algebra.adjoin K
      (Set.range (Function.uncurry (fun i j : I ↦
        X.coefficient (b.coord i) (b j)))) = ⊤) :
    IsClosedImmersion (X.generalLinearGroupHom b).hom.hom.left := by
  have hΦ : Function.Surjective (X.generalLinearCoordinateHom b) := by
    apply (AlgHom.range_eq_top _).mp
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨matrix K I i j, X.generalLinearCoordinateHom_matrix b i j⟩
  have hsurj : Function.Surjective
      ((Scheme.ΓSpecIso (.of (CoordinateRing K I))).inv ≫
        (X.generalLinearGroupHom b).hom.hom.left.appTop) := by
    rw [generalLinearGroupHom_appTop]
    exact hΦ
  exact IsClosedImmersion.of_surjective_of_isAffine
    (X := G) (Y := Spec (.of (CoordinateRing K I)))
    (X.generalLinearGroupHom b).hom.hom.left (Function.Surjective.of_comp hsurj)

end Coalgebra.RightComodule
