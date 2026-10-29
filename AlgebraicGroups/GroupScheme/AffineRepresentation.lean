/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineHomOverConvolution
public import AlgebraicGroups.GroupScheme.RepresentationFiltration
public import AlgebraicGroups.GroupScheme.AdditiveComodule
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom

/-!
# Coordinate representations of affine group schemes

An affine group over `Spec K` has its canonical Hopf algebra on the ring
`Γ(G, ⊤)`. The fully faithful monoidal roundtrip identifies the group on its
spectrum with the group transported along `G.isoSpec`. Thus global sections of
a geometric point give a multiplicative, natural coordinate comparison.

`affinePointGroupFunctor` is the coordinate extension to independently sized
coefficient algebras. Its comparison with geometric points is restricted to the
scheme universe. `AffineRepresentation` uses this extension and the general
linear functor of `R ⊗[K] V`, including when `V` is infinite-dimensional.
Its comodule, invariant-submodule, intertwiner, finite-stage and change-of-test-
level APIs are the existing `PointRepresentation` APIs on the same module and
its original submodule subtypes.

For a group presented as `Spec C`, `coordinateSpecEquiv` normalizes the
canonical coordinate Hopf algebra to the original, specified Hopf algebra `C`.
The polynomial regular representation of the additive group exercises this
normalization without changing its symmetric-algebra coacting coalgebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c, Proposition 4.7 and
  Corollary 4.8. The arbitrary-coalgebra core is a generalization of the
  coordinate-algebra statement; here it is specialized to global sections.
* Mathlib's `AlgebraicGeometry/Group/Affine`, `CommHopfAlgCat`, fully faithful
  monoidal functors, and group-valued Yoneda constructions.
* The right-comodule evaluation, reconstruction, finite-family gluing and
  coefficient-universe formalizations in this library.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite WithConv
open scoped TensorProduct

universe u v w t s r q

namespace AlgebraicGeometry

section Coordinates

open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

section HopfSpectrum

/-- The monoidal structure on algebraic spectrum induced by its braided structure. -/
local instance algSpecMonoidal (B : CommRingCat.{u}) : (algSpec B).Monoidal :=
  (braidedAlgSpec (R := B)).toMonoidal

/-- The lax monoidal structure underlying braided algebraic spectrum. -/
local instance algSpecLaxMonoidal (B : CommRingCat.{u}) : (algSpec B).LaxMonoidal :=
  (braidedAlgSpec (R := B)).toMonoidal.toLaxMonoidal

/-- The oplax monoidal structure underlying braided algebraic spectrum. -/
local instance algSpecOplaxMonoidal (B : CommRingCat.{u}) : (algSpec B).OplaxMonoidal :=
  (braidedAlgSpec (R := B)).toMonoidal.toOplaxMonoidal

/-- Passing the Hopf-algebra equivalence's counit from the opposite category
to cogroup algebras gives the identity on the underlying algebra object. -/
theorem hopfAlgEquivalence_counit_unop_hom (B : CommRingCat.{u})
    (L : Grp ((CommAlgCat.{u, u} B)ᵒᵖ)) :
    (((commHopfAlgCatEquivCogrpCommAlgCat B).counitIso.app (op L)).unop.hom).hom.hom =
      𝟙 L.X := rfl

/-- Applying algebraic spectrum to the counit retains its identity carrier. -/
theorem algSpec_mapGrp_counit_unop_hom (B : CommRingCat.{u})
    (L : Grp ((CommAlgCat.{u, u} B)ᵒᵖ)) :
    ((algSpec B).mapGrp.map
      ((commHopfAlgCatEquivCogrpCommAlgCat B).counitIso.app (op L)).unop.hom).hom.hom =
        𝟙 ((algSpec B).obj L.X) := by
  apply Over.OverMorphism.ext
  change ((algSpec B).map
    (((commHopfAlgCatEquivCogrpCommAlgCat B).counitIso.app (op L)).unop.hom).hom.hom).left = _
  rw [algSpec_map_left]
  change Spec.map (𝟙 (CommRingCat.of L.X.unop)) = 𝟙 (Spec (CommRingCat.of L.X.unop))
  exact Spec.map_id _

/-- Reconstructing a Hopf algebra from a cogroup and taking its spectrum
recovers the complete monoid data on algebraic spectrum. -/
theorem algSpec_hopfAlg_roundtrip_toMonObj (B : CommRingCat.{u})
    (L : Grp ((CommAlgCat.{u, u} B)ᵒᵖ)) :
    ((hopfSpec B).obj
      (op ((commHopfAlgCatEquivCogrpCommAlgCat B).inverse.obj (op L)))).grp.toMonObj =
        ((algSpec B).mapGrp.obj L).grp.toMonObj := by
  let E := commHopfAlgCatEquivCogrpCommAlgCat B
  let R : Grp ((CommAlgCat.{u, u} B)ᵒᵖ) := (E.functor.obj (E.inverse.obj (op L))).unop
  let c : L ≅ R := (E.counitIso.app (op L)).unop
  let X : Over (Spec B) := (algSpec B).obj L.X
  let mL : MonObj X := ((algSpec B).mapGrp.obj L).grp.toMonObj
  let mR : MonObj X := ((algSpec B).mapGrp.obj R).grp.toMonObj
  let f : X ⟶ X := ((algSpec B).mapGrp.map c.hom).hom.hom
  have hf : f = 𝟙 X := algSpec_mapGrp_counit_unop_hom B L
  have hm : @IsMonHom (Over (Spec B)) inferInstance inferInstance X X mL mR f :=
    Mon.Hom.isMonHom_hom (((algSpec B).mapGrp.map c.hom).hom)
  have hmul : mL.mul ≫ f = (f ⊗ₘ f) ≫ mR.mul :=
    @IsMonHom.mul_hom (Over (Spec B)) inferInstance inferInstance X X mL mR f hm
  have h : mL.mul = mR.mul := by
    calc
      mL.mul = mL.mul ≫ 𝟙 X := (Category.comp_id _).symm
      _ = mL.mul ≫ f := congrArg (fun k : X ⟶ X ↦ mL.mul ≫ k) hf.symm
      _ = (f ⊗ₘ f) ≫ mR.mul := hmul
      _ = (𝟙 X ⊗ₘ 𝟙 X) ≫ mR.mul :=
        congrArg (fun k : X ⟶ X ↦ (k ⊗ₘ k) ≫ mR.mul) hf
      _ = mR.mul := by rw [id_tensorHom_id, Category.id_comp]
  exact MonObj.ext mR mL h.symm

/-- Hopf spectrum is the bundled spectrum group for the same specified Hopf
algebra, including its structure morphism, monoid data and inverse. -/
theorem hopfSpec_obj_eq (B A : CommRingCat.{u}) [h : HopfAlgebra B A] :
    (hopfSpec B).obj (op (CommHopfAlgCat.of B A)) =
      { X := (Spec A).asOver (Spec B),
        grp := @instGrpObjSpecAsOverSpec.{u} B A h } := rfl

/-- The monoid underlying Hopf spectrum is the monoid parent of the
spectrum group structure for the same Hopf algebra. -/
theorem hopfSpec_obj_toMonObj (B A : CommRingCat.{u}) [h : HopfAlgebra B A] :
    ((hopfSpec B).obj (op (CommHopfAlgCat.of B A))).grp.toMonObj =
      (@instGrpObjSpecAsOverSpec.{u} B A h).toMonObj := rfl

end HopfSpectrum

variable {K : Type u} [CommRing K] (G : Scheme.{u})
  [G.Over (Spec (.of K))] [IsAffine G]

/-- Global sections of an affine scheme over `Spec K` carry the canonical
`K`-algebra structure obtained from the bundled base ring. -/
instance (priority := 50) affineCoordinateAlgebra : Algebra K Γ(G, ⊤) :=
  (fun (R : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec R)] [IsAffine X] ↦
    (inferInstance : Algebra R Γ(X, ⊤))) (.of K) G

/-- Canonical affinization commutes with the original structure map to the base. -/
theorem affineCoordinate_isoSpec_hom_isOver :
    G.isoSpec.hom.IsOver (Spec (.of K)) :=
  (fun (R : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec R)] [IsAffine X] ↦
    (inferInstance : X.isoSpec.hom.IsOver (Spec R))) (.of K) G

local instance : G.isoSpec.hom.IsOver (Spec (.of K)) :=
  affineCoordinate_isoSpec_hom_isOver (K := K) G

/-- Global sections of an affine monoid scheme carry the canonical bialgebra
structure obtained from the bundled base ring. -/
instance (priority := 50) affineCoordinateBialgebra [MonObj (G.asOver (Spec (.of K)))] :
    Bialgebra K Γ(G, ⊤) :=
  (fun (R : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec R)]
    [MonObj (X.asOver (Spec R))] [IsAffine X] ↦
    (inferInstance : Bialgebra R Γ(X, ⊤))) (.of K) G

/-- The algebra underlying the coordinate bialgebra is the canonical
algebra on global sections. -/
theorem affineCoordinateBialgebra_toAlgebra [MonObj (G.asOver (Spec (.of K)))] :
    (affineCoordinateBialgebra (K := K) G).toAlgebra =
      affineCoordinateAlgebra (K := K) G := rfl

/-- Global sections of an affine group scheme carry the canonical Hopf algebra
structure obtained from the bundled base ring. -/
instance affineCoordinateHopfAlgebra [GrpObj (G.asOver (Spec (.of K)))] :
    HopfAlgebra K Γ(G, ⊤) :=
  (fun (R : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec R)]
    [GrpObj (X.asOver (Spec R))] [IsAffine X] ↦
    (inferInstance : HopfAlgebra R Γ(X, ⊤))) (.of K) G

/-- The canonical affine algebra map agrees with pullback of the structure
morphism, normalized by the spectrum global-sections isomorphism. -/
theorem affineCoordinate_algebraMap :
    CommRingCat.ofHom (algebraMap K Γ(G, ⊤)) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ (G ↘ Spec (.of K)).appTop := by
  change CommRingCat.ofHom (algebraMap (CommRingCat.of K) Γ(G, ⊤)) = _
  rw [algebraMap_presheafObj (R := CommRingCat.of K) (X := G)]
  change (Spec.fullyFaithful.preimage (G.isoSpec.inv ≫ G ↘ Spec (.of K))).unop = _
  apply Spec.map_injective
  rw [Spec.map_preimage_unop, Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact (Scheme.isoSpec_inv_naturality (G ↘ Spec (.of K))).symm

/-- The canonical affine coordinate algebra and the algebra supplied by `algΓ`
are identified by the identity on their common ring of global sections. -/
def affineCoordinateAlgEquiv :
    Γ(G, ⊤) ≃ₐ[K] ((algΓ (.of K)).obj (G.asOver (Spec (.of K)))).unop where
  toRingEquiv := RingEquiv.refl _
  commutes' k := by
    have h := (affineCoordinate_algebraMap (K := K) G).trans
      (algΓ_obj_algebraMap K (G.asOver (Spec (.of K)))).symm
    exact congrArg (fun f ↦ f k) h

@[simp] theorem affineCoordinateAlgEquiv_apply (x : Γ(G, ⊤)) :
    affineCoordinateAlgEquiv (K := K) G x = x := rfl

@[simp] theorem affineCoordinateAlgEquiv_symm_apply (x : Γ(G, ⊤)) :
    (affineCoordinateAlgEquiv (K := K) G).symm x = x := rfl

variable [GrpObj (G.asOver (Spec (.of K)))]

/-- The bialgebra underlying the coordinate Hopf algebra is the canonical
coordinate bialgebra. -/
theorem affineCoordinateHopfAlgebra_toBialgebra :
    (affineCoordinateHopfAlgebra (K := K) G).toHopfAlgebraStruct.toBialgebra =
      affineCoordinateBialgebra (K := K) G := rfl

/-- The algebra underlying the coordinate Hopf algebra is the canonical
algebra on global sections. -/
theorem affineCoordinateHopfAlgebra_toAlgebra :
    (affineCoordinateHopfAlgebra (K := K) G).toHopfAlgebraStruct.toBialgebra.toAlgebra =
      affineCoordinateAlgebra (K := K) G := by
  rw [affineCoordinateHopfAlgebra_toBialgebra, affineCoordinateBialgebra_toAlgebra]

-- The target over-structure uses the algebra parent of the coordinate Hopf algebra.
private theorem affineCoordinate_group_isoSpec_hom_isOver :
    G.isoSpec.hom.IsOver (Spec (.of K)) where
  comp_over := by
    change G.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(G, ⊤))) = G ↘ Spec (.of K)
    have h : CommRingCat.ofHom (algebraMap K Γ(G, ⊤)) =
        (Scheme.ΓSpecIso (.of K)).inv ≫ (G ↘ Spec (.of K)).appTop :=
      affineCoordinate_algebraMap (K := K) G
    rw [h, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

local instance : G.isoSpec.hom.IsOver (Spec (.of K)) :=
  affineCoordinate_group_isoSpec_hom_isOver (K := K) G

/-- The monoid on the coordinate spectrum induced by the coordinate bialgebra. -/
local instance affineCoordinateSpecMonObj : MonObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K))) :=
  @instMonObjSpecAsOverSpec.{u} (CommRingCat.of K) (CommRingCat.of Γ(G, ⊤))
    (affineCoordinateBialgebra (K := K) G)

/-- The group on the coordinate spectrum induced by the coordinate Hopf algebra. -/
local instance affineCoordinateSpecGrpObj : GrpObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K))) :=
  @instGrpObjSpecAsOverSpec.{u} (CommRingCat.of K) (CommRingCat.of Γ(G, ⊤))
    (affineCoordinateHopfAlgebra (K := K) G)

/-- The fully faithful reconstruction of the coordinate bialgebra recovers the
transported unit on its spectrum. -/
theorem affineCoordinate_spec_one :
    η[(Spec Γ(G, ⊤)).asOver (Spec (.of K))] =
      η[G.asOver (Spec (.of K))] ≫ (G.isoSpec.asOver (Spec (.of K))).hom := by
  let B : CommRingCat.{u} := CommRingCat.of K
  let braided := braidedAlgSpec (R := B)
  let monoidal : (algSpec B).Monoidal := braided.toMonoidal
  let _ : (algSpec B).LaxMonoidal := monoidal.toLaxMonoidal
  let _ : (algSpec B).OplaxMonoidal := monoidal.toOplaxMonoidal
  let A : CommAlgCat.{u, u} B := CommAlgCat.of B Γ(G, ⊤)
  let a : (CommAlgCat.{u, u} B)ᵒᵖ := op A
  let hF : (algSpec B).FullyFaithful := algSpec.fullyFaithful (R := B)
  let e : G.asOver (Spec B) ≅ (algSpec B).obj a := G.isoSpec.asOver (Spec B)
  change Functor.LaxMonoidal.ε (algSpec B) ≫ (algSpec B).map
    (hF.preimage
      (Functor.OplaxMonoidal.η (algSpec B) ≫ (η[G.asOver (Spec B)] ≫ e.hom))) = _
  rw [hF.map_preimage]
  simp only [← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]
  rfl

/-- The multiplication roundtrip cancels the lax and oplax comparisons. In
particular it compares the canonical coordinate bialgebra with the transported
monoid structure. -/
theorem affineCoordinate_spec_mul :
    μ[(Spec Γ(G, ⊤)).asOver (Spec (.of K))] =
      ((G.isoSpec.asOver (Spec (.of K))).inv ⊗ₘ
        (G.isoSpec.asOver (Spec (.of K))).inv) ≫
          μ[G.asOver (Spec (.of K))] ≫ (G.isoSpec.asOver (Spec (.of K))).hom := by
  let B : CommRingCat.{u} := CommRingCat.of K
  let braided := braidedAlgSpec (R := B)
  let monoidal : (algSpec B).Monoidal := braided.toMonoidal
  let _ : (algSpec B).LaxMonoidal := monoidal.toLaxMonoidal
  let _ : (algSpec B).OplaxMonoidal := monoidal.toOplaxMonoidal
  let A : CommAlgCat.{u, u} B := CommAlgCat.of B Γ(G, ⊤)
  let a : (CommAlgCat.{u, u} B)ᵒᵖ := op A
  let hF : (algSpec B).FullyFaithful := algSpec.fullyFaithful (R := B)
  let e : G.asOver (Spec B) ≅ (algSpec B).obj a := G.isoSpec.asOver (Spec B)
  change Functor.LaxMonoidal.μ (algSpec B) a a ≫ (algSpec B).map
    (hF.preimage
      (Functor.OplaxMonoidal.δ (algSpec B) a a ≫
        ((e.inv ⊗ₘ e.inv) ≫ μ[G.asOver (Spec B)] ≫ e.hom))) = _
  rw [hF.map_preimage]
  simp only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]
  rfl

/-- Equality of the monoid data on `Spec Γ(G)` with transport from `G`. -/
theorem affineCoordinate_specMonObj_eq :
    (inferInstance : MonObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K)))) =
      MonObj.ofIso (G.isoSpec.asOver (Spec (.of K))) := by
  apply MonObj.ext
  exact affineCoordinate_spec_mul (K := K) G

/-- The group structure on the coordinate spectrum has the monoid structure
induced by the coordinate bialgebra. -/
theorem affineCoordinate_specGrpObj_toMonObj :
    (inferInstance : GrpObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K)))).toMonObj =
      (inferInstance : MonObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K)))) := by
  change @instMonObjSpecAsOverSpec.{u} (CommRingCat.of K) (CommRingCat.of Γ(G, ⊤))
      ((affineCoordinateHopfAlgebra (K := K) G).toHopfAlgebraStruct.toBialgebra) =
    @instMonObjSpecAsOverSpec.{u} (CommRingCat.of K) (CommRingCat.of Γ(G, ⊤))
      (affineCoordinateBialgebra (K := K) G)
  rfl

/-- Hopf-Spec gives the coordinate spectrum the same underlying monoid structure
as the coordinate bialgebra. -/
theorem affineCoordinate_hopfSpec_toMonObj :
    ((hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K Γ(G, ⊤)))).grp.toMonObj =
      (inferInstance : MonObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K)))) := by
  exact (hopfSpec_obj_toMonObj (CommRingCat.of K) (CommRingCat.of Γ(G, ⊤))
    (h := affineCoordinateHopfAlgebra (K := K) G)).trans
      (affineCoordinate_specGrpObj_toMonObj (K := K) G)

/-- The inverse data agree as well, by uniqueness of the inverse for the
already identified monoid data. -/
theorem affineCoordinate_specGrpObj_eq :
    (inferInstance : GrpObj ((Spec Γ(G, ⊤)).asOver (Spec (.of K)))) =
      GrpObj.ofIso (G.isoSpec.asOver (Spec (.of K))) := by
  apply GrpObj.ext
  rw [affineCoordinate_specGrpObj_toMonObj]
  exact affineCoordinate_specMonObj_eq (K := K) G

/-- Affinization is a group morphism for the canonical coordinate Hopf algebra. -/
instance isMonHom_isoSpec_hom :
    IsMonHom (G.isoSpec.asOver (Spec (.of K))).hom := by
  let Y : Over (Spec (.of K)) := G.asOver (Spec (.of K))
  let X : Over (Spec (.of K)) := (Spec Γ(G, ⊤)).asOver (Spec (.of K))
  let e : Y ≅ X := G.isoSpec.asOver (Spec (.of K))
  let mSource : MonObj Y := inferInstance
  let mTarget : MonObj X := inferInstance
  change @IsMonHom (Over (Spec (.of K))) _ _ Y X mSource mTarget e.hom
  have hTarget : mTarget = @MonObj.ofIso (Over (Spec (.of K))) _ _ Y X mSource e :=
    affineCoordinate_specMonObj_eq (K := K) G
  have hStock : @IsMonHom (Over (Spec (.of K))) _ _ Y X mSource
      (@MonObj.ofIso (Over (Spec (.of K))) _ _ Y X mSource e) e.hom :=
    @CategoryTheory.isMonHom_ofIso (Over (Spec (.of K))) _ _ Y X mSource e
  exact Eq.mpr
    (congrArg (fun m : MonObj X ↦
      @IsMonHom (Over (Spec (.of K))) _ _ Y X mSource m e.hom) hTarget) hStock

/-- The inverse affinization is a group morphism for the same structures. -/
instance isMonHom_isoSpec_inv :
    IsMonHom (G.isoSpec.asOver (Spec (.of K))).inv := inferInstance

/-- Affinization bundled as an isomorphism of group objects. Its underlying
scheme isomorphism is the canonical `G.isoSpec`. -/
def affineGroupIsoSpec :
    Grp.mk (G.asOver (Spec (.of K))) ≅
      (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K Γ(G, ⊤))) := by
  refine Grp.mkIso (G.isoSpec.asOver (Spec (.of K))) ?_ ?_
  · rw [affineCoordinate_hopfSpec_toMonObj (K := K) G]
    exact IsMonHom.one_hom (G.isoSpec.asOver (Spec (.of K))).hom
  · rw [affineCoordinate_hopfSpec_toMonObj (K := K) G]
    exact IsMonHom.mul_hom (G.isoSpec.asOver (Spec (.of K))).hom

@[simp] theorem affineGroupIsoSpec_hom_left :
    (affineGroupIsoSpec (K := K) G).hom.hom.hom.left = G.isoSpec.hom := rfl

@[simp] theorem affineGroupIsoSpec_inv_left :
    (affineGroupIsoSpec (K := K) G).inv.hom.hom.left = G.isoSpec.inv := by
  have h := congrArg
    (fun f : Grp.mk (G.asOver (Spec (.of K))) ⟶ Grp.mk (G.asOver (Spec (.of K))) ↦
      f.hom.hom.left) (affineGroupIsoSpec (K := K) G).hom_inv_id
  change (affineGroupIsoSpec (K := K) G).hom.hom.hom.left ≫
      (affineGroupIsoSpec (K := K) G).inv.hom.hom.left = 𝟙 G at h
  rw [affineGroupIsoSpec_hom_left] at h
  exact (cancel_epi G.isoSpec.hom).1 (h.trans G.isoSpec.hom_inv_id.symm)

/-- The geometric point functor in the scheme universe, with coefficient maps
acting by precomposition. The opposite functor here is `rightOp`. -/
abbrev affineGeometricPointFunctor : CommAlgCat.{u, u} K ⥤ GrpCat.{u} :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrpObj (G.asOver (Spec (.of K)))

/-- The coordinate extension to any independent coefficient universe. The
coordinate Hopf algebra is the canonical one on global sections. -/
abbrev affinePointGroupFunctor : CommAlgCat.{r, u} K ⥤ GrpCat.{max u r} :=
  pointGroupFunctor K Γ(G, ⊤)

section PointComparison

variable {A : Type u} [CommRing A] [hA : HopfAlgebra K A]

/-- Forgetting a morphism to Hopf spectrum gives a monoid morphism to the
spectrum monoid for the same specified Hopf algebra. -/
theorem hopfSpectrum_isMonHom (Y : Grp (Over (Spec (.of K))))
    (j : Y ≅ (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K A))) :
    @IsMonHom (Over (Spec (.of K))) _ _ Y.X
      ((Spec (.of A)).asOver (Spec (.of K))) Y.grp.toMonObj
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      ((Grp.forget (Over (Spec (.of K)))).map j.hom) := by
  exact Eq.mp
    (congrArg (fun m : MonObj ((Spec (.of A)).asOver (Spec (.of K))) ↦
      @IsMonHom (Over (Spec (.of K))) _ _ Y.X
        ((Spec (.of A)).asOver (Spec (.of K))) Y.grp.toMonObj m
        ((Grp.forget (Over (Spec (.of K)))).map j.hom))
      (hopfSpec_obj_toMonObj (.of K) (.of A) (h := hA)))
    j.hom.hom.isMonHom_hom

variable (Y : Over (Spec (.of K))) [mY : MonObj Y]

private def stockPointMulEquiv
    (i : Y ≅ (Spec (.of A)).asOver (Spec (.of K)))
    (hi : @IsMonHom (Over (Spec (.of K))) _ _ Y
      ((Spec (.of A)).asOver (Spec (.of K))) mY
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      i.hom)
    (R : Type u) [CommRing R] [Algebra K R] :
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ Y) ≃*
      (pointGroupFunctor K A).obj (CommAlgCat.of K R) := by
  letI : IsMonHom i.hom := hi
  let e0 := (Hom.mulEquivCongrRight i ((Spec (.of R)).asOver (Spec (.of K)))).trans
    (Spec.mapMulEquiv (R := K) (S := A) (T := R)).symm
  refine { toEquiv := e0.toEquiv, map_mul' := ?_ }
  intro g h
  apply WithConv.ofConv_injective
  exact (congrArg (fun p : WithConv (A →ₐ[K] R) ↦ p.ofConv) (e0.map_mul g h)).trans
    (pointGroupFunctor_mul_ofConv K A (CommAlgCat.of K R) (e0 g) (e0 h)).symm

private theorem stockPointMulEquiv_apply_toRingHom
    (i : Y ≅ (Spec (.of A)).asOver (Spec (.of K)))
    (hi : @IsMonHom (Over (Spec (.of K))) _ _ Y
      ((Spec (.of A)).asOver (Spec (.of K))) mY
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      i.hom)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ Y) :
    CommRingCat.ofHom (stockPointMulEquiv Y i hi R g).ofConv.toRingHom =
      Spec.preimage (g.left ≫ i.hom.left) := rfl

private theorem stockPointMulEquiv_spec_map
    (i : Y ≅ (Spec (.of A)).asOver (Spec (.of K)))
    (hi : @IsMonHom (Over (Spec (.of K))) _ _ Y
      ((Spec (.of A)).asOver (Spec (.of K))) mY
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      i.hom)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ Y) :
    Spec.map (CommRingCat.ofHom (stockPointMulEquiv Y i hi R g).ofConv.toRingHom) =
      g.left ≫ i.hom.left := by
  rw [stockPointMulEquiv_apply_toRingHom, Spec.map_preimage]
  rfl

private theorem stockPointMulEquiv_symm_left
    (i : Y ≅ (Spec (.of A)).asOver (Spec (.of K)))
    (hi : @IsMonHom (Over (Spec (.of K))) _ _ Y
      ((Spec (.of A)).asOver (Spec (.of K))) mY
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      i.hom)
    (R : Type u) [CommRing R] [Algebra K R]
    (p : (pointGroupFunctor K A).obj (CommAlgCat.of K R)) :
    ((stockPointMulEquiv Y i hi R).symm p).left =
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫ i.inv.left := rfl

private theorem stockPointMulEquiv_naturality
    (i : Y ≅ (Spec (.of A)).asOver (Spec (.of K)))
    (hi : @IsMonHom (Over (Spec (.of K))) _ _ Y
      ((Spec (.of A)).asOver (Spec (.of K))) mY
      (@instMonObjSpecAsOverSpec.{u} (.of K) (.of A) hA.toHopfAlgebraStruct.toBialgebra)
      i.hom)
    {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ Y) :
    (stockPointMulEquiv Y i hi S
      ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)) ≫ g)).ofConv =
        f.comp (stockPointMulEquiv Y i hi R g).ofConv := by
  let eR := Spec.mapMulEquiv (R := K) (S := A) (T := R)
  let eS := Spec.mapMulEquiv (R := K) (S := A) (T := S)
  let a : (Spec (.of S)).asOver (Spec (.of K)) ⟶
      (Spec (.of R)).asOver (Spec (.of K)) :=
    (Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K))
  have hR : eR (stockPointMulEquiv Y i hi R g) = g ≫ i.hom :=
    eR.apply_symm_apply _
  have hS : eS (stockPointMulEquiv Y i hi S (a ≫ g)) = (a ≫ g) ≫ i.hom :=
    eS.apply_symm_apply _
  have h : stockPointMulEquiv Y i hi S (a ≫ g) =
      AlgHom.convolutionPostcomp f (stockPointMulEquiv Y i hi R g) := by
    apply eS.injective
    exact hS.trans ((Category.assoc a g i.hom).trans
      ((congrArg (fun k ↦ a ≫ k) hR.symm).trans
        (Spec.mapMulEquiv_convolutionPostcomp f (stockPointMulEquiv Y i hi R g)).symm))
  exact congrArg (fun p : WithConv (A →ₐ[K] S) ↦ p.ofConv) h

end PointComparison

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Geometric points of an affine group are multiplicatively equivalent to
algebra maps out of its canonical coordinate Hopf algebra. -/
def affinePointMulEquiv :
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) ≃*
      (affinePointGroupFunctor G).obj (CommAlgCat.of K R) := by
  -- Elaborate the stock construction before specializing the coordinate Hopf algebra.
  let build (A : Type u) [CommRing A] [HopfAlgebra K A]
      (Y : Grp (Over (Spec (.of K))))
      (j : Y ≅ (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K A)))
      (T : Type u) [CommRing T] [Algebra K T] :
      ((Spec (.of T)).asOver (Spec (.of K)) ⟶ Y.X) ≃*
        (pointGroupFunctor K A).obj (CommAlgCat.of K T) := by
    let i : Y.X ≅ (Spec (.of A)).asOver (Spec (.of K)) :=
      (Grp.forget (Over (Spec (.of K)))).mapIso j
    letI : IsMonHom i.hom := hopfSpectrum_isMonHom Y j
    let e0 := (Hom.mulEquivCongrRight i ((Spec (.of T)).asOver (Spec (.of K)))).trans
      (Spec.mapMulEquiv (R := K) (S := A) (T := T)).symm
    refine { toEquiv := e0.toEquiv, map_mul' := ?_ }
    intro g h
    apply WithConv.ofConv_injective
    exact (congrArg (fun p : WithConv (A →ₐ[K] T) ↦ p.ofConv) (e0.map_mul g h)).trans
      (pointGroupFunctor_mul_ofConv K A (CommAlgCat.of K T) (e0 g) (e0 h)).symm
  exact build Γ(G, ⊤) (Grp.mk (G.asOver (Spec (.of K))))
    (affineGroupIsoSpec (K := K) G) R

private theorem affinePointMulEquiv_preimage
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    CommRingCat.ofHom (affinePointMulEquiv G R g).ofConv.toRingHom =
      Spec.preimage (g.left ≫ G.isoSpec.hom) := by
  let j := affineGroupIsoSpec (K := K) G
  let i : G.asOver (Spec (.of K)) ≅ (Spec Γ(G, ⊤)).asOver (Spec (.of K)) :=
    (Grp.forget (Over (Spec (.of K)))).mapIso j
  have h := stockPointMulEquiv_apply_toRingHom (K := K) (A := Γ(G, ⊤))
    (hA := affineCoordinateHopfAlgebra (K := K) G) (G.asOver (Spec (.of K)))
    i (hopfSpectrum_isMonHom _ j) R g
  exact h.trans (congrArg Spec.preimage
    (congrArg (fun f : G ⟶ Spec Γ(G, ⊤) ↦ g.left ≫ f)
      (affineGroupIsoSpec_hom_left (K := K) G)))

/-- The stock spectrum comparison sends an algebra map to its spectrum map. -/
@[simp] theorem Spec.mapMulEquiv_apply_left {B A T : Type u}
    [CommRing B] [CommRing A] [CommRing T] [Bialgebra B A] [Algebra B T]
    (f : WithConv (A →ₐ[B] T)) :
    (Spec.mapMulEquiv (R := B) (S := A) (T := T) f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) := rfl

/-- Coordinates are the stock spectrum comparison after the original affinization. -/
theorem affinePointMulEquiv_apply
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    affinePointMulEquiv G R g =
      (Spec.mapMulEquiv (R := K) (S := Γ(G, ⊤)) (T := R)).symm
        (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom) := by
  have h : CommRingCat.ofHom (affinePointMulEquiv G R g).ofConv.toRingHom =
      CommRingCat.ofHom
        ((Spec.mapMulEquiv (R := K) (S := Γ(G, ⊤)) (T := R)).symm
          (g ≫ (G.isoSpec.asOver (Spec (.of K))).hom)).ofConv.toRingHom :=
    affinePointMulEquiv_preimage G R g
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  exact congrArg (fun f : CommRingCat.of Γ(G, ⊤) ⟶ CommRingCat.of R ↦ f a) h

/-- Applying the spectrum functor to coordinates gives the original point
followed by canonical affinization. -/
theorem affinePointMulEquiv_spec_map
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    Spec.map (CommRingCat.ofHom (affinePointMulEquiv G R g).ofConv.toRingHom) =
      g.left ≫ G.isoSpec.hom := by
  let j := affineGroupIsoSpec (K := K) G
  let i : G.asOver (Spec (.of K)) ≅ (Spec Γ(G, ⊤)).asOver (Spec (.of K)) :=
    (Grp.forget (Over (Spec (.of K)))).mapIso j
  exact (stockPointMulEquiv_spec_map (K := K) (A := Γ(G, ⊤))
    (hA := affineCoordinateHopfAlgebra (K := K) G) (G.asOver (Spec (.of K)))
    i (hopfSpectrum_isMonHom _ j) R g).trans
      (congrArg (fun f : G ⟶ Spec Γ(G, ⊤) ↦ g.left ≫ f)
        (affineGroupIsoSpec_hom_left (K := K) G))

/-- The spectrum of the coordinate ring homomorphism is the point followed by affinization. -/
@[simp] theorem affinePointMulEquiv_spec_map_coe
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    Spec.map (CommRingCat.ofHom
      ((affinePointMulEquiv G R g).ofConv : Γ(G, ⊤) →+* R)) =
        g.left ≫ G.isoSpec.hom :=
  affinePointMulEquiv_spec_map G R g

/-- The coordinate ring map is pullback along the original point followed by
normalization of the coefficient spectrum. -/
theorem affinePointMulEquiv_toRingHom
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    CommRingCat.ofHom (affinePointMulEquiv G R g).ofConv.toRingHom =
      g.left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
  let γ : Spec (.of R) ⟶ G := g.left
  let q : Γ(G, ⊤) ⟶ Γ(Spec (.of R), ⊤) := γ.appTop
  let ε : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of R := (Scheme.ΓSpecIso (.of R)).hom
  have hγ : γ ≫ G.isoSpec.hom = Spec.map (q ≫ ε) := by
    calc
      γ ≫ G.isoSpec.hom = γ ≫ G.toSpecΓ :=
        congrArg (fun k : G ⟶ Spec Γ(G, ⊤) ↦ γ ≫ k) (Scheme.isoSpec_hom G)
      _ = (Spec (.of R)).toSpecΓ ≫ Spec.map q := Scheme.toSpecΓ_naturality γ
      _ = Spec.map ε ≫ Spec.map q :=
        congrArg (fun k : Spec (.of R) ⟶ Spec Γ(Spec (.of R), ⊤) ↦ k ≫ Spec.map q)
          (SpecMap_ΓSpecIso_hom (.of R)).symm
      _ = Spec.map (q ≫ ε) := (Spec.map_comp q ε).symm
  apply Spec.map_injective
  exact (affinePointMulEquiv_spec_map G R g).trans hγ

/-- The inverse coordinate comparison applies `Spec` and then inverse
canonical affinization. -/
@[simp] theorem affinePointMulEquiv_symm_left
    (f : (affinePointGroupFunctor G).obj (CommAlgCat.of K R)) :
    ((affinePointMulEquiv G R).symm f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫ G.isoSpec.inv := by
  let j := affineGroupIsoSpec (K := K) G
  let i : G.asOver (Spec (.of K)) ≅ (Spec Γ(G, ⊤)).asOver (Spec (.of K)) :=
    (Grp.forget (Over (Spec (.of K)))).mapIso j
  exact (stockPointMulEquiv_symm_left (K := K) (A := Γ(G, ⊤))
    (hA := affineCoordinateHopfAlgebra (K := K) G) (G.asOver (Spec (.of K)))
    i (hopfSpectrum_isMonHom _ j) R f).trans
      (congrArg (fun k : Spec Γ(G, ⊤) ⟶ G ↦
        Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫ k)
        (affineGroupIsoSpec_inv_left (K := K) G))

/-- Coordinate equality detects equality of geometric points. -/
theorem affinePoint_ext
    {g h : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))}
    (e : (affinePointMulEquiv G R g).ofConv = (affinePointMulEquiv G R h).ofConv) :
    g = h :=
  (affinePointMulEquiv G R).injective (WithConv.ofConv_injective e)

/-- The unit has counit coordinates. -/
@[simp] theorem affinePointMulEquiv_one :
    (affinePointMulEquiv G R 1).ofConv =
      (Algebra.ofId K R).comp (Bialgebra.counitAlgHom K Γ(G, ⊤)) := by
  rw [map_one]
  rfl

/-- Multiplication has convolution coordinates in the original order. -/
theorem affinePointMulEquiv_mul
    (g h : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (a : Γ(G, ⊤)) :
    (affinePointMulEquiv G R (g * h)).ofConv a =
      Algebra.TensorProduct.lift (affinePointMulEquiv G R g).ofConv
        (affinePointMulEquiv G R h).ofConv (fun _ _ ↦ .all ..) (Coalgebra.comul a) := by
  rw [map_mul]
  exact pointGroupFunctor_mul_apply K Γ(G, ⊤) (CommAlgCat.of K R)
    (affinePointMulEquiv G R g) (affinePointMulEquiv G R h) a

/-- Inversion has antipode-precomposition coordinates. -/
@[simp] theorem affinePointMulEquiv_inv
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (affinePointMulEquiv G R g⁻¹).ofConv =
      (affinePointMulEquiv G R g).ofConv.comp (HopfAlgebra.antipodeAlgHom K Γ(G, ⊤)) := by
  rw [map_inv]
  exact AlgHom.convolutionInverse_ofConv _

variable {R} {S : Type u} [CommRing S] [Algebra K S]

/-- Every algebra map acts on coordinates by postcomposition. -/
theorem affinePointMulEquiv_naturality (f : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    affinePointMulEquiv G S
        ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)) ≫ g) =
      AlgHom.convolutionPostcomp f (affinePointMulEquiv G R g) := by
  apply WithConv.ofConv_injective
  let j := affineGroupIsoSpec (K := K) G
  let i : G.asOver (Spec (.of K)) ≅ (Spec Γ(G, ⊤)).asOver (Spec (.of K)) :=
    (Grp.forget (Over (Spec (.of K)))).mapIso j
  exact stockPointMulEquiv_naturality (K := K) (A := Γ(G, ⊤))
    (hA := affineCoordinateHopfAlgebra (K := K) G) (G.asOver (Spec (.of K)))
    i (hopfSpectrum_isMonHom _ j) f g

/-- The group-valued natural isomorphism between geometric points and
the canonical coordinate extension in the scheme universe. -/
def affinePointsIso :
    affineGeometricPointFunctor (K := K) G ≅ affinePointGroupFunctor (K := K) G :=
  NatIso.ofComponents (fun R ↦ (affinePointMulEquiv (K := K) G R).toGrpIso)
    (fun {R S} f ↦ by
      apply GrpCat.ext
      intro g
      apply WithConv.ofConv_injective
      have h := affinePointMulEquiv_naturality (K := K) G f.hom g
      exact (congrArg (fun p : WithConv (Γ(G, ⊤) →ₐ[K] S) ↦ p.ofConv) h).trans
        (pointGroupFunctor_map_ofConv K Γ(G, ⊤) f (affinePointMulEquiv G R g)).symm)

end Coordinates

section SpectrumNormalization

section HopfSpectrumComparison

variable {K A : Type u} [CommRing K] [CommRing A] [hA : HopfAlgebra K A]

-- Compare the complete bundled parents before forming any indexed morphism law.
private def hopfSpectrumIso :
    (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K A)) ≅
      Grp.mk ((Spec (.of A)).asOver (Spec (.of K))) :=
  eqToIso (hopfSpec_obj_eq (.of K) (.of A) (h := hA))

private theorem hopfSpectrumIso_hom_left :
    (hopfSpectrumIso (K := K) (A := A)).hom.hom.hom.left = 𝟙 (Spec (.of A)) := rfl

private theorem hopfSpectrumIso_inv_left :
    (hopfSpectrumIso (K := K) (A := A)).inv.hom.hom.left = 𝟙 (Spec (.of A)) := rfl

variable (A0 A1 : CommHopfAlgCat.{u} K)
  (j : (hopfSpec (.of K)).obj (op A0) ≅ (hopfSpec (.of K)).obj (op A1))

-- Full faithfulness gives both original maps at abstract bundled Hopf algebras.
private theorem hopfSpec_preimageIso_hom_left :
    let e : A1 ≃ₐc[K] A0 := CommHopfAlgCat.ofIso
      (((hopfSpec.fullyFaithful (R := .of K)).preimageIso j).unop)
    Spec.map (CommRingCat.ofHom (e.toAlgEquiv.toAlgHom.toRingHom)) =
      j.hom.hom.hom.left := by
  exact congrArg
    (fun f : (hopfSpec (.of K)).obj (op A0) ⟶ (hopfSpec (.of K)).obj (op A1) ↦
      f.hom.hom.left)
    ((hopfSpec.fullyFaithful (R := .of K)).map_preimage j.hom)

private theorem hopfSpec_preimageIso_inv_left :
    let e : A0 ≃ₐc[K] A1 := (CommHopfAlgCat.ofIso
      (((hopfSpec.fullyFaithful (R := .of K)).preimageIso j).unop)).symm
    Spec.map (CommRingCat.ofHom (e.toAlgEquiv.toAlgHom.toRingHom)) =
      j.inv.hom.hom.left := by
  exact congrArg
    (fun f : (hopfSpec (.of K)).obj (op A1) ⟶ (hopfSpec (.of K)).obj (op A0) ↦
      f.hom.hom.left)
    ((hopfSpec.fullyFaithful (R := .of K)).map_preimage j.inv)

end HopfSpectrumComparison

variable {K C : Type u} [CommRing K] [CommRing C] [hC : HopfAlgebra K C]

local instance : (Spec (.of C)).isoSpec.hom.IsOver (Spec (.of K)) :=
  affineCoordinate_group_isoSpec_hom_isOver (K := K) (Spec (.of C))

/-- The canonical coordinate Hopf algebra of `Spec C` is isomorphic to the
specified `C`. Fully faithful Hopf-Spec lifts the original affinization,
with its original forward and inverse maps. -/
def coordinateSpecHopfIso :
    CommHopfAlgCat.of K Γ(Spec (.of C), ⊤) ≅ CommHopfAlgCat.of K C := by
  let source : (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K C)) ≅
      Grp.mk ((Spec (.of C)).asOver (Spec (.of K))) :=
    eqToIso (hopfSpec_obj_eq (.of K) (.of C) (h := hC))
  let j : (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K C)) ≅
      (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K Γ(Spec (.of C), ⊤))) :=
    source ≪≫ affineGroupIsoSpec (K := K) (Spec (.of C))
  exact ((hopfSpec.fullyFaithful (R := .of K)).preimageIso j).unop

private theorem coordinateSpecHopfIso_spec_hom :
    let e : Γ(Spec (.of C), ⊤) ≃ₐc[K] C :=
      CommHopfAlgCat.ofIso (coordinateSpecHopfIso (K := K) (C := C))
    Spec.map (CommRingCat.ofHom (e.toAlgEquiv.toAlgHom.toRingHom)) =
      (Spec (.of C)).isoSpec.hom := by
  let j : (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K C)) ≅
      (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K Γ(Spec (.of C), ⊤))) :=
    hopfSpectrumIso (K := K) (A := C) ≪≫ affineGroupIsoSpec (K := K) (Spec (.of C))
  have hj : j.hom.hom.hom.left = (Spec (.of C)).isoSpec.hom := by
    change (hopfSpectrumIso (K := K) (A := C)).hom.hom.hom.left ≫
      (affineGroupIsoSpec (K := K) (Spec (.of C))).hom.hom.hom.left = _
    rw [hopfSpectrumIso_hom_left]
    exact (Category.id_comp
      (affineGroupIsoSpec (K := K) (Spec (.of C))).hom.hom.hom.left).trans
      (affineGroupIsoSpec_hom_left (K := K) (Spec (.of C)))
  exact (hopfSpec_preimageIso_hom_left (CommHopfAlgCat.of K C)
    (CommHopfAlgCat.of K Γ(Spec (.of C), ⊤)) j).trans hj

private theorem coordinateSpecHopfIso_spec_inv :
    let e : C ≃ₐc[K] Γ(Spec (.of C), ⊤) :=
      (CommHopfAlgCat.ofIso (coordinateSpecHopfIso (K := K) (C := C))).symm
    Spec.map (CommRingCat.ofHom (e.toAlgEquiv.toAlgHom.toRingHom)) =
      (Spec (.of C)).isoSpec.inv := by
  let j : (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K C)) ≅
      (hopfSpec (.of K)).obj (op (CommHopfAlgCat.of K Γ(Spec (.of C), ⊤))) :=
    hopfSpectrumIso (K := K) (A := C) ≪≫ affineGroupIsoSpec (K := K) (Spec (.of C))
  have hj : j.inv.hom.hom.left = (Spec (.of C)).isoSpec.inv := by
    change (affineGroupIsoSpec (K := K) (Spec (.of C))).inv.hom.hom.left ≫
      (hopfSpectrumIso (K := K) (A := C)).inv.hom.hom.left = _
    rw [hopfSpectrumIso_inv_left]
    exact (Category.comp_id
      (affineGroupIsoSpec (K := K) (Spec (.of C))).inv.hom.hom.left).trans
      (affineGroupIsoSpec_inv_left (K := K) (Spec (.of C)))
  exact (hopfSpec_preimageIso_inv_left (CommHopfAlgCat.of K C)
    (CommHopfAlgCat.of K Γ(Spec (.of C), ⊤)) j).trans hj

/-- The spectrum global-sections isomorphism as a bialgebra equivalence,
between the reconstructed coordinate Hopf algebra and the original one. -/
def coordinateSpecEquiv : Γ(Spec (.of C), ⊤) ≃ₐc[K] C :=
  CommHopfAlgCat.ofIso (coordinateSpecHopfIso (K := K) (C := C))

/-- The bialgebra normalization has exactly the canonical ring-map data. -/
theorem coordinateSpecEquiv_toRingHom :
    CommRingCat.ofHom (coordinateSpecEquiv (K := K) (C := C)).toAlgEquiv.toAlgHom.toRingHom =
      (Scheme.ΓSpecIso (.of C)).hom := by
  apply Spec.map_injective
  exact (coordinateSpecHopfIso_spec_hom (K := K) (C := C)).trans
    (Scheme.isoSpec_Spec_hom (.of C))

/-- Evaluation of the canonical normalization. -/
@[simp] theorem coordinateSpecEquiv_apply (x : Γ(Spec (.of C), ⊤)) :
    coordinateSpecEquiv (K := K) (C := C) x = (Scheme.ΓSpecIso (.of C)).hom x :=
  congrArg (fun f : CommRingCat.of Γ(Spec (.of C), ⊤) ⟶ CommRingCat.of C ↦ f x)
    (coordinateSpecEquiv_toRingHom (K := K) (C := C))

/-- The inverse normalization is the canonical inverse global-sections map. -/
@[simp] theorem coordinateSpecEquiv_symm_apply (x : C) :
    (coordinateSpecEquiv (K := K) (C := C)).symm x = (Scheme.ΓSpecIso (.of C)).inv x := by
  have h : CommRingCat.ofHom
      (coordinateSpecEquiv (K := K) (C := C)).symm.toAlgEquiv.toAlgHom.toRingHom =
        (Scheme.ΓSpecIso (.of C)).inv := by
    apply Spec.map_injective
    exact (coordinateSpecHopfIso_spec_inv (K := K) (C := C)).trans
      (Scheme.isoSpec_Spec_inv (.of C))
  exact congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of Γ(Spec (.of C), ⊤) ↦ f x) h

/-- The algebra-equivalence presentation has the same canonical inverse values. -/
@[simp] theorem coordinateSpecEquiv_toAlgEquiv_symm_apply (x : C) :
    (coordinateSpecEquiv (K := K) (C := C) : Γ(Spec (.of C), ⊤) ≃ₐ[K] C).symm x =
      (Scheme.ΓSpecIso (.of C)).inv x := by
  let E := coordinateSpecEquiv (K := K) (C := C)
  let F : Γ(Spec (.of C), ⊤) ≃ₐ[K] C := E
  have hF (z : Γ(Spec (.of C), ⊤)) : F z = (Scheme.ΓSpecIso (.of C)).hom z :=
    (congrFun (BialgEquiv.coe_toAlgEquiv E) z).trans (coordinateSpecEquiv_apply z)
  apply F.injective
  calc
    _ = x := F.apply_symm_apply x
    _ = (Scheme.ΓSpecIso (.of C)).hom ((Scheme.ΓSpecIso (.of C)).inv x) :=
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of C)) x).symm
    _ = _ := (hF ((Scheme.ΓSpecIso (.of C)).inv x)).symm

/-- The coalgebra-equivalence presentation has the canonical inverse global-sections values. -/
@[simp] theorem coordinateSpecEquiv_toCoalgEquiv_symm_apply (x : C) :
    (coordinateSpecEquiv (K := K) (C := C) : Γ(Spec (.of C), ⊤) ≃ₗc[K] C).symm x =
      (Scheme.ΓSpecIso (.of C)).inv x :=
  coordinateSpecEquiv_symm_apply x

/-- The inverse linear projection of the bialgebra normalization is the
canonical inverse map on global sections. -/
theorem coordinateSpecEquiv_symm_toLinearMap_apply (x : C) :
    (coordinateSpecEquiv (K := K) (C := C)).symm.toLinearMap x =
      (Scheme.ΓSpecIso (.of C)).inv x := by
  calc
    _ = (coordinateSpecEquiv (K := K) (C := C)).symm x := rfl
    _ = _ := coordinateSpecEquiv_symm_apply x

/-- The inverse linear projection sends the unit to the original unit. -/
theorem coordinateSpecEquiv_symm_toLinearMap_one :
    (coordinateSpecEquiv (K := K) (C := C)).symm.toLinearMap 1 = 1 := by
  change (coordinateSpecEquiv (K := K) (C := C)).symm 1 = 1
  exact map_one _

/-- The normalization preserves the unit of the specified algebra. -/
theorem coordinateSpecEquiv_one :
    coordinateSpecEquiv (K := K) (C := C) 1 = 1 := map_one _

/-- Counits are normalized without changing the original Hopf algebra. -/
theorem coordinateSpecEquiv_counit (x : Γ(Spec (.of C), ⊤)) :
    Coalgebra.counit (R := K) (coordinateSpecEquiv (K := K) (C := C) x) =
      Coalgebra.counit (R := K) x :=
  LinearMap.congr_fun (coordinateSpecEquiv (K := K) (C := C)).counit_comp x

/-- Comultiplication is normalized by the tensor square of the same map. -/
theorem coordinateSpecEquiv_comul (x : Γ(Spec (.of C), ⊤)) :
    TensorProduct.map (coordinateSpecEquiv (K := K) (C := C)).toLinearMap
        (coordinateSpecEquiv (K := K) (C := C)).toLinearMap (Coalgebra.comul x) =
      Coalgebra.comul (coordinateSpecEquiv (K := K) (C := C) x) :=
  LinearMap.congr_fun (coordinateSpecEquiv (K := K) (C := C)).map_comp_comul x

/-- Antipodes are normalized by uniqueness of convolution inverses. -/
theorem coordinateSpecEquiv_antipode (x : Γ(Spec (.of C), ⊤)) :
    coordinateSpecEquiv (K := K) (C := C) (HopfAlgebra.antipode K x) =
      HopfAlgebra.antipode K (coordinateSpecEquiv (K := K) (C := C) x) :=
  BialgHom.map_antipode (coordinateSpecEquiv (K := K) (C := C)).toBialgHom x

/-- The spectrum global-sections map intertwines the coordinate and original antipodes. -/
@[simp] theorem coordinateSpec_antipode (x : Γ(Spec (.of C), ⊤)) :
    (Scheme.ΓSpecIso (.of C)).hom (HopfAlgebra.antipode K x) =
      HopfAlgebra.antipode K ((Scheme.ΓSpecIso (.of C)).hom x) := by
  simpa only [coordinateSpecEquiv_apply] using
    coordinateSpecEquiv_antipode (K := K) (C := C) x

/-- A point of an originally specified spectrum acquires coordinates by
precomposing with the canonical bialgebra normalization. -/
theorem affinePointMulEquiv_spec (R : Type u) [CommRing R] [Algebra K R]
    (f : C →ₐ[K] R) :
    (affinePointMulEquiv (K := K) (Spec (.of C)) R
      ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)))).ofConv =
        f.comp (coordinateSpecEquiv (K := K) (C := C)).toAlgEquiv.toAlgHom := by
  have h : CommRingCat.ofHom
      (affinePointMulEquiv (K := K) (Spec (.of C)) R
        ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)))).ofConv.toRingHom =
      CommRingCat.ofHom
        (f.comp (coordinateSpecEquiv (K := K) (C := C)).toAlgEquiv.toAlgHom).toRingHom := by
    rw [affinePointMulEquiv_toRingHom]
    change (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
        (Scheme.ΓSpecIso (.of R)).hom =
      CommRingCat.ofHom (coordinateSpecEquiv (K := K) (C := C)).toAlgEquiv.toAlgHom.toRingHom ≫
        CommRingCat.ofHom f.toRingHom
    rw [coordinateSpecEquiv_toRingHom]
    exact Scheme.ΓSpecIso_naturality _
  apply AlgHom.ext
  intro c
  exact congrArg
    (fun q : CommRingCat.of Γ(Spec (.of C), ⊤) ⟶ CommRingCat.of R ↦ q c) h

end SpectrumNormalization

section Representations

attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Hom.group

variable {K : Type u} [CommRing K] (G : Scheme.{u})
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))] [IsAffine G]
  (V : Type v) [AddCommGroup V] [Module K V]

/-- A representation of an affine group on an arbitrary module, using the
coordinate extension to the indicated category of coefficient algebras.
This is a natural transformation to the standard tensor general linear functor. -/
abbrev AffineRepresentation := PointRepresentation.{u, u, v, t} K Γ(G, ⊤) V

/-- A representation of the geometric point functor in the scheme universe.
No finite-dimensional vector scheme is used for the target. -/
abbrev GeometricRepresentation :=
  NatTrans (affineGeometricPointFunctor G ⋙ GrpCat.uliftFunctor.{v, u})
    (generalLinearModuleFunctor K V : CommAlgCat.{u, u} K ⥤ GrpCat.{max u v})

-- Compute functor precomposition before specializing either point functor.
private theorem whisker_ulift_comp_app
    {D : Type s} [Category.{r} D]
    {F H : D ⥤ GrpCat.{u}} {P : D ⥤ GrpCat.{max u v}}
    (α : F ⟶ H) (η : H ⋙ GrpCat.uliftFunctor.{v, u} ⟶ P)
    (R : D) (x : F.obj R) :
    (((CategoryTheory.Functor.whiskerRight α GrpCat.uliftFunctor.{v, u}) ≫ η).app R).hom
        (ULift.up x) =
      (η.app R).hom (ULift.up ((α.app R).hom x)) := rfl

namespace GeometricRepresentation

variable {G V}

/-- Coordinate change of a geometric natural representation. Its inverse is
precomposition with the proved group-valued natural point comparison. -/
def coordinateEquiv : GeometricRepresentation (K := K) G V ≃
    AffineRepresentation.{u, v, 0} (K := K) G V where
  toFun η := (Functor.isoWhiskerRight (affinePointsIso G) GrpCat.uliftFunctor.{v, u}).inv ≫ η
  invFun η := (Functor.isoWhiskerRight (affinePointsIso G) GrpCat.uliftFunctor.{v, u}).hom ≫ η
  left_inv η := by
    let e := Functor.isoWhiskerRight (affinePointsIso (K := K) G) GrpCat.uliftFunctor.{v, u}
    exact e.hom_inv_id_assoc η
  right_inv η := by
    let e := Functor.isoWhiskerRight (affinePointsIso (K := K) G) GrpCat.uliftFunctor.{v, u}
    exact e.inv_hom_id_assoc η

/-- Coordinates use the component at the inverse geometric point comparison. -/
theorem coordinateEquiv_operator (η : GeometricRepresentation (K := K) G V)
    (R : CommAlgCat.{u, u} K) (f : Γ(G, ⊤) →ₐ[K] R) :
    (coordinateEquiv η).operator R f =
      (η.app R).hom (ULift.up ((affinePointMulEquiv G R).symm (toConv f))) := by
  exact whisker_ulift_comp_app (affinePointsIso (K := K) G).inv η R (toConv f)

/-- The geometric representation–comodule correspondence on the same
module, for the canonical Hopf algebra on `Γ(G, ⊤)`. -/
def rightComoduleEquiv : GeometricRepresentation (K := K) G V ≃
    Coalgebra.RightComodule K Γ(G, ⊤) V :=
  coordinateEquiv.trans (PointRepresentation.rightComoduleEquiv K Γ(G, ⊤) V)

/-- The inverse correspondence evaluates the original specified coaction
against the coordinates of the original geometric point. -/
theorem rightComoduleEquiv_symm_app
    (X : Coalgebra.RightComodule K Γ(G, ⊤) V) (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    ((rightComoduleEquiv (G := G) (V := V)).symm X).app R (ULift.up g) =
      X.pointAction (affinePointMulEquiv G R g) := by
  let ξ := PointRepresentation.ofRightComodule.{u, u, v, 0} X
  have h := whisker_ulift_comp_app (affinePointsIso (K := K) G).hom ξ R g
  exact h.trans (PointRepresentation.ofRightComodule_operator X R
    (affinePointMulEquiv (K := K) G R g).ofConv)

end GeometricRepresentation

namespace AffineRepresentation

variable {G V}

/-- The coordinate representation–comodule correspondence with coordinate
algebra `Γ(G, ⊤)`. It retains both inverse values of the generic API. -/
abbrev rightComoduleEquiv : AffineRepresentation.{u, v, t} (K := K) G V ≃
    Coalgebra.RightComodule K Γ(G, ⊤) V :=
  PointRepresentation.rightComoduleEquiv K Γ(G, ⊤) V

/-- The action of a geometric point, evaluated from the same recovered
coaction even when the original presentation uses a larger tester category. -/
def geometricAction (η : AffineRepresentation.{u, v, t} (K := K) G V)
    (R : Type u) [CommRing R] [Algebra K R] :
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) →*
      LinearMap.GeneralLinearGroup R (R ⊗[K] V) :=
  η.pointAction.comp (affinePointMulEquiv G R).toMonoidHom

/-- The geometric action of a point is the canonical action of its coordinates. -/
@[simp] theorem geometricAction_apply
    (η : AffineRepresentation.{u, v, t} (K := K) G V)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    η.geometricAction R g = η.pointAction (affinePointMulEquiv G R g) := rfl

/-- The geometric action has the standard coefficient-evaluation formula. -/
theorem geometricAction_one_tmul (η : AffineRepresentation.{u, v, t} (K := K) G V)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) (x : V) :
    (η.geometricAction R g).val (1 ⊗ₜ[K] x) =
      TensorProduct.map (affinePointMulEquiv G R g).ofConv.toLinearMap
        (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V Γ(G, ⊤) (η.toRightComodule.coaction x)) := by
  rw [geometricAction_apply]
  let φ : Γ(G, ⊤) →ₐ[K] R := (affinePointMulEquiv G R g).ofConv
  exact PointRepresentation.pointAction_one_tmul η φ x

/-- Every coefficient map in the scheme universe commutes with the
geometric action. -/
theorem geometricAction_baseChange (η : AffineRepresentation.{u, v, t} (K := K) G V)
    {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    generalLinearModuleBaseChange K V R S f (η.geometricAction R g) =
      η.geometricAction S
        ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)) ≫ g) := by
  simp only [geometricAction_apply]
  let cR : WithConv (Γ(G, ⊤) →ₐ[K] R) := affinePointMulEquiv G R g
  let cS : WithConv (Γ(G, ⊤) →ₐ[K] S) :=
    affinePointMulEquiv G S
      ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)) ≫ g)
  have hc : cS = AlgHom.convolutionPostcomp f cR :=
    affinePointMulEquiv_naturality (K := K) G f g
  calc
    _ = η.pointAction (AlgHom.convolutionPostcomp f cR) := η.pointAction_baseChange f cR
    _ = _ := congrArg (fun p : WithConv (Γ(G, ⊤) →ₐ[K] S) ↦ η.pointAction p) hc.symm

/-- In the scheme-universe tester slice this is the original component,
not just an isomorphic operator on another module. -/
theorem geometricAction_eq_operator
    (η : AffineRepresentation.{u, v, 0} (K := K) G V)
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    η.geometricAction R g = η.operator R (affinePointMulEquiv G R g).ofConv :=
  (geometricAction_apply η R g).trans
    (η.pointAction_eq_operator R (affinePointMulEquiv G R g).ofConv)

/-- Invariance in the tester slice can be expressed using the canonical point
actions. This slice contains a genuine lifted generic point; preservation at
other coefficient sizes follows from the recovered coaction. -/
theorem isInvariant_iff_all_points
    (η : AffineRepresentation.{u, v, t} (K := K) G V) (U : Submodule K V) :
    η.IsInvariant U ↔
      ∀ (R : CommAlgCat.{max u t, u} K) (f : Γ(G, ⊤) →ₐ[K] R)
        (z : R ⊗[K] V), z ∈ LinearMap.range (U.subtype.baseChange R) →
          (η.pointAction (toConv f)).val z ∈ LinearMap.range (U.subtype.baseChange R) := by
  constructor
  · intro h R f z hz
    have he := congrArg
      (fun a : LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦ a.val z)
      (η.pointAction_eq_operator R f)
    rw [he]
    exact h R f z hz
  · intro h R f z hz
    have he := congrArg
      (fun a : LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦ a.val z)
      (η.pointAction_eq_operator R f)
    rw [← he]
    exact h R f z hz

/-- For a representation in the scheme universe, invariance of the original
scalar-extension images can equivalently be tested on all geometric points. -/
theorem isInvariant_iff_geometric
    (η : AffineRepresentation.{u, v, 0} (K := K) G V) (U : Submodule K V) :
    η.IsInvariant U ↔
      ∀ (R : Type u) [CommRing R] [Algebra K R]
        (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
        (z : R ⊗[K] V), z ∈ LinearMap.range (U.subtype.baseChange R) →
          (η.geometricAction R g).val z ∈ LinearMap.range (U.subtype.baseChange R) := by
  constructor
  · intro h R _ _ g z hz
    simp only [geometricAction_apply]
    have he := LinearMap.congr_fun
      (PointRepresentation.pointAction_val η (affinePointMulEquiv (K := K) G R g)) z
    exact he.symm ▸ PointRepresentation.IsInvariant.evaluate_mem_baseChange η h
      (affinePointMulEquiv (K := K) G R g).ofConv hz
  · intro h
    apply (isInvariant_iff_all_points η U).2
    intro R f z hz
    have hg := h R ((affinePointMulEquiv (K := K) G R).symm (toConv f)) z hz
    simp only [geometricAction_apply] at hg
    exact (congrArg
      (fun p : WithConv (Γ(G, ⊤) →ₐ[K] R) ↦
        (η.pointAction p).val z ∈ LinearMap.range (U.subtype.baseChange R))
      ((affinePointMulEquiv (K := K) G R).apply_symm_apply (toConv f))) ▸ hg

/-- The original-image criterion for geometric points is exactly stability of
the same recovered coaction, with no base-field density argument. -/
theorem isStable_iff_geometric
    (η : AffineRepresentation.{u, v, 0} (K := K) G V) (U : Submodule K V) :
    η.toRightComodule.IsStable U ↔
      ∀ (R : Type u) [CommRing R] [Algebra K R]
        (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
        (z : R ⊗[K] V), z ∈ LinearMap.range (U.subtype.baseChange R) →
          (η.geometricAction R g).val z ∈ LinearMap.range (U.subtype.baseChange R) :=
  (η.isInvariant_iff_isStable U).symm.trans (isInvariant_iff_geometric η U)

/-- Changing tester level leaves all geometric actions unchanged as group
homomorphisms, because it preserves the specified recovered coaction. -/
theorem geometricAction_changeTestLevel
    (η : AffineRepresentation.{u, v, t} (K := K) G V)
    (R : Type u) [CommRing R] [Algebra K R] :
    geometricAction (PointRepresentation.changeTestLevel.{u, u, v, t, s} η) R =
      geometricAction η R := by
  have hA : (PointRepresentation.changeTestLevel.{u, u, v, t, s} η).pointAction
      (R := R) = η.pointAction :=
    PointRepresentation.changeTestLevel_pointAction η
  exact congrArg
    (fun a : WithConv (Γ(G, ⊤) →ₐ[K] R) →*
        LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦
      a.comp (affinePointMulEquiv (K := K) G R).toMonoidHom) hA

/-- Every independently sized algebra uses evaluation of the same recovered
coaction; stock tensor transport supplies its lift comparison. -/
theorem action_lift_down (η : AffineRepresentation.{u, v, t} (K := K) G V)
    {R : Type r} [CommRing R] [Algebra K R] (f : Γ(G, ⊤) →ₐ[K] R)
    (z : ULift.{q} R ⊗[K] V) :
    coefficientTensorEquiv (ULift.algEquiv (R := K) : ULift.{q} R ≃ₐ[K] R)
        ((η.pointAction (toConv ((ULift.algEquiv (R := K)).symm.toAlgHom.comp f))).val z) =
      (η.pointAction (toConv f)).val
        (coefficientTensorEquiv (ULift.algEquiv (R := K) : ULift.{q} R ≃ₐ[K] R) z) :=
  η.evaluate_lift_down f z

/-- The canonical restriction on exactly the original submodule intertwines
geometric actions through exactly its scalar-extended subtype inclusion.
Flatness is needed only for the existing subtype-coaction construction. -/
theorem restricted_geometricAction
    [Module.Flat K Γ(G, ⊤)]
    (η : AffineRepresentation.{u, v, t} (K := K) G V)
    (U : Submodule K V) (hU : η.IsInvariant U)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : R ⊗[K] U) :
    U.subtype.baseChange R
        ((geometricAction (G := G) (η.restrictedPointRepresentation U hU) R g).val z) =
      (η.geometricAction R g).val (U.subtype.baseChange R z) :=
  η.restrictedInclusion_evaluate_apply U hU (affinePointMulEquiv G R g).ofConv z

/-- Geometric intertwining is colinearity for the same recovered coactions.
No injectivity assumption on scalar extension of the map is needed. -/
theorem geometricIntertwining_iff_colinear
    {W : Type w} [AddCommGroup W] [Module K W]
    (η : AffineRepresentation.{u, v, 0} (K := K) G V)
    (θ : AffineRepresentation.{u, w, 0} (K := K) G W) (f : V →ₗ[K] W) :
    (∀ (R : Type u) [CommRing R] [Algebra K R]
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (η.geometricAction R g).val =
        (θ.geometricAction R g).val ∘ₗ f.baseChange R) ↔
      θ.toRightComodule.coaction ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ η.toRightComodule.coaction := by
  rw [← PointRepresentation.isPointIntertwining_iff_colinear η θ f]
  constructor
  · intro h R a
    have hg := h R ((affinePointMulEquiv (K := K) G R).symm (toConv a))
    simp only [geometricAction_apply] at hg
    have hp : f.baseChange R ∘ₗ (η.pointAction (toConv a)).val =
        (θ.pointAction (toConv a)).val ∘ₗ f.baseChange R :=
      (congrArg
        (fun p : WithConv (Γ(G, ⊤) →ₐ[K] R) ↦
          f.baseChange R ∘ₗ (η.pointAction p).val =
            (θ.pointAction p).val ∘ₗ f.baseChange R)
        ((affinePointMulEquiv (K := K) G R).apply_symm_apply (toConv a))) ▸ hg
    exact (congrArg₂
      (fun p : LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦
        fun q : LinearMap.GeneralLinearGroup R (R ⊗[K] W) ↦
          f.baseChange R ∘ₗ p.val = q.val ∘ₗ f.baseChange R)
      (PointRepresentation.pointAction_eq_operator η R a)
      (PointRepresentation.pointAction_eq_operator θ R a)) ▸ hp
  · intro h R _ _ g
    simp only [geometricAction_apply]
    exact (congrArg₂
      (fun p : LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦
        fun q : LinearMap.GeneralLinearGroup R (R ⊗[K] W) ↦
          f.baseChange R ∘ₗ p.val = q.val ∘ₗ f.baseChange R)
      (PointRepresentation.pointAction_eq_operator η (CommAlgCat.of K R)
        (affinePointMulEquiv (K := K) G R g).ofConv)
      (PointRepresentation.pointAction_eq_operator θ (CommAlgCat.of K R)
        (affinePointMulEquiv (K := K) G R g).ofConv)).symm ▸
      h (CommAlgCat.of K R) (affinePointMulEquiv (K := K) G R g).ofConv

end AffineRepresentation

end Representations

section FiniteSystem

variable {K : Type u} [Field K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))] [IsAffine G]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  (η : AffineRepresentation.{u, v, t} (K := K) G V)
  (θ : AffineRepresentation.{u, w, t} (K := K) G W)

namespace AffineRepresentation

/-- All compatible families on the original finite-dimensional subspaces glue
uniquely to an intertwiner into any target representation. The stage system,
restriction, reconstruction and maps are unchanged from the generic API. -/
abbrev finiteFamilyEquiv := PointRepresentation.homEquivFiniteCompatibleFamily η θ

/-- Over a field the scalar extension of every original subspace inclusion is
injective, regardless of the dimensions of the subspace or ambient module. -/
theorem subtype_baseChange_injective (U : Submodule K V)
    (R : Type r) [CommRing R] [Algebra K R] :
    Function.Injective (U.subtype.baseChange R) :=
  Module.Flat.lTensor_preserves_injective_linearMap U.subtype Subtype.val_injective

/-- The glued morphism intertwines the original geometric actions, on every
tensor, not only on base-field vectors. This uses the whole compatible-family
glue, with no finite-dimensionality requirement on either ambient module. -/
theorem glueFinite_geometricAction
    (f : PointRepresentation.FiniteCompatibleFamily η.toRightComodule θ)
    (R : Type u) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : R ⊗[K] V) :
    ((finiteFamilyEquiv η θ).symm f).toLinearMap.baseChange R
        ((η.geometricAction R g).val z) =
      (θ.geometricAction R g).val
        (((finiteFamilyEquiv η θ).symm f).toLinearMap.baseChange R z) :=
  PointRepresentation.glueFinite_evaluate η θ f (affinePointMulEquiv G R g).ofConv z

/-- Extension to a common tester universe and genuine stock-lift restriction
retain the whole glued map, on the same finite-dimensional stage subtypes. -/
theorem finiteFamily_commonMax_glue
    (f : PointRepresentation.FiniteCompatibleFamily η.toRightComodule θ) :
    (PointRepresentation.FiniteCompatibleFamily.restrictTestLevel.{u, u, v, w, s, r}
        (PointRepresentation.changeTestLevel.{u, u, w, t, max s r} θ)
        (PointRepresentation.FiniteCompatibleFamily.changeTestLevel.{u, u, v, w, t, max s r}
          f)).gluePresentation.toLinearMap =
      ((finiteFamilyEquiv η θ).symm f).toLinearMap :=
  PointRepresentation.FiniteCompatibleFamily.commonMax_gluePresentation_toLinearMap f

end AffineRepresentation

end FiniteSystem

section NormalizedComodules

variable {K C : Type u} [CommRing K] [CommRing C] [HopfAlgebra K C]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Express a comodule over a specified Hopf algebra in the canonical global-
sections coordinates of its spectrum. Only the coefficient factor changes. -/
def normalizeSpecComodule (X : Coalgebra.RightComodule K C V) :
    Coalgebra.RightComodule K Γ(Spec (.of C), ⊤) V :=
  X.mapCoalgebra ((coordinateSpecEquiv (K := K) (C := C)).symm :
    C →ₗc[K] Γ(Spec (.of C), ⊤))

/-- The normalized coaction applies the inverse canonical map to coefficients. -/
@[simp] theorem normalizeSpecComodule_coaction (X : Coalgebra.RightComodule K C V) :
    (normalizeSpecComodule X).coaction =
      (coordinateSpecEquiv (K := K) (C := C)).symm.toLinearMap.lTensor V ∘ₗ X.coaction := rfl

/-- Applying the canonical coefficient map back recovers the original specified
comodule, not merely an isomorphic module. -/
@[simp] theorem normalizeSpecComodule_map_back (X : Coalgebra.RightComodule K C V) :
    (normalizeSpecComodule X).mapCoalgebra
      (coordinateSpecEquiv (K := K) (C := C) : Γ(Spec (.of C), ⊤) →ₗc[K] C) = X := by
  rw [normalizeSpecComodule, Coalgebra.RightComodule.mapCoalgebra_comp]
  have h : (coordinateSpecEquiv (K := K) (C := C) : Γ(Spec (.of C), ⊤) →ₗc[K] C).comp
      ((coordinateSpecEquiv (K := K) (C := C)).symm : C →ₗc[K] Γ(Spec (.of C), ⊤)) =
        CoalgHom.id K C := by
    ext x
    exact (coordinateSpecEquiv (K := K) (C := C)).apply_symm_apply x
  rw [h, Coalgebra.RightComodule.mapCoalgebra_id]

/-- The two explicit coefficient changes cancel in every evaluated action,
for an independently sized coefficient algebra and arbitrary module. -/
theorem normalizeSpecComodule_evaluate (X : Coalgebra.RightComodule K C V)
    {R : Type r} [CommRing R] [Algebra K R] (f : C →ₐ[K] R) :
    (normalizeSpecComodule X).evaluate
        (f.comp (coordinateSpecEquiv (K := K) (C := C)).toAlgEquiv.toAlgHom).toLinearMap =
      X.evaluate f.toLinearMap := by
  let E := coordinateSpecEquiv (K := K) (C := C)
  have he : (f.comp E.toAlgEquiv.toAlgHom).toLinearMap ∘ₗ E.symm.toLinearMap =
      f.toLinearMap := by
    ext c
    exact congrArg f (E.apply_symm_apply c)
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  rw [Coalgebra.RightComodule.evaluate_tmul, Coalgebra.RightComodule.evaluate_tmul,
    normalizeSpecComodule_coaction, LinearMap.comp_apply]
  apply congrArg (fun z ↦ a • z)
  change TensorProduct.map (f.comp E.toAlgEquiv.toAlgHom).toLinearMap
      (LinearMap.id : V →ₗ[K] V)
      (TensorProduct.comm K V Γ(Spec (.of C), ⊤)
        (E.symm.toLinearMap.lTensor V (X.coaction v))) =
    TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V)
      (TensorProduct.comm K V C (X.coaction v))
  rw [LinearMap.lTensor_def, ← TensorProduct.map_comm E.symm.toLinearMap
    (LinearMap.id : V →ₗ[K] V) (X.coaction v), TensorProduct.map_map, he, LinearMap.id_comp]

/-- The geometric action of the normalized comodule is exactly the original
specified coordinate action for a point induced by `f`. -/
theorem normalizeSpecComodule_geometricAction
    (X : Coalgebra.RightComodule K C V)
    (R : Type u) [CommRing R] [Algebra K R] (f : C →ₐ[K] R) :
    (AffineRepresentation.geometricAction (G := Spec (.of C))
      (PointRepresentation.ofRightComodule.{u, u, v, t} (normalizeSpecComodule X)) R
      ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K)))).val =
        (X.pointAction (toConv f)).val := by
  simp only [AffineRepresentation.geometricAction_apply]
  have hA : (PointRepresentation.ofRightComodule.{u, u, v, t}
      (normalizeSpecComodule X)).pointAction (R := R) =
        (normalizeSpecComodule X).pointAction :=
    PointRepresentation.pointAction_ofRightComodule (normalizeSpecComodule X)
  have ha := congrArg
    (fun a : WithConv (Γ(Spec (.of C), ⊤) →ₐ[K] R) →*
        LinearMap.GeneralLinearGroup R (R ⊗[K] V) ↦
      (a (affinePointMulEquiv (K := K) (Spec (.of C)) R
        ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of K))))).val) hA
  have hc := congrArg
    (fun a : Γ(Spec (.of C), ⊤) →ₐ[K] R ↦
      (normalizeSpecComodule X).evaluate a.toLinearMap)
    (affinePointMulEquiv_spec R f)
  exact ha.trans ((Coalgebra.RightComodule.pointAction_val _ _).trans
    (hc.trans (normalizeSpecComodule_evaluate X f)))

end NormalizedComodules

section AdditiveNormalization

variable (K : Type u) [CommRing K]

/-- The infinite polynomial regular comodule, in canonical global-sections
coordinates of the additive group, without replacing its original model. -/
abbrev additivePolynomialCoordinateComodule :=
  normalizeSpecComodule (additiveGroupPolynomialComodule K)

/-- The primitive polynomial coaction reads back after the explicit canonical
map on the coefficient factor. The original symmetric-algebra coalgebra is fixed. -/
theorem additivePolynomialCoordinateComodule_readback (p : Polynomial K) :
    (coordinateSpecEquiv (K := K) (C := additiveGroupCoordinateRing K)).toLinearMap.lTensor
        (Polynomial K) ((additivePolynomialCoordinateComodule K).coaction p) =
      (additiveGroupPolynomialComodule K).coaction p := by
  have h := congrArg Coalgebra.RightComodule.coaction
    (normalizeSpecComodule_map_back (additiveGroupPolynomialComodule K))
  exact LinearMap.congr_fun h p

/-- In canonical coordinates the primitive term is the inverse image of the
original additive coordinate, not a new polynomial Hopf instance. -/
theorem additivePolynomialCoordinateComodule_coaction_X :
    (additivePolynomialCoordinateComodule K).coaction Polynomial.X =
      Polynomial.X ⊗ₜ[K] (1 : Γ(Spec (.of (additiveGroupCoordinateRing K)), ⊤)) +
        (1 : Polynomial K) ⊗ₜ[K]
          (coordinateSpecEquiv (K := K) (C := additiveGroupCoordinateRing K)).symm
            (additiveGroupCoordinate K) := by
  rw [normalizeSpecComodule_coaction, LinearMap.comp_apply,
    additiveGroupPolynomialComodule_coaction_X]
  simp only [map_add, LinearMap.lTensor_tmul]
  rw [coordinateSpecEquiv_symm_toLinearMap_one,
    coordinateSpecEquiv_symm_toLinearMap_apply, coordinateSpecEquiv_symm_apply]

/-- A genuine point of the additive group acts on every polynomial tensor by
the original regular action, after canonical global-sections normalization. -/
theorem additivePolynomialCoordinateComodule_pointAction
    (R : Type u) [CommRing R] [Algebra K R] (x : R) :
    (AffineRepresentation.geometricAction
        (G := Spec (.of (additiveGroupCoordinateRing K)))
        (PointRepresentation.ofRightComodule.{u, u, u, t}
          (additivePolynomialCoordinateComodule K)) R
        (additiveGroupMulEquivPoints K R (Multiplicative.ofAdd x))).val =
      ((additiveGroupPolynomialComodule K).pointAction
        (additiveGroupMulEquivAlgHom K R (Multiplicative.ofAdd x))).val :=
  normalizeSpecComodule_geometricAction (additiveGroupPolynomialComodule K) R
    (additiveGroupMulEquivAlgHom K R (Multiplicative.ofAdd x)).ofConv

end AdditiveNormalization

end AlgebraicGeometry
