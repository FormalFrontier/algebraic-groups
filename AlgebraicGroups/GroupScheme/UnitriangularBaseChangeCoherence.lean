module

public import AlgebraicGroups.GroupScheme.UnitriangularBaseChange
public import AlgebraicGroups.Algebra.UnitriangularBaseChangeCoherence

/-!
# Identity and scalar-tower coherence for the unitriangular group scheme
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits UnitriangularCoordinateRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The base morphism on spectra induced by a scalar extension. -/
abbrev unitriangularBaseMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

theorem unitriangularBaseMap_comp (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    unitriangularBaseMap S T ≫ unitriangularBaseMap R S = unitriangularBaseMap R T := by
  simp only [unitriangularBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq R S T]

theorem unitriangularBaseMap_self (R : Type u) [CommRing R] :
    unitriangularBaseMap R R = 𝟙 (Spec (.of R)) := by
  simp [unitriangularBaseMap]

/-- The canonical group-object compositor for pullback over a scalar tower. -/
def unitriangularGroupSchemeBaseChangeTowerIso
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (Over.pullback (unitriangularBaseMap R T)).mapGrp.obj (unitriangularGroupScheme R ι) ≅
      (Over.pullback (unitriangularBaseMap S T)).mapGrp.obj
        ((Over.pullback (unitriangularBaseMap R S)).mapGrp.obj (unitriangularGroupScheme R ι)) :=
  (eqToIso (congrArg (fun f => (Over.pullback f).mapGrp.obj (unitriangularGroupScheme R ι))
      (unitriangularBaseMap_comp R S T).symm)).trans
    (((Functor.mapGrpNatIso (Over.pullbackComp (unitriangularBaseMap S T)
      (unitriangularBaseMap R S))).app (unitriangularGroupScheme R ι)).trans
    (Functor.mapGrpCompIso.app (unitriangularGroupScheme R ι))
    )

/-- The canonical group-object unit for pullback along the identity of the base. -/
def unitriangularGroupSchemeBaseChangeSelfIso
    (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (Over.pullback (unitriangularBaseMap R R)).mapGrp.obj (unitriangularGroupScheme R ι) ≅
      unitriangularGroupScheme R ι :=
  (eqToIso (congrArg (fun f => (Over.pullback f).mapGrp.obj (unitriangularGroupScheme R ι))
      (unitriangularBaseMap_self R))).trans
    (((Functor.mapGrpNatIso (Over.pullbackId (X := Spec (.of R)))).app
      (unitriangularGroupScheme R ι)).trans
    (Functor.mapGrpIdIso.app (unitriangularGroupScheme R ι)))

private theorem pullbackId_left (R : Type u) [CommRing R]
    (g : Over (Spec (.of R))) :
    ((Over.pullbackId (X := Spec (.of R))).hom.app g).left =
      pullback.fst g.hom (𝟙 (Spec (.of R))) := by
  simp [Over.pullbackId, CategoryTheory.conjugateIsoEquiv,
    CategoryTheory.conjugateEquiv, Over.mapPullbackAdj]

private theorem pullbackComp_left_fst (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] (g : Over (Spec (.of R))) :
    ((Over.pullbackComp (unitriangularBaseMap S T)
      (unitriangularBaseMap R S)).hom.app g).left ≫
        pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  have h := CategoryTheory.conjugateEquiv_counit
    (Over.mapPullbackAdj (unitriangularBaseMap S T ≫ unitriangularBaseMap R S))
    ((Over.mapPullbackAdj (unitriangularBaseMap S T)).comp
      (Over.mapPullbackAdj (unitriangularBaseMap R S)))
    (Over.mapComp (unitriangularBaseMap S T) (unitriangularBaseMap R S)).symm.hom g
  have hleft := congrArg Over.Hom.left h
  simpa [Over.pullbackComp, CategoryTheory.conjugateIsoEquiv,
    Adjunction.comp_counit_app, Over.mapComp] using hleft

private theorem pullbackComp_left_snd (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] (g : Over (Spec (.of R))) :
    ((Over.pullbackComp (unitriangularBaseMap S T)
      (unitriangularBaseMap R S)).hom.app g).left ≫
        pullback.snd _ _ = pullback.snd _ _ := by
  exact ((Over.pullbackComp (unitriangularBaseMap S T)
    (unitriangularBaseMap R S)).hom.app g).w

private theorem identityComparison_ext (R : Type u) [CommRing R]
    (G : Grp (Over (Spec (.of R))))
    (f : Spec (.of R) ⟶ Spec (.of R)) (hf : f = 𝟙 _)
    (c : (Over.pullback f).mapGrp.obj G ⟶ G)
    (hc : c.hom.hom.left = pullback.fst G.X.hom f) :
    c = (eqToIso (congrArg (fun h => (Over.pullback h).mapGrp.obj G) hf)).hom ≫
      ((Functor.mapGrpNatIso (Over.pullbackId (X := Spec (.of R)))).app G).hom ≫
      (Functor.mapGrpIdIso.app G).hom := by
  cases hf
  apply (Grp.forget _).map_injective
  apply Over.OverMorphism.ext
  change c.hom.hom.left = _
  rw [hc]
  change pullback.fst G.X.hom (𝟙 (Spec (.of R))) =
    ((Over.pullbackId (X := Spec (.of R))).hom.app G.X ≫ 𝟙 G.X).left
  simp only [Over.comp_left, Over.id_left, pullbackId_left]
  simp

private theorem pullbackTransportOver_snd (R T : Type u)
    [CommRing R] [CommRing T]
    (g : Over (Spec (.of R)))
    (f h : Spec (.of T) ⟶ Spec (.of R)) (hf : f = h) :
    (eqToIso (congrArg (fun k => (Over.pullback k).obj g) hf)).hom.left ≫
      pullback.snd g.hom h = pullback.snd g.hom f := by
  cases hf
  rfl

private theorem pullbackTransportOver_fst (R T : Type u)
    [CommRing R] [CommRing T]
    (g : Over (Spec (.of R)))
    (f h : Spec (.of T) ⟶ Spec (.of R)) (hf : f = h) :
    (eqToIso (congrArg (fun k => (Over.pullback k).obj g) hf)).hom.left ≫
      pullback.fst g.hom h = pullback.fst g.hom f := by
  cases hf
  rfl

private theorem pullbackGrpTransport_left_eq (R T : Type u)
    [CommRing R] [CommRing T]
    (G : Grp (Over (Spec (.of R))))
    (f g : Spec (.of T) ⟶ Spec (.of R)) (hf : f = g) :
    (eqToIso (congrArg (fun h => (Over.pullback h).mapGrp.obj G) hf)).hom.hom.hom.left =
      (eqToIso (congrArg (fun h => (Over.pullback h).obj G.X) hf)).hom.left := by
  cases hf
  rfl

private def affineBaseChangeIso (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (unitriangularBaseMap S T) ≅ Spec (.of (T ⊗[S] A)) :=
  (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap S A)))
    (unitriangularBaseMap S T)).trans (pullbackSpecIso S T A)

private theorem affineBaseChangeIso_hom_fst (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] :
    (affineBaseChangeIso S T A).hom ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (unitriangularBaseMap S T) := by
  simp only [affineBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd]

private theorem affineBaseChangeIso_hom_snd (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] :
    (affineBaseChangeIso S T A).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[S] A)) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (unitriangularBaseMap S T) := by
  simp only [affineBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullbackSpecIso_hom_fst, pullbackSymmetry_hom_comp_fst]

private theorem affineBaseChangeIso_inv_fst (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] :
    (affineBaseChangeIso S T A).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (unitriangularBaseMap S T) =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A))) := by
  rw [← affineBaseChangeIso_hom_fst S T A, Iso.inv_hom_id_assoc]

private theorem affineBaseChangeIso_inv_snd (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] :
    (affineBaseChangeIso S T A).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (unitriangularBaseMap S T) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[S] A)) := by
  rw [← affineBaseChangeIso_hom_snd S T A, Iso.inv_hom_id_assoc]

private def affineAsOverIso (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] :
    (Over.pullback (unitriangularBaseMap R S)).obj
        ((Spec (.of A)).asOver (Spec (.of R))) ≅
      (Spec (.of (S ⊗[R] A))).asOver (Spec (.of S)) :=
  Over.isoMk (affineBaseChangeIso R S A) (by
    exact (affineBaseChangeIso_hom_snd R S A))

private theorem affineAsOverIso_hom_left (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] :
    (affineAsOverIso R S A).hom.left = (affineBaseChangeIso R S A).hom := rfl

private theorem affineAsOver_hom (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] :
    ((Spec (.of A)).asOver (Spec (.of R))).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl

private theorem affineHom_ext (S T A : Type u)
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A]
    {X : Scheme} (f g : X ⟶ Spec (.of (T ⊗[S] A)))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A))) =
      g ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A))))
    (hg : f ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[S] A)) =
      g ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[S] A))) :
    f = g := by
  rw [← cancel_mono (affineBaseChangeIso S T A).inv]
  apply pullback.hom_ext
  · simpa only [Category.assoc, affineBaseChangeIso_inv_fst] using hf
  · simpa only [Category.assoc, affineBaseChangeIso_inv_snd] using hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem affinePullbackMap (S T A B : Type u)
    [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra S A] [Algebra S B]
    (e : B ≃ₐ[S] A) :
    (affineBaseChangeIso S T A).inv ≫
      ((Over.pullback (unitriangularBaseMap S T)).map
        ((algSpec (.of S)).map (.op (CommAlgCat.ofHom e.toAlgHom)))).left ≫
      (affineBaseChangeIso S T B).hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.congr
            (AlgEquiv.refl : T ≃ₐ[T] T) e).toAlgHom.toRingHom) := by
  apply (Iso.eq_comp_inv (affineBaseChangeIso S T B)
    (f := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : T ≃ₐ[T] T) e).toAlgHom.toRingHom))
    (g := (affineBaseChangeIso S T A).inv ≫
      ((Over.pullback (unitriangularBaseMap S T)).map
        ((algSpec (.of S)).map (.op (CommAlgCat.ofHom e.toAlgHom)))).left)).mp
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, algSpec_obj_hom]
    rw [Category.assoc, pullback.lift_fst]
    simp only [← Category.assoc, affineBaseChangeIso_inv_fst, algSpec_map_left]
    simp only [Category.assoc, affineBaseChangeIso_inv_fst]
    change Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A))) ≫
        Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) e).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight : B →ₐ[S] T ⊗[S] B)))
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · simp only [Over.pullback_map_left, algSpec_obj_hom]
    rw [Category.assoc, pullback.lift_snd]
    simp only [Category.assoc, affineBaseChangeIso_inv_snd]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro t
    simp [Algebra.TensorProduct.congr_apply]

private theorem affineCancel_fst_fst (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R A] :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.cancelBaseChange R S T T A).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight :
          S ⊗[R] A →ₐ[S] T ⊗[S] (S ⊗[R] A)))) ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A))) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]
  simp

private theorem affineCancel_fst_snd (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R A] :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.cancelBaseChange R S T T A).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight :
          S ⊗[R] A →ₐ[S] T ⊗[S] (S ⊗[R] A)))) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A)) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R] A)) ≫
      unitriangularBaseMap S T := by
  simp only [unitriangularBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro s
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (s ⊗ₜ[R] (1 : A))) =
        (algebraMap S T s) ⊗ₜ[R] (1 : A)
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]
  simp [Algebra.smul_def]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem affineComp (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R A] :
    (affineBaseChangeIso R T A).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.cancelBaseChange R S T T A).toAlgHom.toRingHom) =
      (eqToIso (congrArg (fun f => (Over.pullback f).obj
          ((Spec (.of A)).asOver (Spec (.of R))))
        (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
      ((Over.pullbackComp (unitriangularBaseMap S T)
        (unitriangularBaseMap R S)).hom.app
          ((Spec (.of A)).asOver (Spec (.of R)))).left ≫
      ((Over.pullback (unitriangularBaseMap S T)).map
        (affineAsOverIso R S A).hom).left ≫
      (affineBaseChangeIso S T (S ⊗[R] A)).hom := by
  apply affineHom_ext S T (S ⊗[R] A)
  · simp only [Category.assoc, affineBaseChangeIso_hom_fst, Over.pullback_map_left,
      Over.pullback_obj_left, affineAsOver_hom]
    rw [pullback.lift_fst]
    rw [affineAsOverIso_hom_left]
    apply affineHom_ext R S A
    · have hCancel := congrArg (fun f => (affineBaseChangeIso R T A).hom ≫ f)
        (affineCancel_fst_fst R S T A)
      have hMate := pullbackComp_left_fst R S T
        ((Spec (.of A)).asOver (Spec (.of R)))
      have hTransport := pullbackTransportOver_fst R T
        ((Spec (.of A)).asOver (Spec (.of R)))
        (unitriangularBaseMap R T)
        (unitriangularBaseMap S T ≫ unitriangularBaseMap R S)
        (unitriangularBaseMap_comp R S T).symm
      have hComposed := congrArg
        (fun f => (eqToIso (congrArg (fun k => (Over.pullback k).obj
          ((Spec (.of A)).asOver (Spec (.of R))))
          (unitriangularBaseMap_comp R S T).symm)).hom.left ≫ f) hMate
      calc
        _ = (affineBaseChangeIso R T A).hom ≫ Spec.map
            (CommRingCat.ofHom (RingHomClass.toRingHom
              (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A))) := by
              simpa only [Category.assoc] using hCancel
        _ = pullback.fst _ _ := affineBaseChangeIso_hom_fst R T A
        _ = _ := by
          simpa only [Category.assoc, affineBaseChangeIso_hom_fst,
            affineAsOver_hom] using (hComposed.trans hTransport).symm
    · have hCancel := congrArg (fun f => (affineBaseChangeIso R T A).hom ≫ f)
        (affineCancel_fst_snd R S T A)
      calc
        _ = (affineBaseChangeIso R T A).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R] A)) ≫
              unitriangularBaseMap S T := by
                simpa only [Category.assoc] using hCancel
        _ = pullback.snd _ _ ≫ unitriangularBaseMap S T := by
          rw [← Category.assoc, affineBaseChangeIso_hom_snd R T A]
        _ = _ := by
          have hCondition :
              pullback.fst
                  ((Over.pullback (unitriangularBaseMap R S)).obj
                    ((Spec (.of A)).asOver (Spec (.of R)))).hom
                  (unitriangularBaseMap S T) ≫
                pullback.snd ((Spec (.of A)).asOver (Spec (.of R))).hom
                  (unitriangularBaseMap R S) =
                pullback.snd
                    ((Over.pullback (unitriangularBaseMap R S)).obj
                      ((Spec (.of A)).asOver (Spec (.of R)))).hom
                    (unitriangularBaseMap S T) ≫ unitriangularBaseMap S T := by
            exact pullback.condition
          have hMate := pullbackComp_left_snd R S T
            ((Spec (.of A)).asOver (Spec (.of R)))
          have hTransport := pullbackTransportOver_snd R T
            ((Spec (.of A)).asOver (Spec (.of R)))
            (unitriangularBaseMap R T)
            (unitriangularBaseMap S T ≫ unitriangularBaseMap R S)
            (unitriangularBaseMap_comp R S T).symm
          have hTotal :
              (eqToIso (congrArg (fun f => (Over.pullback f).obj
                ((Spec (.of A)).asOver (Spec (.of R))))
                (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
                ((Over.pullbackComp (unitriangularBaseMap S T)
                  (unitriangularBaseMap R S)).hom.app
                    ((Spec (.of A)).asOver (Spec (.of R)))).left ≫
                pullback.fst
                    ((Over.pullback (unitriangularBaseMap R S)).obj
                      ((Spec (.of A)).asOver (Spec (.of R)))).hom
                    (unitriangularBaseMap S T) ≫
                pullback.snd ((Spec (.of A)).asOver (Spec (.of R))).hom
                  (unitriangularBaseMap R S) =
                pullback.snd ((Spec (.of A)).asOver (Spec (.of R))).hom
                  (unitriangularBaseMap R T) ≫ unitriangularBaseMap S T := by
            calc
              _ = (eqToIso (congrArg (fun f => (Over.pullback f).obj
                    ((Spec (.of A)).asOver (Spec (.of R))))
                    (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
                  ((Over.pullbackComp (unitriangularBaseMap S T)
                    (unitriangularBaseMap R S)).hom.app
                      ((Spec (.of A)).asOver (Spec (.of R)))).left ≫
                  pullback.snd
                    ((Over.pullback (unitriangularBaseMap R S)).obj
                      ((Spec (.of A)).asOver (Spec (.of R)))).hom
                    (unitriangularBaseMap S T) ≫ unitriangularBaseMap S T := by
                simpa only [Category.assoc] using congrArg (fun f =>
                  (eqToIso (congrArg (fun k => (Over.pullback k).obj
                    ((Spec (.of A)).asOver (Spec (.of R))))
                    (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
                    ((Over.pullbackComp (unitriangularBaseMap S T)
                      (unitriangularBaseMap R S)).hom.app
                        ((Spec (.of A)).asOver (Spec (.of R)))).left ≫ f) hCondition
              _ = _ := by
                simpa only [Category.assoc] using
                  ((congrArg (fun f =>
                    (eqToIso (congrArg (fun k => (Over.pullback k).obj
                      ((Spec (.of A)).asOver (Spec (.of R))))
                      (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
                      f ≫ unitriangularBaseMap S T) hMate).trans
                    (congrArg (fun f => f ≫ unitriangularBaseMap S T) hTransport))
          simpa only [Category.assoc, affineBaseChangeIso_hom_snd,
            affineAsOver_hom, Over.pullback_obj_hom] using hTotal.symm

  · simp only [Category.assoc, affineBaseChangeIso_hom_snd, Over.pullback_map_left,
      Over.pullback_obj_left, affineAsOver_hom]
    rw [pullback.lift_snd]
    simp only [← Category.assoc, pullbackComp_left_snd]
    rw [pullbackTransportOver_snd R T
      ((Spec (.of A)).asOver (Spec (.of R)))
      (unitriangularBaseMap R T)
      (unitriangularBaseMap S T ≫ unitriangularBaseMap R S)
      (unitriangularBaseMap_comp R S T).symm]
    have hAlgebra :
        (Algebra.TensorProduct.cancelBaseChange R S T T A).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom :
              T →+* T ⊗[S] (S ⊗[R] A)) =
          (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R] A) := by
      apply RingHom.ext
      intro t
      exact (Algebra.TensorProduct.cancelBaseChange R S T T A).commutes t
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hAlgebra]
    exact affineBaseChangeIso_hom_snd R T A

set_option maxHeartbeats 1000000 in
private theorem towerIso_left (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (unitriangularGroupSchemeBaseChangeTowerIso R S T ι).hom.hom.hom.left =
      (eqToIso (congrArg (fun f => (Over.pullback f).obj
        (unitriangularGroupScheme R ι).X)
        (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
      ((Over.pullbackComp (unitriangularBaseMap S T)
        (unitriangularBaseMap R S)).hom.app
          (unitriangularGroupScheme R ι).X).left := by
  simp only [unitriangularGroupSchemeBaseChangeTowerIso, Iso.trans_hom,
    Grp.comp_hom_hom, Over.comp_left]
  rw [pullbackGrpTransport_left_eq R T (unitriangularGroupScheme R ι)
    (unitriangularBaseMap R T)
    (unitriangularBaseMap S T ≫ unitriangularBaseMap R S)
    (unitriangularBaseMap_comp R S T).symm]
  change _ ≫ ((Over.pullbackComp (unitriangularBaseMap S T)
    (unitriangularBaseMap R S)).hom.app (unitriangularGroupScheme R ι).X).left ≫
    𝟙 _ = _
  simp only [Category.comp_id]
  rfl

theorem unitriangularGroupSchemeBaseChangeIso_self
    (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (unitriangularGroupSchemeBaseChangeIso R R ι).hom =
      (unitriangularGroupSchemeBaseChangeSelfIso R ι).hom := by
  apply identityComparison_ext R (unitriangularGroupScheme R ι)
    (unitriangularBaseMap R R) (unitriangularBaseMap_self R)
  rw [unitriangularGroupSchemeBaseChangeIso_hom_left]
  have hRing :
      (baseChangeBialgEquiv R R ι).symm.toBialgHom.toAlgHom.toRingHom =
        (Algebra.TensorProduct.includeRight :
          CoordinateRing R ι →ₐ[R] R ⊗[R] CoordinateRing R ι).toRingHom := by
    apply RingHom.ext
    intro a
    change (baseChange R R ι).symm a = (1 : R) ⊗ₜ[R] a
    rw [baseChange_self]
    exact Algebra.TensorProduct.lid_symm_apply R a
  rw [hRing]
  change (pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R ι))))
      (unitriangularBaseMap R R) ≪≫
      pullbackSpecIso R R (CoordinateRing R ι)).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight :
            CoordinateRing R ι →ₐ[R] R ⊗[R] CoordinateRing R ι))) =
      pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap R (CoordinateRing R ι)))) (unitriangularBaseMap R R)
  rw [Iso.trans_hom, Category.assoc]
  rw [pullbackSpecIso_hom_snd]
  exact pullbackSymmetry_hom_comp_snd _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Scalar extension from `R` to `T` agrees with successive extension through `S`. -/
theorem unitriangularGroupSchemeBaseChangeIso_tower
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (unitriangularGroupSchemeBaseChangeIso R T ι).hom =
      (unitriangularGroupSchemeBaseChangeTowerIso R S T ι).hom ≫
        (Over.pullback (unitriangularBaseMap S T)).mapGrp.map
          (unitriangularGroupSchemeBaseChangeIso R S ι).hom ≫
        (unitriangularGroupSchemeBaseChangeIso S T ι).hom := by
  letI : HopfAlgebra S (S ⊗[R] CoordinateRing R ι) := inferInstance
  letI : CommRing (S ⊗[R] CoordinateRing R ι) := inferInstance
  letI : Algebra S (S ⊗[R] CoordinateRing R ι) := inferInstance
  letI : CommRing (T ⊗[S] CoordinateRing S ι) := inferInstance
  letI : Algebra T (T ⊗[S] CoordinateRing S ι) := inferInstance
  have hFactor :
      (unitriangularGroupSchemeBaseChangeIso R S ι).hom.hom.hom =
        (affineAsOverIso R S (CoordinateRing R ι)).hom ≫
          (algSpec (.of S)).map (.op (CommAlgCat.ofHom
            (baseChange R S ι).symm.toAlgHom)) := by
    apply Over.OverMorphism.ext
    rw [unitriangularGroupSchemeBaseChangeIso_hom_left]
    rfl
  apply (Grp.forget _).map_injective
  apply Over.OverMorphism.ext
  change (unitriangularGroupSchemeBaseChangeIso R T ι).hom.hom.hom.left =
    (unitriangularGroupSchemeBaseChangeTowerIso R S T ι).hom.hom.hom.left ≫
      ((Over.pullback (unitriangularBaseMap S T)).map
        (unitriangularGroupSchemeBaseChangeIso R S ι).hom.hom.hom).left ≫
      (unitriangularGroupSchemeBaseChangeIso S T ι).hom.hom.hom.left
  rw [unitriangularGroupSchemeBaseChangeIso_hom_left]
  rw [hFactor, Functor.map_comp, Over.comp_left]
  have hComp := affineComp R S T (CoordinateRing R ι)
  have hPulled := affinePullbackMap S T
    (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι)
    (baseChange R S ι).symm
  have hTowerIso := towerIso_left R S T ι
  rw [unitriangularGroupSchemeBaseChangeIso_hom_left S T ι, hTowerIso]
  have hComposition :
      ((eqToIso (congrArg (fun f => (Over.pullback f).obj
          ((Spec (.of (CoordinateRing R ι))).asOver (Spec (.of R))))
        (unitriangularBaseMap_comp R S T).symm)).hom.left ≫
        ((Over.pullbackComp (unitriangularBaseMap S T)
          (unitriangularBaseMap R S)).hom.app
            ((Spec (.of (CoordinateRing R ι))).asOver (Spec (.of R)))).left) ≫
        ((Over.pullback (unitriangularBaseMap S T)).map
          (affineAsOverIso R S (CoordinateRing R ι)).hom).left ≫
        (affineBaseChangeIso S T (S ⊗[R] CoordinateRing R ι)).hom =
      (affineBaseChangeIso R T (CoordinateRing R ι)).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.cancelBaseChange
          R S T T (CoordinateRing R ι)).toAlgHom.toRingHom) := by
    simpa only [Category.assoc] using hComp.symm
  have hBase (a : CoordinateRing T ι) :
      (baseChange R T ι).symm a =
        (Algebra.TensorProduct.cancelBaseChange R S T T (CoordinateRing R ι))
          ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
            (baseChange R S ι)).symm ((baseChange S T ι).symm a)) := by
    apply (baseChange R T ι).injective
    have h := congrArg (fun e => e
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
        (baseChange R S ι)).symm ((baseChange S T ι).symm a)))
        (baseChange_tower R S T ι)
    simpa only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] using h.symm
  have hAlgebraMaps :
      Spec.map (CommRingCat.ofHom
        (baseChangeBialgEquiv R T ι).symm.toBialgHom.toAlgHom.toRingHom) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.cancelBaseChange
          R S T T (CoordinateRing R ι)).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr
          (AlgEquiv.refl : T ≃ₐ[T] T)
          (baseChange R S ι).symm).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (baseChangeBialgEquiv S T ι).symm.toBialgHom.toAlgHom.toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    exact hBase a
  rw [hAlgebraMaps]
  change (affineBaseChangeIso R T (CoordinateRing R ι)).hom ≫ _ = _
  simp only [← Category.assoc]
  rw [← hComposition]
  rw [← hPulled]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry
