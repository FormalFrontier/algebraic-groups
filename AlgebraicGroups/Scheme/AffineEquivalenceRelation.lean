/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Category.EquivalenceRelation
public import AlgebraicGroups.RingTheory.TargetCopy
public import AlgebraicGroups.Scheme.AffinePullback
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

/-!
# Coordinates of an affine internal equivalence relation

This file transports the composition morphism of an internal affine-scheme
relation to the explicit mixed tensor-product presentation.  The resulting
cartesian square and outer groupoid identities are the inputs for invariance
of finite-projective characteristic polynomials.
-/

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.AffineEquivalenceRelation

universe uC u

variable {C : Type uC} {A B : Type u}
  [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B] [Algebra A B] [IsScalarTower C A B]

/-- The scheme morphism contravariantly induced by an algebra homomorphism. -/
abbrev specMap (f : A →ₐ[C] B) :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

omit [Algebra A B] [IsScalarTower C A B] in
/-- Both coordinate-ring maps of an affine internal equivalence relation are
injective.  Contravariantly, the reflexivity morphism is a common left inverse
of the two ring maps. -/
lemma maps_injective_of_equivalenceRelation (s t : A →ₐ[C] B)
    (h : EquivalenceRelation (specMap s) (specMap t)) :
    Function.Injective s ∧ Function.Injective t := by
  have map_injective (f : A →ₐ[C] B)
      (hf : h.r ≫ specMap f = 𝟙 _) : Function.Injective f := by
    let r : B →+* A := (Spec.preimage h.r).hom
    have hrf : r.comp f.toRingHom = RingHom.id A := by
      have hrfCat : CommRingCat.ofHom f.toRingHom ≫ Spec.preimage h.r = 𝟙 _ := by
        apply Spec.map_injective
        simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using hf
      exact congr_arg CommRingCat.Hom.hom hrfCat
    intro x y hxy
    calc
      x = r (f x) := by
        change x = (r.comp f.toRingHom) x
        rw [hrf]
        rfl
      _ = r (f y) := congr_arg r hxy
      _ = y := by
        change (r.comp f.toRingHom) y = y
        rw [hrf]
        rfl
  exact ⟨map_injective s h.reflexivity₁, map_injective t h.reflexivity₂⟩

/-- The composition morphism of an internal affine-scheme equivalence relation,
transported from its arbitrary limiting pullback cone to the explicit mixed
tensor product.  The two equations are the outer groupoid identities used by
the invariant-coordinate calculation. -/
lemma exists_composition_coordinates (s t : A →ₐ[C] B)
    (hs : IsScalarTower.toAlgHom C A B = s)
    (h : EquivalenceRelation (specMap s) (specMap t)) :
    letI : Algebra C (TargetCopy B) :=
      (targetCopyMap (algebraMap C B)).toAlgebra
    letI : Algebra A (TargetCopy B) :=
      (targetCopyMap t.toRingHom).toAlgebra
    letI : IsScalarTower C A (TargetCopy B) := targetCopy_isScalarTower t
    letI : Algebra C (TargetCopy B ⊗[A] B) :=
      Algebra.TensorProduct.leftAlgebra
    ∃ (p0 p1 c : B →ₐ[C] TargetCopy B ⊗[A] B),
      (∀ x, p0 x = (1 : TargetCopy B) ⊗ₜ[A] x) ∧
      (∀ x, p1 x = TargetCopy.mk x ⊗ₜ[A] (1 : B)) ∧
      p0.comp s = p1.comp t ∧
      c.comp s = p1.comp s ∧
      c.comp t = p0.comp t ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom c.toRingHom))
        (Spec.map (CommRingCat.ofHom p1.toRingHom))
        (specMap s) (specMap s) := by
  subst s
  let s : A →ₐ[C] B := IsScalarTower.toAlgHom C A B
  change EquivalenceRelation (specMap s) (specMap t) at h
  let _ : Algebra C (TargetCopy B) :=
    (targetCopyMap (algebraMap C B)).toAlgebra
  let _ : Algebra A (TargetCopy B) :=
    (targetCopyMap t.toRingHom).toAlgebra
  let _ : IsScalarTower C A (TargetCopy B) := targetCopy_isScalarTower t
  let _ : Algebra C (TargetCopy B ⊗[A] B) :=
    Algebra.TensorProduct.leftAlgebra
  let eCopy : B ≃ₐ[C] TargetCopy B :=
    AlgEquiv.ofRingEquiv (f := TargetCopy.ringEquiv.symm) (fun _ ↦ rfl)
  let p0 : B →ₐ[C] TargetCopy B ⊗[A] B :=
    (Algebra.TensorProduct.includeRight :
      B →ₐ[A] TargetCopy B ⊗[A] B).restrictScalars C
  let p1 : B →ₐ[C] TargetCopy B ⊗[A] B :=
    (Algebra.TensorProduct.includeLeft :
      TargetCopy B →ₐ[C] TargetCopy B ⊗[A] B).comp eCopy.toAlgHom
  have hp0p1 : p0.comp s = p1.comp t := by
    ext x
    simp [p0, p1, eCopy, s]
    change TargetCopy.mk (t x) ⊗ₜ[A] (1 : B) =
      TargetCopy.mk (t x) ⊗ₜ[A] (1 : B)
    rfl
  let iCopy : Spec (.of (TargetCopy B)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom eCopy.toRingHom)
  let eCat : CommRingCat.of B ≅ CommRingCat.of (TargetCopy B) :=
    eCopy.toRingEquiv.toCommRingCatIso
  have heCat : IsIso eCat.hom := eCat.isIso_hom
  let _ : IsIso eCat.hom := heCat
  have hiCopy : IsIso iCopy := by
    change IsIso (Spec.map eCat.hom)
    infer_instance
  let _ : IsIso iCopy := hiCopy
  have hCopy :
      Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))) ≫ 𝟙 _ =
        iCopy ≫ specMap t := by
    simp only [Category.comp_id]
    dsimp [iCopy]
    rw [← Spec.map_comp]
    congr 1
  have hStructural :
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ 𝟙 _ =
        𝟙 _ ≫ specMap s := by
    simp only [Category.comp_id, Category.id_comp]
    congr 1
  let m :
      pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶
      pullback (specMap t) (specMap s) :=
    pullback.map
      (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (specMap t) (specMap s) iCopy (𝟙 _) (𝟙 _)
      hCopy hStructural
  have hm : IsIso m := by
    dsimp [m]
    infer_instance
  let _ : IsIso m := hm
  have hm_fst : m ≫ pullback.fst (specMap t) (specMap s) =
      pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ iCopy := by
    exact pullback.lift_fst _ _ _
  have hm_snd : m ≫ pullback.snd (specMap t) (specMap s) =
      pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    change pullback.lift
        (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
            (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ iCopy)
        (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
            (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ 𝟙 _)
        _ ≫ pullback.snd (specMap t) (specMap s) = _
    rw [pullback.lift_snd, Category.comp_id]
  let mIso :
      pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A (TargetCopy B))))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
        pullback (specMap t) (specMap s) :=
    @asIso Scheme _ _ _ m hm
  let k : Spec (.of (TargetCopy B ⊗[A] B)) ≅
      pullback (specMap t) (specMap s) :=
    (pullbackSpecIso A (TargetCopy B) B).symm.trans mIso
  have hkfst : k.hom ≫ pullback.fst (specMap t) (specMap s) =
      Spec.map (CommRingCat.ofHom p1.toRingHom) := by
    change ((pullbackSpecIso A (TargetCopy B) B).inv ≫ m) ≫
      pullback.fst (specMap t) (specMap s) = _
    rw [Category.assoc, hm_fst, ← Category.assoc, pullbackSpecIso_inv_fst]
    rw [← Spec.map_comp]
    rfl
  have hksnd : k.hom ≫ pullback.snd (specMap t) (specMap s) =
      Spec.map (CommRingCat.ofHom p0.toRingHom) := by
    change ((pullbackSpecIso A (TargetCopy B) B).inv ≫ m) ≫
      pullback.snd (specMap t) (specMap s) = _
    rw [Category.assoc, hm_snd]
    exact pullbackSpecIso_inv_snd A (TargetCopy B) B
  let q : PullbackCone (specMap t) (specMap s) :=
    PullbackCone.mk
      (k.hom ≫ pullback.fst (specMap t) (specMap s))
      (k.hom ≫ pullback.snd (specMap t) (specMap s))
      (by simp only [Category.assoc, pullback.condition])
  let hq : IsLimit q := by
    dsimp only [q]
    refine PullbackCone.IsLimit.mk _
      (fun z ↦ pullback.lift z.fst z.snd z.condition ≫ k.inv) ?_ ?_ ?_
    · intro z
      calc
        (pullback.lift z.fst z.snd z.condition ≫ k.inv) ≫
            (k.hom ≫ pullback.fst (specMap t) (specMap s)) =
          pullback.lift z.fst z.snd z.condition ≫
            ((k.inv ≫ k.hom) ≫ pullback.fst (specMap t) (specMap s)) := by
              simp only [Category.assoc]
        _ = pullback.lift z.fst z.snd z.condition ≫
            pullback.fst (specMap t) (specMap s) := by simp
        _ = z.fst := pullback.lift_fst _ _ _
    · intro z
      calc
        (pullback.lift z.fst z.snd z.condition ≫ k.inv) ≫
            (k.hom ≫ pullback.snd (specMap t) (specMap s)) =
          pullback.lift z.fst z.snd z.condition ≫
            ((k.inv ≫ k.hom) ≫ pullback.snd (specMap t) (specMap s)) := by
              simp only [Category.assoc]
        _ = pullback.lift z.fst z.snd z.condition ≫
            pullback.snd (specMap t) (specMap s) := by simp
        _ = z.snd := pullback.lift_snd _ _ _
    · intro z n hn0 hn1
      rw [← cancel_mono k.hom]
      apply pullback.hom_ext
      · simpa only [Category.assoc, k.inv_hom_id, Category.comp_id,
          pullback.lift_fst] using hn0
      · simpa only [Category.assoc, k.inv_hom_id, Category.comp_id,
          pullback.lift_snd] using hn1
  let j : h.c.pt ≅ q.pt := h.isLimit.conePointUniqueUpToIso hq
  let j' : h.c.pt ≅ Spec (.of (TargetCopy B ⊗[A] B)) := j
  let compScheme : Spec (.of (TargetCopy B ⊗[A] B)) ⟶ Spec (.of B) :=
    j'.inv ≫ h.t
  have htransitivity₁ : h.t ≫ specMap s = h.c.fst ≫ specMap s :=
    h.transitivity₁
  have htransitivity₂ : h.t ≫ specMap t = h.c.snd ≫ specMap t :=
    h.transitivity₂
  have hjfst : j'.inv ≫ h.c.fst = q.fst := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp h.isLimit hq
      WalkingCospan.left
  have hjsnd : j'.inv ≫ h.c.snd = q.snd := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp h.isLimit hq
      WalkingCospan.right
  have hcomp_s : compScheme ≫ specMap s =
      Spec.map (CommRingCat.ofHom p1.toRingHom) ≫ specMap s := by
    change (j'.inv ≫ h.t) ≫ specMap s = _
    rw [Category.assoc, htransitivity₁, ← Category.assoc, hjfst]
    change (k.hom ≫ pullback.fst (specMap t) (specMap s)) ≫
      specMap s = _
    rw [hkfst]
  have hcomp_t : compScheme ≫ specMap t =
      Spec.map (CommRingCat.ofHom p0.toRingHom) ≫ specMap t := by
    change (j'.inv ≫ h.t) ≫ specMap t = _
    rw [Category.assoc, htransitivity₂, ← Category.assoc, hjsnd]
    change (k.hom ≫ pullback.snd (specMap t) (specMap s)) ≫
      specMap t = _
    rw [hksnd]
  let cRing : B →+* TargetCopy B ⊗[A] B := (Spec.preimage compScheme).hom
  have hcRing_s : cRing.comp s.toRingHom = p1.toRingHom.comp s.toRingHom := by
    change (CommRingCat.ofHom s.toRingHom ≫ Spec.preimage compScheme).hom =
      (CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom p1.toRingHom).hom
    congr 1
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage] using hcomp_s
  have hcRing_t : cRing.comp t.toRingHom = p0.toRingHom.comp t.toRingHom := by
    change (CommRingCat.ofHom t.toRingHom ≫ Spec.preimage compScheme).hom =
      (CommRingCat.ofHom t.toRingHom ≫ CommRingCat.ofHom p0.toRingHom).hom
    congr 1
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage] using hcomp_t
  have hc_commutes (x : C) : cRing (algebraMap C B x) =
      algebraMap C (TargetCopy B ⊗[A] B) x := by
    calc
      cRing (algebraMap C B x) = cRing (s (algebraMap C A x)) := by
        rw [s.commutes]
      _ = p1 (s (algebraMap C A x)) := DFunLike.congr_fun hcRing_s _
      _ = algebraMap C (TargetCopy B ⊗[A] B) x := (p1.comp s).commutes x
  let c : B →ₐ[C] TargetCopy B ⊗[A] B :=
    { cRing with commutes' := hc_commutes }
  have hc_s : c.comp s = p1.comp s := by
    ext x
    exact DFunLike.congr_fun hcRing_s x
  have hc_t : c.comp t = p0.comp t := by
    ext x
    exact DFunLike.congr_fun hcRing_t x
  have hcSpec : Spec.map (CommRingCat.ofHom c.toRingHom) = compScheme := by
    change Scheme.Spec.map (Scheme.Spec.preimage compScheme) = compScheme
    exact Scheme.Spec.map_preimage compScheme
  have hp1Spec : j'.inv ≫ h.c.fst =
      Spec.map (CommRingCat.ofHom p1.toRingHom) := by
    rw [hjfst]
    change k.hom ≫ pullback.fst (specMap t) (specMap s) = _
    exact hkfst
  let hderived : IsLimit
      (PullbackCone.mk h.t h.c.fst h.transitivity₁) :=
    CategoryTheory.EquivalenceRelation.isLimit_composition_fst h
  let derivedLift (z : PullbackCone (specMap s) (specMap s)) :
      z.pt ⟶ h.c.pt := hderived.lift z
  have derivedLift_t (z : PullbackCone (specMap s) (specMap s)) :
      derivedLift z ≫ h.t = z.fst := by
    exact hderived.fac z WalkingCospan.left
  have derivedLift_fst (z : PullbackCone (specMap s) (specMap s)) :
      derivedLift z ≫ h.c.fst = z.snd := by
    exact hderived.fac z WalkingCospan.right
  have derived_hom_ext {W : Scheme}
      {f g : W ⟶ h.c.pt} (h0 : f ≫ h.t = g ≫ h.t)
      (h1 : f ≫ h.c.fst = g ≫ h.c.fst) : f = g := by
    exact PullbackCone.IsLimit.hom_ext hderived h0 h1
  have hcartLimit : IsLimit
      (PullbackCone.mk
        (Spec.map (CommRingCat.ofHom c.toRingHom))
        (Spec.map (CommRingCat.ofHom p1.toRingHom))
        (by rw [hcSpec]; exact hcomp_s)) := by
    refine PullbackCone.IsLimit.mk (by rw [hcSpec]; exact hcomp_s)
      (fun z ↦ derivedLift z ≫ j'.hom) ?_ ?_ ?_
    · intro z
      rw [hcSpec]
      change (derivedLift z ≫ j'.hom) ≫ (j'.inv ≫ h.t) = z.fst
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        derivedLift_t z
    · intro z
      rw [← hp1Spec]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        derivedLift_fst z
    · intro z m hm0 hm1
      have hpre : m ≫ j'.inv = derivedLift z := by
        apply derived_hom_ext
        · calc
            (m ≫ j'.inv) ≫ h.t =
                m ≫ Spec.map (CommRingCat.ofHom c.toRingHom) := by
                  rw [Category.assoc, hcSpec]
            _ = z.fst := hm0
            _ = derivedLift z ≫ h.t := (derivedLift_t z).symm
        · calc
            (m ≫ j'.inv) ≫ h.c.fst =
                m ≫ Spec.map (CommRingCat.ofHom p1.toRingHom) := by
                  rw [Category.assoc, hp1Spec]
            _ = z.snd := hm1
            _ = derivedLift z ≫ h.c.fst := (derivedLift_fst z).symm
      calc
        m = (m ≫ j'.inv) ≫ j'.hom := by simp
        _ = derivedLift z ≫ j'.hom := by rw [hpre]
  have hcart : IsPullback
      (Spec.map (CommRingCat.ofHom c.toRingHom))
      (Spec.map (CommRingCat.ofHom p1.toRingHom))
      (specMap s) (specMap s) := by
    exact IsPullback.of_isLimit hcartLimit
  exact ⟨p0, p1, c, fun _ ↦ rfl, fun _ ↦ rfl, hp0p1, hc_s, hc_t, hcart⟩

end AlgebraicGeometry.AffineEquivalenceRelation
