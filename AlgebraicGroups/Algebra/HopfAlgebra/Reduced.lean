/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.ULift
public import AlgebraicGroups.GroupScheme.Reduction
public import AlgebraicGroups.Scheme.GeometricallyReduced
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smoothness of the reduced quotient of a Hopf algebra

Over a perfect field, the quotient of a finite-type commutative Hopf algebra by its
nilradical is smooth. The proof uses the canonical scheme reduction of its spectrum:
the reduced self-product supplies the existing group structure on the reduction,
and geometric reducedness then gives smoothness. The affine chart of the canonical
reduction identifies the resulting coefficient map with the original map to the quotient.
No Hopf algebra structure on the quotient is constructed.

Scalar and carrier universes are independent. The common-universe geometric argument
is private; the public theorem uses the full Hopf algebra lift and descends smoothness
through the scalar and quotient ring equivalences.

## References

- J. S. Milne, *Algebraic Groups*, Corollary 1.39, for the subgroup structure on
  the reduction over a perfect field.
- The existing `Scheme.reductionOverGrpObj` and Mathlib's
  `AlgebraicGeometry.smooth_of_grpObj` provide the group-scheme reduction and
  smoothness steps.
-/

public section

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry

universe u v

namespace HopfAlgebra

private lemma nilradical_eq_map_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    nilradical S = (nilradical R).map e.toRingHom := by
  have hker : RingHom.ker e.toRingHom ≤ (⊥ : Ideal R) := by
    intro x hx
    change x = 0
    apply e.injective
    change e x = 0 at hx
    simpa only [map_zero] using hx
  change (⊥ : Ideal S).radical = ((⊥ : Ideal R).radical).map e.toRingHom
  rw [Ideal.map_radical_of_surjective e.surjective hker, Ideal.map_bot]

private theorem smooth_quotient_nilradical_aux
    (K H : Type u) [Field K] [PerfectField K] [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] :
    Algebra.Smooth K (H ⧸ nilradical H) := by
  classical
  let X : Scheme.{u} := Spec (.of H)
  let G : Over (Spec (.of K)) := X.asOver (Spec (.of K))
  let Gr : Over (Spec (.of K)) := Scheme.reductionOver G
  let _ : LocallyOfFiniteType G.hom := by
    change LocallyOfFiniteType (Spec (.of H) ↘ Spec (.of K))
    infer_instance
  let _ : IsClosedImmersion (Scheme.reductionι.app G.left) :=
    inferInstanceAs (IsClosedImmersion (Scheme.reductionOverι G).left)
  let _ : LocallyOfFiniteType Gr.hom := by
    change LocallyOfFiniteType (Scheme.reductionι.app G.left ≫ G.hom)
    infer_instance
  let _ : AlgebraicGeometry.IsReduced Gr.left := Scheme.reductionOver_isReduced G
  let _ : IsLocallyNoetherian Gr.left :=
    LocallyOfFiniteType.isLocallyNoetherian Gr.hom
  let _ : Flat Gr.hom := by infer_instance
  let _ : GeometricallyReduced Gr.hom :=
    GeometricallyReduced.of_isReduced_of_perfectField Gr.hom
  let _ : AlgebraicGeometry.IsReduced ((Gr ⊗ Gr).left) := by
    change AlgebraicGeometry.IsReduced (pullback Gr.hom Gr.hom)
    infer_instance
  let _ : GrpObj (Over.mk Gr.hom) := Scheme.reductionOverGrpObj G
  let _ : Smooth Gr.hom := smooth_of_grpObj Gr.hom
  let I : X.IdealSheafData := X.nilradical
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let J : Ideal Γ(X, ⊤) := I.ideal U
  let m : Spec (.of (Γ(X, ⊤) ⧸ J)) ⟶ Gr.left := I.subschemeCover.f U
  let _ : IsOpenImmersion m := I.subschemeCover.map_prop U
  have hmRange : m.opensRange = ⊤ := by
    let _ : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    have h : (I.subschemeCover.f U).opensRange = (⊤ : I.subscheme.Opens) := by
      simp [U]
    exact h
  let _ : IsIso m := isIso_of_isOpenImmersion_of_opensRange_eq_top m hmRange
  have hmSmooth : Smooth (m ≫ Gr.hom) := inferInstance
  let E : Γ(X, ⊤) ≃+* H :=
    (Scheme.ΓSpecIso (.of H)).commRingCatIsoToRingEquiv
  have hJ : nilradical H = J.map E.toRingHom := by
    change nilradical H = (nilradical Γ(X, ⊤)).map E.toRingHom
    exact nilradical_eq_map_ringEquiv E
  let Q : (Γ(X, ⊤) ⧸ J) ≃+* (H ⧸ nilradical H) :=
    Ideal.quotientEquiv J (nilradical H) E hJ
  let l : K →+* (Γ(X, ⊤) ⧸ J) :=
    (Ideal.Quotient.mk J).comp (E.symm.toRingHom.comp (algebraMap K H))
  have hmι : m ≫ Scheme.reductionι.app G.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        (isAffineOpen_top X).fromSpec :=
    (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  have hmfac : m ≫ Gr.hom = Spec.map (CommRingCat.ofHom l) := by
    change m ≫ (Scheme.reductionι.app G.left ≫ G.hom) = _
    rw [← Category.assoc, hmι]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
      (isAffineOpen_top X).fromSpec) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K H)) = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [hmfac] at hmSmooth
  have hl : l.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hmSmooth
  have hQ : Q.toRingHom.Smooth := RingHom.Smooth.of_bijective Q.bijective
  have hmap : Q.toRingHom.comp l = algebraMap K (H ⧸ nilradical H) := by
    ext k
    exact (Ideal.quotientEquiv_mk J (nilradical H) E hJ
      (E.symm (algebraMap K H k))).trans
        (congrArg (Ideal.Quotient.mk (nilradical H))
          (E.apply_symm_apply (algebraMap K H k)))
  apply RingHom.smooth_algebraMap.mp
  rw [← hmap]
  exact hl.comp hQ

/-- The reduced quotient of a finite-type commutative Hopf algebra over a perfect field
is smooth for the algebra structure induced by its original coefficient map.
The proof uses the reduced subgroup construction of Milne, *Algebraic Groups*,
Corollary 1.39, followed by smoothness of geometrically reduced group schemes.
No reducedness of the Hopf algebra itself is assumed. -/
theorem smooth_quotient_nilradical
    (K : Type u) (H : Type v) [Field K] [PerfectField K] [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] :
    Algebra.Smooth K (H ⧸ nilradical H) := by
  let K' : Type (max u v) := ULift.{v} K
  let H' : Type (max u v) := ULift.{u} H
  let D : K' ≃+* K := ULift.ringEquiv
  let E : H' ≃+* H := ULift.ringEquiv
  let _ : HopfAlgebra K' H' := HopfAlgebra.ulift K H
  let _ : PerfectField K' := PerfectField.of_ringEquiv D.symm
  have hft : (algebraMap K' H').FiniteType := by
    have hmap : algebraMap K' H' =
        E.symm.toRingHom.comp ((algebraMap K H).comp D.toRingHom) := by
      ext k
      rfl
    rw [hmap]
    exact (RingHom.FiniteType.of_surjective E.symm.toRingHom E.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType K H)).comp
          (RingHom.FiniteType.of_surjective D.toRingHom D.surjective))
  let _ : Algebra.FiniteType K' H' := RingHom.finiteType_algebraMap.mp hft
  have hs : Algebra.Smooth K' (H' ⧸ nilradical H') :=
    smooth_quotient_nilradical_aux K' H'
  have hl : (algebraMap K' (H' ⧸ nilradical H')).Smooth :=
    RingHom.smooth_algebraMap.mpr hs
  let Q : (H' ⧸ nilradical H') ≃+* (H ⧸ nilradical H) :=
    Ideal.quotientEquiv (nilradical H') (nilradical H) E
      (nilradical_eq_map_ringEquiv E)
  have hD : D.symm.toRingHom.Smooth := RingHom.Smooth.of_bijective D.symm.bijective
  have hQ : Q.toRingHom.Smooth := RingHom.Smooth.of_bijective Q.bijective
  have hmap : Q.toRingHom.comp
      ((algebraMap K' (H' ⧸ nilradical H')).comp D.symm.toRingHom) =
      algebraMap K (H ⧸ nilradical H) := by
    ext k
    exact (Ideal.quotientEquiv_mk (nilradical H') (nilradical H) E
      (nilradical_eq_map_ringEquiv E) (algebraMap K' H' (D.symm k))).trans (by rfl)
  apply RingHom.smooth_algebraMap.mp
  rw [← hmap]
  exact (hD.comp hl).comp hQ

/-- A reduced finite-type commutative Hopf algebra over a perfect field is smooth
for its original algebra structure. -/
theorem smooth_of_isReduced
    (K : Type u) (A : Type v) [Field K] [PerfectField K] [CommRing A]
    [HopfAlgebra K A] [Algebra.FiniteType K A] [IsReduced A] :
    Algebra.Smooth K A := by
  let _ : Algebra.Smooth K (A ⧸ nilradical A) := smooth_quotient_nilradical K A
  let e : (A ⧸ nilradical A) ≃ₐ[K] (A ⧸ (⊥ : Ideal A)) :=
    Ideal.quotientEquivAlgOfEq K (_root_.nilradical_eq_zero A)
  exact Algebra.Smooth.of_equiv (e.trans (AlgEquiv.quotientBot K A))

/-- A geometrically reduced finite-type commutative Hopf algebra over a field is smooth
for its original algebra structure. -/
theorem smooth_of_isGeometricallyReduced
    (K : Type u) (A : Type v) [Field K] [CommRing A] [HopfAlgebra K A]
    [Algebra.FiniteType K A] [Algebra.IsGeometricallyReduced K A] :
    Algebra.Smooth K A := by
  let Ω := AlgebraicClosure K
  let _ : IsReduced (TensorProduct K Ω A) :=
    (Algebra.isGeometricallyReduced_field_iff K A).mp inferInstance
  let _ : Algebra.Smooth Ω (TensorProduct K Ω A) :=
    smooth_of_isReduced Ω (TensorProduct K Ω A)
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω

end HopfAlgebra
