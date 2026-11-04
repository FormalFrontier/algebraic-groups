/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.ULift
public import AlgebraicGroups.GroupScheme.AffineHomOver
public import AlgebraicGroups.GroupScheme.FaithfullyFlatCoordinates
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness over reduced Hopf algebras

An injective morphism of finite-type commutative Hopf algebras over a field is
faithfully flat if its source coordinate algebra is reduced. The corresponding
morphism of affine group schemes has reduced target. This is the reduced-target,
finite-type coordinate-algebra consequence of Milne, *Algebraic Groups*, 1.70.

The proof uses the Hopf spectrum functor and the faithfully flat coordinate
criterion for affine group schemes. Canonical universe lifts put the spectra in
one universe; the coordinate criterion is applied to the original rings and to
the algebra structure induced by the given ring homomorphism. No geometric
reducedness or reducedness of the other coordinate algebra is required.

## References

- J. S. Milne, *Algebraic Groups* (2017), 1.69–1.70.
-/

@[expose] public section

noncomputable section

universe u v w

namespace BialgHom

open AlgebraicGeometry hiding IsReduced
open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

/-- An injective morphism between finite-type commutative Hopf algebras over a field
is faithfully flat when its source coordinate algebra is reduced. The underlying
ring map is the supplied bialgebra morphism, in independent universes. This is the
coordinate-algebra consequence of Milne, *Algebraic Groups*, 1.70 for reduced
targets. -/
theorem faithfullyFlat_of_injective_of_isReduced
    {K : Type u} [Field K]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [HopfAlgebra K A] [HopfAlgebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    [IsReduced A]
    (f : A →ₐc[K] B) (hinj : Function.Injective f) :
    f.toAlgHom.toRingHom.FaithfullyFlat := by
  let K' := ULift.{max v w} K
  let A' := ULift.{max u w} A
  let B' := ULift.{max u v} B
  let dK : K' ≃+* K := ULift.ringEquiv
  let dA : A' ≃+* A := ULift.ringEquiv
  let dB : B' ≃+* B := ULift.ringEquiv
  let : HopfAlgebra K' A' := HopfAlgebra.ulift K A
  let : HopfAlgebra K' B' := HopfAlgebra.ulift K B
  let f' : A' →ₐc[K'] B' := f.ulift
  have hf' (a : A') : (f' a).down = f a.down := by
    -- The scalar lift is invisible after coercing the bialgebra map to a function.
    exact BialgHom.down_ulift_apply.{u, v, w, max u w, max v w, max u v} f a
  have hcoefA : algebraMap K' A' =
      dA.symm.toRingHom.comp ((algebraMap K A).comp dK.toRingHom) := by
    change @algebraMap K' A' _ _ (HopfAlgebra.ulift K A).toBialgebra.toAlgebra = _
    rw [HopfAlgebra.ulift_toAlgebra]
    rfl
  have hcoefB : algebraMap K' B' =
      dB.symm.toRingHom.comp ((algebraMap K B).comp dK.toRingHom) := by
    change @algebraMap K' B' _ _ (HopfAlgebra.ulift K B).toBialgebra.toAlgebra = _
    rw [HopfAlgebra.ulift_toAlgebra]
    rfl
  have : Algebra.FiniteType K' A' := by
    apply RingHom.finiteType_algebraMap.mp
    rw [hcoefA]
    exact (RingHom.FiniteType.of_surjective _ dA.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType K A)).comp
        (RingHom.FiniteType.of_surjective _ dK.surjective))
  have : Algebra.FiniteType K' B' := by
    apply RingHom.finiteType_algebraMap.mp
    rw [hcoefB]
    exact (RingHom.FiniteType.of_surjective _ dB.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType K B)).comp
        (RingHom.FiniteType.of_surjective _ dK.surjective))
  have : IsReduced A' := isReduced_of_injective dA dA.injective
  let R : CommRingCat.{max u v w} := .of K'
  let GA := (hopfSpec R).obj (op (CommHopfAlgCat.of K' A'))
  let GB := (hopfSpec R).obj (op (CommHopfAlgCat.of K' B'))
  let XA : Over (Spec R) := GA.X
  let XB : Over (Spec R) := GB.X
  let : GrpObj XA := inferInstance
  let : GrpObj XB := inferInstance
  let ψ : GB ⟶ GA := (hopfSpec R).map (CommHopfAlgCat.ofHom f').op
  let φ : XB ⟶ XA := ψ.hom.hom
  have : IsMonHom φ := inferInstance
  have hleft : φ.left = Spec.map (CommRingCat.ofHom f'.toAlgHom.toRingHom) := by
    change ((algSpec R).map (CommAlgCat.ofHom f'.toAlgHom).op).left = _
    rw [algSpec_map_left]
    rfl
  have hXA : XA.hom = Spec.map (CommRingCat.ofHom (algebraMap K' A')) := by
    change ((algSpec R).obj (op (CommAlgCat.of K' A'))).hom = _
    exact algSpec_obj_hom (R := R) (op (CommAlgCat.of K' A'))
  have hXB : XB.hom = Spec.map (CommRingCat.ofHom (algebraMap K' B')) := by
    change ((algSpec R).obj (op (CommAlgCat.of K' B'))).hom = _
    exact algSpec_obj_hom (R := R) (op (CommAlgCat.of K' B'))
  have : IsAffine XA.left := by
    change IsAffine (Spec (.of A'))
    infer_instance
  have : IsAffine XB.left := by
    change IsAffine (Spec (.of B'))
    infer_instance
  have : LocallyOfFiniteType XA.hom := by
    rw [hXA]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType XB.hom := by
    rw [hXB]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : AlgebraicGeometry.IsReduced XA.left := by
    change AlgebraicGeometry.IsReduced (Spec (.of A'))
    exact (affine_isReduced_iff (.of A')).mpr inferInstance
  let aA : A' →ₐ[K'] ((algΓ R).obj XA).unop :=
    affineSpecHomOverEquiv K' XA A' (𝟙 XA)
  let aB : B' →ₐ[K'] ((algΓ R).obj XB).unop :=
    affineSpecHomOverEquiv K' XB B' (𝟙 XB)
  have haA : aA.toRingHom = (Scheme.ΓSpecIso (.of A')).inv.hom := by
    ext a
    have h := congrArg (fun q => CommRingCat.Hom.hom q a)
      (affineSpecHomOverEquiv_apply_toRingHom K' XA A' (𝟙 XA))
    simp only [CommRingCat.hom_ofHom] at h
    change aA a = (Scheme.Hom.appTop (𝟙 XA.left)).hom
      ((Scheme.ΓSpecIso (.of A')).inv.hom a) at h
    rw [Scheme.Hom.id_appTop] at h
    exact h
  have haB : aB.toRingHom = (Scheme.ΓSpecIso (.of B')).inv.hom := by
    ext b
    have h := congrArg (fun q => CommRingCat.Hom.hom q b)
      (affineSpecHomOverEquiv_apply_toRingHom K' XB B' (𝟙 XB))
    simp only [CommRingCat.hom_ofHom] at h
    change aB b = (Scheme.Hom.appTop (𝟙 XB.left)).hom
      ((Scheme.ΓSpecIso (.of B')).inv.hom b) at h
    rw [Scheme.Hom.id_appTop] at h
    exact h
  -- Keep the naturality square bundled until its source and target ring maps agree.
  have hΓ : (Scheme.ΓSpecIso (.of B')).inv.hom.comp f'.toAlgHom.toRingHom =
      (Spec.map (CommRingCat.ofHom f'.toAlgHom.toRingHom)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of A')).inv.hom := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f'.toAlgHom.toRingHom))
  have hφ' : aB.toRingHom.comp f'.toAlgHom.toRingHom =
      φ.left.appTop.hom.comp aA.toRingHom := by
    rw [haA, haB, hleft]
    exact hΓ
  let eA' : A' ≃ₐ[K'] ((algΓ R).obj XA).unop := AlgEquiv.ofBijective aA (by
    change Function.Bijective (aA.toRingHom : A' → Γ(XA.left, ⊤))
    rw [haA]
    exact (Scheme.ΓSpecIso (.of A')).symm.commRingCatIsoToRingEquiv.bijective)
  let eB' : B' ≃ₐ[K'] ((algΓ R).obj XB).unop := AlgEquiv.ofBijective aB (by
    change Function.Bijective (aB.toRingHom : B' → Γ(XB.left, ⊤))
    rw [haB]
    exact (Scheme.ΓSpecIso (.of B')).symm.commRingCatIsoToRingEquiv.bijective)
  let : Algebra K' A := ULift.algebra' K A
  let : Algebra K' B := ULift.algebra' K B
  let uA : A ≃ₐ[K'] A' := AlgEquiv.ofRingEquiv (f := dA.symm) (by
    intro k
    change ULift.up (algebraMap K A k.down) = algebraMap K' A' k
    rw [hcoefA]
    rfl)
  let uB : B ≃ₐ[K'] B' := AlgEquiv.ofRingEquiv (f := dB.symm) (by
    intro k
    change ULift.up (algebraMap K B k.down) = algebraMap K' B' k
    rw [hcoefB]
    rfl)
  let eA : A ≃ₐ[K'] ((algΓ R).obj XA).unop := uA.trans eA'
  let eB : B ≃ₐ[K'] ((algΓ R).obj XB).unop := uB.trans eB'
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  have hφ : eB.toRingHom.comp (algebraMap A B) =
      φ.left.appTop.hom.comp eA.toRingHom := by
    ext a
    have hu : f'.toAlgHom.toRingHom (uA a) = uB (f a) := by
      apply dB.injective
      exact hf' (uA a)
    change aB (uB (f a)) = φ.left.appTop.hom (aA (uA a))
    rw [← hu]
    exact DFunLike.congr_fun hφ' (uA a)
  let gA : GrpObj (Over.mk XA.hom) := by
    change GrpObj XA
    infer_instance
  let gB : GrpObj (Over.mk XB.hom) := by
    change GrpObj XB
    infer_instance
  have hff : Module.FaithfullyFlat A B :=
    faithfullyFlat_of_injective_group_coordinate_map XB.hom XA.hom φ eA eB hφ
      (show Function.Injective (algebraMap A B) from hinj)
  exact (RingHom.faithfullyFlat_algebraMap_iff.mpr hff :
    (algebraMap A B).FaithfullyFlat)

end BialgHom
