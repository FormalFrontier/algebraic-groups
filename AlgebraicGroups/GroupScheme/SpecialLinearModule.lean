/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearModule
public import AlgebraicGroups.GroupScheme.SpecialLinear
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Special linear groups of finite-free modules

The determinant-one automorphisms of the scalar extension of a finite-free module
form a group-valued functor. Its coefficient maps combine Mathlib's special
linear base change with tensor reassociation and the general linear module
functor. A chosen finite basis identifies it naturally with matrix special
linear groups and their represented affine points over every commutative
coefficient algebra. No basis-independent representing scheme is constructed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8, p. 41: the
  special linear groups mentioned alongside finite-dimensional `GL(V)` over
  a field; the general-base coefficient and basis coherence here use the
  formalizations below, not a proof in that brief passage.
* Mathlib, `LinearAlgebra/SpecialLinearGroup`: Antoine Chambert-Loir's
  `SpecialLinearGroup.baseChange`, `congr_linearEquiv`, and
  `Matrix.SpecialLinearGroup.toLin_equiv` for determinant-one automorphisms.
* Mathlib, `LinearAlgebra/TensorProduct/Tower` and
  `RingTheory/TensorProduct/Free`: tensor cancellation and scalar-extended bases.
* `AlgebraicGroups.Algebra.GeneralLinearBaseChange` and
  `AlgebraicGroups.GroupScheme.GeneralLinearModule` supply the comparison with
  GL under coefficient and basis change; `AlgebraicGroups.GroupScheme.SpecialLinear`
  supplies the matrix special linear scheme and its point inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing SpecialLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Canonical extension of determinant-one automorphisms along a coefficient map. -/
def specialLinearModuleBaseChange (R S : Type u) [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (g : R →ₐ[K] S) :
    SpecialLinearGroup R (SourceOrderTensor K V R) →*
      SpecialLinearGroup S (SourceOrderTensor K V S) := by
  letI : Algebra R S := g.toRingHom.toAlgebra
  exact (SpecialLinearGroup.congr_linearEquiv
    (AlgebraTensorModule.cancelBaseChange K R S S V)).toMonoidHom.comp
    (SpecialLinearGroup.baseChange (R := R) (S := S)
      (V := SourceOrderTensor K V R))

/-- Scalar extension of SL agrees with general-linear scalar extension after inclusion. -/
theorem specialLinearModuleBaseChange_toGL (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    (specialLinearModuleBaseChange K V R S g f).toGeneralLinearGroup =
      generalLinearModuleBaseChange K V R S g f.toGeneralLinearGroup := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem specialLinearModuleBaseChange_id (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleBaseChange K V R R (AlgHom.id K R) f = f := by
  apply SpecialLinearGroup.toGeneralLinearGroup_injective
  rw [specialLinearModuleBaseChange_toGL, generalLinearModuleBaseChange_id]

@[simp] theorem specialLinearModuleBaseChange_comp
    (R S T : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    [CommRing T] [Algebra K T] (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleBaseChange K V S T h
        (specialLinearModuleBaseChange K V R S g f) =
      specialLinearModuleBaseChange K V R T (h.comp g) f := by
  apply SpecialLinearGroup.toGeneralLinearGroup_injective
  rw [specialLinearModuleBaseChange_toGL, specialLinearModuleBaseChange_toGL,
    specialLinearModuleBaseChange_toGL, generalLinearModuleBaseChange_comp]

/-- Determinant-one automorphisms, functorial under scalar extension. -/
def specialLinearModuleFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (SpecialLinearGroup R (SourceOrderTensor K V R))
  map g := GrpCat.ofHom (specialLinearModuleBaseChange K V _ _ g.hom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact specialLinearModuleBaseChange_id K V R f
  map_comp g h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact (specialLinearModuleBaseChange_comp K V _ _ _ g.hom h.hom f).symm

/-- Inclusion of determinant-one automorphisms is natural into the GL functor. -/
def specialLinearModuleInclusion :
    specialLinearModuleFunctor K V ⟶ generalLinearModuleFunctor K V where
  app R := GrpCat.ofHom (SpecialLinearGroup.toGeneralLinearGroup)
  naturality := by
    intro R S g
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact (specialLinearModuleBaseChange_toGL K V R S g.hom f).symm

theorem specialLinearModuleBaseChange_tmul (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R))
    (s : S) (v : V) :
    (specialLinearModuleBaseChange K V R S g f) (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] v)) := by
  exact generalLinearModuleBaseChange_tmul K V R S g f.toGeneralLinearGroup s v

variable (indexType : Type u) [Fintype indexType] [DecidableEq indexType]
  (basis : Module.Basis indexType K V)

/-- The chosen-basis comparison uses Chambert-Loir's Mathlib
`Matrix.SpecialLinearGroup.toLin_equiv`; compare the SL groups in Milne,
*Algebraic Groups*, item 2.8, in the field case. -/
def specialLinearModuleMatrixEquiv (R : Type u) [CommRing R] [Algebra K R] :
    SpecialLinearGroup R (SourceOrderTensor K V R) ≃*
      Matrix.SpecialLinearGroup indexType R :=
  (Matrix.SpecialLinearGroup.toLin_equiv
    (generalLinearScalarBasis K V indexType basis R)).symm

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleMatrixEquiv_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) (row column : indexType) :
    specialLinearModuleMatrixEquiv K V indexType basis R f row column =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  exact Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq
    (generalLinearScalarBasis K V indexType basis R) f ▸
      LinearMap.toMatrix_apply _ _ _ _ _

omit [Module.Free K V] [Module.Finite K V] in
/-- Matrix SL followed by GL agrees with the chosen-basis GL comparison. -/
theorem specialLinearModuleMatrixEquiv_toGL (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    Matrix.SpecialLinearGroup.toGL
        (specialLinearModuleMatrixEquiv K V indexType basis R f) =
      generalLinearModuleMatrixEquiv K V indexType basis R f.toGeneralLinearGroup := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  rfl

/-- Finite-basis SL coordinates commute with canonical coefficient change. -/
theorem specialLinearModuleMatrixEquiv_natural (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleMatrixEquiv K V indexType basis S
        (specialLinearModuleBaseChange K V R S g f) =
      Matrix.SpecialLinearGroup.map g.toRingHom
        (specialLinearModuleMatrixEquiv K V indexType basis R f) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearModuleMatrixEquiv_toGL,
    specialLinearModuleBaseChange_toGL,
    generalLinearModuleMatrixEquiv_natural]
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  rfl

omit [Module.Free K V] [Module.Finite K V] in
/-- Matrix coordinates describe the action of the original automorphism. -/
theorem specialLinearModuleMatrixEquiv_action (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R))
    (x : SourceOrderTensor K V R) :
    (specialLinearModuleMatrixEquiv K V indexType basis R f : Matrix indexType indexType R) *ᵥ
        (generalLinearScalarBasis K V indexType basis R).repr x =
      (generalLinearScalarBasis K V indexType basis R).repr (f x) := by
  change (generalLinearModuleMatrixEquiv K V indexType basis R f.toGeneralLinearGroup).val *ᵥ
    (generalLinearScalarBasis K V indexType basis R).repr x = _
  exact generalLinearModuleMatrixEquiv_action K V indexType basis R f.toGeneralLinearGroup x

/-- A chosen finite basis gives a natural isomorphism of determinant-one
automorphism groups with matrix SL, extending the field setting of Milne,
*Algebraic Groups*, item 2.8. -/
def specialLinearModuleMatrixIso :
    specialLinearModuleFunctor K V ≅ specialLinearGroupFunctor K indexType :=
  NatIso.ofComponents
    (fun R ↦ (specialLinearModuleMatrixEquiv K V indexType basis R).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      exact specialLinearModuleMatrixEquiv_natural K V indexType basis R S g.hom f)

/-- Chosen-basis representation by the finite matrix SL affine group scheme,
using `specialLinearGroupPointsIso`. -/
def specialLinearModulePointsIso :
    specialLinearModuleFunctor K V ≅ specialLinearGroupPointsFunctor K indexType :=
  (specialLinearModuleMatrixIso K V indexType basis) ≪≫
    specialLinearGroupPointsIso K indexType

/-- Evaluation of SL coordinate functions on a finite-free module automorphism. -/
def specialLinearModuleCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    SpecialLinearCoordinateRing.CoordinateRing K indexType →ₐ[K] R :=
  specialLinearFromSL K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f)

theorem specialLinearModuleCoordinateEval_natural (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleCoordinateEval K V indexType basis S
        (specialLinearModuleBaseChange K V R S g f) =
      g.comp (specialLinearModuleCoordinateEval K V indexType basis R f) := by
  rw [specialLinearModuleCoordinateEval, specialLinearModuleMatrixEquiv_natural,
    specialLinearFromSL_natural]
  rfl

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleCoordinateEval_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) (row column : indexType) :
    specialLinearModuleCoordinateEval K V indexType basis R f
        (entry K indexType row column) =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  change (specialLinearGroupMulEquivAlgHom K indexType R
      (specialLinearModuleMatrixEquiv K V indexType basis R f)).ofConv
        (entry K indexType row column) = _
  exact (specialLinearGroupMulEquivAlgHom_entry K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f) row column).trans
      (specialLinearModuleMatrixEquiv_entry K V indexType basis R f row column)

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleCoordinateEval_detInverse (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleCoordinateEval K V indexType basis R f
      (quotient K indexType (detInverse K indexType)) = 1 :=
  specialLinearGroupMulEquivAlgHom_detInverse K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f)

/-- The underlying morphism of the represented `Spec R` point. -/
theorem specialLinearModulePointsIso_apply_left (R : CommAlgCat K)
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    ((specialLinearModulePointsIso K V indexType basis).hom.app R f).left =
      Spec.map (CommRingCat.ofHom
        (specialLinearModuleCoordinateEval K V indexType basis R f).toRingHom) := rfl

/-- Pull back a universal matrix entry along the represented `Spec` point. -/
theorem specialLinearModulePoint_preimage_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) (row column : indexType) :
    (Spec.preimage
      ((specialLinearModulePointsIso K V indexType basis).hom.app (CommAlgCat.of K R) f).left).hom
        (entry K indexType row column) =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  change (Spec.preimage (specialLinearGroupMulEquivPoints K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
      (entry K indexType row column) = _
  exact (specialLinearGroupPoint_preimage_entry K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f) row column).trans
      (specialLinearModuleMatrixEquiv_entry K V indexType basis R f row column)

/-- The inverse-determinant coordinate evaluates to one at every SL point. -/
theorem specialLinearModulePoint_preimage_detInverse (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    (Spec.preimage
      ((specialLinearModulePointsIso K V indexType basis).hom.app (CommAlgCat.of K R) f).left).hom
        (quotient K indexType (detInverse K indexType)) = 1 := by
  change (Spec.preimage (specialLinearGroupMulEquivPoints K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f)).left).hom
      (quotient K indexType (detInverse K indexType)) = 1
  exact specialLinearGroupPoint_preimage_detInverse K indexType R
    (specialLinearModuleMatrixEquiv K V indexType basis R f)

/-- The SL-to-GL inclusion agrees with the matrix-scheme inclusion on points. -/
theorem specialLinearModulePointsIso_inclusion (R : CommAlgCat K)
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    (specialLinearModulePointsIso K V indexType basis).hom.app R f ≫
        (specialLinearInclusion K indexType).hom.hom =
      (generalLinearModulePointsIso K V indexType basis).hom.app R
        f.toGeneralLinearGroup := by
  change specialLinearGroupMulEquivPoints K indexType R
      (specialLinearModuleMatrixEquiv K V indexType basis R f) ≫
        (specialLinearInclusion K indexType).hom.hom =
    generalLinearGroupMulEquivPoints K indexType R
      (generalLinearModuleMatrixEquiv K V indexType basis R f.toGeneralLinearGroup)
  rw [specialLinearInclusion_point,
    specialLinearModuleMatrixEquiv_toGL]

variable (otherBasis thirdBasis : Module.Basis indexType K V)

/-- Changing chosen bases transports the same automorphism without altering it. -/
def specialLinearModuleChangeBasis (R : Type u) [CommRing R] [Algebra K R] :
    Matrix.SpecialLinearGroup indexType R ≃* Matrix.SpecialLinearGroup indexType R :=
  (specialLinearModuleMatrixEquiv K V indexType basis R).symm.trans
    (specialLinearModuleMatrixEquiv K V indexType otherBasis R)

omit [Module.Free K V] [Module.Finite K V] in
@[simp] theorem specialLinearModuleChangeBasis_apply (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleChangeBasis K V indexType basis otherBasis R
        (specialLinearModuleMatrixEquiv K V indexType basis R f) =
      specialLinearModuleMatrixEquiv K V indexType otherBasis R f := by
  simp [specialLinearModuleChangeBasis]

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleChangeBasis_id (R : Type u) [CommRing R] [Algebra K R] :
    specialLinearModuleChangeBasis K V indexType basis basis R = MulEquiv.refl _ := by
  ext f
  simp [specialLinearModuleChangeBasis]

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleChangeBasis_comp (R : Type u) [CommRing R] [Algebra K R] :
    (specialLinearModuleChangeBasis K V indexType basis otherBasis R).trans
        (specialLinearModuleChangeBasis K V indexType otherBasis thirdBasis R) =
      specialLinearModuleChangeBasis K V indexType basis thirdBasis R := by
  ext f
  simp [specialLinearModuleChangeBasis]

/-- The chosen-basis change commutes with coefficient homomorphisms. -/
theorem specialLinearModuleChangeBasis_natural (R S : Type u)
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Matrix.SpecialLinearGroup indexType R) :
    specialLinearModuleChangeBasis K V indexType basis otherBasis S
        (Matrix.SpecialLinearGroup.map g.toRingHom f) =
      Matrix.SpecialLinearGroup.map g.toRingHom
        (specialLinearModuleChangeBasis K V indexType basis otherBasis R f) := by
  obtain ⟨h, rfl⟩ := (specialLinearModuleMatrixEquiv K V indexType basis R).surjective f
  rw [← specialLinearModuleMatrixEquiv_natural K V indexType basis R S g h]
  simp only [specialLinearModuleChangeBasis_apply]
  exact specialLinearModuleMatrixEquiv_natural K V indexType otherBasis R S g h

omit [Module.Free K V] [Module.Finite K V] in
/-- SL change-of-basis is the restriction of the established GL comparison. -/
theorem specialLinearModuleChangeBasis_toGL (R : Type u)
    [CommRing R] [Algebra K R] (f : Matrix.SpecialLinearGroup indexType R) :
    Matrix.SpecialLinearGroup.toGL
        (specialLinearModuleChangeBasis K V indexType basis otherBasis R f) =
      generalLinearModuleChangeBasis K V indexType basis otherBasis R
        (Matrix.SpecialLinearGroup.toGL f) := by
  obtain ⟨h, rfl⟩ := (specialLinearModuleMatrixEquiv K V indexType basis R).surjective f
  rw [specialLinearModuleChangeBasis_apply,
    specialLinearModuleMatrixEquiv_toGL,
    specialLinearModuleMatrixEquiv_toGL]
  exact (generalLinearModuleChangeBasis_apply K V indexType basis otherBasis R
    h.toGeneralLinearGroup).symm

/-- Natural isomorphism between two matrix SL presentations of the same module. -/
def specialLinearModuleChangeBasisIso :
    specialLinearGroupFunctor K indexType ≅ specialLinearGroupFunctor K indexType :=
  (specialLinearModuleMatrixIso K V indexType basis).symm ≪≫
    specialLinearModuleMatrixIso K V indexType otherBasis

/-- The two represented points differ only by their choice of coordinates. -/
theorem specialLinearModulePointsIso_changeBasis (R : CommAlgCat K)
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    (specialLinearModulePointsIso K V indexType otherBasis).hom.app R f =
      (specialLinearGroupPointsIso K indexType).hom.app R
        (specialLinearModuleChangeBasis K V indexType basis otherBasis R
          (specialLinearModuleMatrixEquiv K V indexType basis R f)) := by
  rw [specialLinearModuleChangeBasis_apply]
  rfl

omit [Module.Free K V] [Module.Finite K V] in
/-- The changed matrix acts by the same automorphism in the new coordinates. -/
theorem specialLinearModuleChangeBasis_action (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R))
    (x : SourceOrderTensor K V R) :
    (specialLinearModuleChangeBasis K V indexType basis otherBasis R
        (specialLinearModuleMatrixEquiv K V indexType basis R f) :
          Matrix indexType indexType R) *ᵥ
        (generalLinearScalarBasis K V indexType otherBasis R).repr x =
      (generalLinearScalarBasis K V indexType otherBasis R).repr (f x) := by
  rw [specialLinearModuleChangeBasis_apply]
  exact specialLinearModuleMatrixEquiv_action K V indexType otherBasis R f x

end AlgebraicGeometry

#lint
