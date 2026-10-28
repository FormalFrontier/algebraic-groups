/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange

/-!
# Integral finite general and special linear schemes

The genuine coordinate algebras of finite `GL` and `SL` are domains over integral
base rings. Over any commutative base their structure maps have integral fibers
after extension to every field, so both morphisms are geometrically integral.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8 for the field-base determinant
  localization of `GL`, and §2.42 for the field-base domain argument for `SL`.
  The assertions here also concern integral-base coordinate rings and
  relative geometric integrality over arbitrary bases.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), XIII §3,
  item 3.14: a right-diagonal determinant splitting for positive rank.
  The algebra section used here instead comes from left normalization; it is
  not an assertion that arbitrary injections survive tensor products.
* Mathlib, `RingTheory/Localization/Away/Basic`,
  `RingTheory/Localization/BaseChange`, `RingTheory/TensorProduct/MvPolynomial`,
  `AlgebraicGeometry/Geometrically/Integral` and
  `AlgebraicGeometry/Pullbacks`: localization domains, tensor equivalences,
  geometric-fiber criteria and affine pullbacks. Compatibility of the generic
  determinant with coefficient maps is checked explicitly below.
-/

@[expose] public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TauCeti.GeneralLinear SpecialLinearCoordinateRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n]

private def emptySpecialLinearEquiv [IsEmpty n] :
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) ≃ₐ[K]
      (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) := by
  classical
  have determinant_one : (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det = 1 :=
    Matrix.det_isEmpty
  have ideal_bot : (TauCeti.SpecialLinear.definingHopfIdeal K (Fintype.card n)).toIdeal = ⊥ := by
    rw [TauCeti.SpecialLinear.definingHopfIdeal_toIdeal,
      ← generalLinearReindexedGenericMatrix_det K n, determinant_one]
    simp
  exact (AlgEquiv.quotientBot K ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card
    n)))).symm.trans
    (Ideal.quotientEquivAlgOfEq K ideal_bot.symm)

private theorem emptySpecialLinearEquiv_quotient [IsEmpty n] :
    (emptySpecialLinearEquiv K n).toAlgHom = (TauCeti.SpecialLinear.coordinateMap K (Fintype.card
      n)).hom.toAlgHom := by
  ext x
  erw [TauCeti.SpecialLinear.coordinateMap_apply]

private def specialLinearSection :
    (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) →ₐ[K]
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) := by
  classical
  exact if nonemptyIndex : Nonempty n then
    specialLinearNormalizationSection K n (Classical.choice nonemptyIndex)
  else
    letI : IsEmpty n := ⟨fun index => nonemptyIndex ⟨index⟩⟩
    (emptySpecialLinearEquiv K n).symm.toAlgHom

private theorem specialLinearSection_split :
    ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom).comp
      (specialLinearSection K n) =
      AlgHom.id K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := by
  classical
  unfold specialLinearSection
  split_ifs with nonemptyIndex
  · exact specialLinearNormalizationSection_comp_quotient K n _
  · let : IsEmpty n := ⟨fun index => nonemptyIndex ⟨index⟩⟩
    rw [← emptySpecialLinearEquiv_quotient K n]
    exact AlgEquiv.comp_symm (emptySpecialLinearEquiv K n)

/-- The actual determinant-one coordinate ring is a domain over every integral base,
including in rank zero. Compare the positive-rank field-base result in Milne,
*Algebraic Groups*, §2.42: here the algebra section into the GL domain is
injective, while rank zero uses the quotient-bottom equivalence. -/
instance specialLinearCoordinateRing_isDomain [IsDomain K] :
    IsDomain ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := by
  have hleft : Function.LeftInverse
      (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom
      (specialLinearSection K n) := by
    intro x
    exact AlgHom.congr_fun (specialLinearSection_split K n) x
  exact hleft.injective.isDomain (specialLinearSection K n)

/-- The total space of finite `GL` is integral over any integral base, using
mathlib's integral-affine-Spec instance for the GL coordinate domain. -/
instance generalLinearGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).left := by
  change IsIntegral (Spec (.of ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)))))
  infer_instance

/-- The total space of finite `SL` is integral over any integral base, using
mathlib's integral-affine-Spec instance for the SL coordinate domain. -/
instance specialLinearGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).left := by
  change IsIntegral (Spec (.of ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)))))
  infer_instance

private theorem generalLinearTensor_isDomain (F : Type u) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) := by
  let e : F ⊗[K] TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) ≃ₐ[F]
      TauCeti.GeneralLinear.coordinateHopfAlgebra F (Fintype.card n) :=
    (TauCeti.GeneralLinear.coordinateHopfAlgebraBaseChangeBialgEquiv K F
      (Fintype.card n)).toAlgEquiv
  exact e.injective.isDomain e.toRingHom

private theorem specialLinearTensor_isDomain (F : Type u) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := by
  let e : F ⊗[K] TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n) ≃ₐc[F]
      TauCeti.SpecialLinear.coordinateHopfAlgebra F (Fintype.card n) :=
    CommBialgCat.bialgEquivOfIso
      ((forget₂ (CommHopfAlgCat F) (CommBialgCat F)).mapIso
        (TauCeti.SpecialLinear.coordinateHopfAlgebraBaseChangeIso K F (Fintype.card n)))
  exact e.injective.isDomain e.toAlgEquiv.toRingHom

private theorem integral_closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral := by
  constructor
  intro X Y iso integral
  let : IsIntegral X := integral
  exact IsIntegral.of_isIso iso.hom

/-- Every geometric fiber of the genuine finite general linear structure morphism
is integral, for every finite index and every commutative base. The field
presentation follows Milne, *Algebraic Groups*, §2.8; the relative proof uses
mathlib's polynomial-tensor and localization equivalences, geometric-fiber
criterion and affine-Spec pullback isomorphism. -/
instance generalLinearGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    integral_closedUnderIsomorphisms
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  have : IsDomain (F ⊗[K] (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) :=
    generalLinearTensor_isDomain K n F
  have : IsDomain
      ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) ⊗[K] F) :=
    (Algebra.TensorProduct.comm K
      ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) F).injective.isDomain
        (Algebra.TensorProduct.comm K
          ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) F).toRingHom
  exact IsIntegral.of_isIso
    (pullbackSpecIso K ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) F).inv

/-- Every geometric fiber of the genuine finite special linear structure morphism
is integral, for every finite index and every commutative base. The field
case extends Milne, *Algebraic Groups*, §2.42; the relative proof tensors
the explicit algebra-section identity and uses mathlib's geometric-fiber
criterion and affine-Spec pullback isomorphism. -/
instance specialLinearGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    integral_closedUnderIsomorphisms
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  have : IsDomain (F ⊗[K] (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) :=
    specialLinearTensor_isDomain K n F
  have : IsDomain
      ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) ⊗[K] F) :=
    (Algebra.TensorProduct.comm K
      ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) F).injective.isDomain
        (Algebra.TensorProduct.comm K
          ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) F).toRingHom
  exact IsIntegral.of_isIso
    (pullbackSpecIso K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) F).inv

end AlgebraicGeometry
