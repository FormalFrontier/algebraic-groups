/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Chris Birkbeck, Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda

/-!
# A one-pivot section of the determinant character

For a specified matrix index `pivot`, the multiplicative group scheme embeds into the
finite general linear group scheme by placing a unit in that diagonal position and
ones in all other diagonal positions. The explicit pivot is essential: in rank zero,
the determinant is constant one and need not have a section over an arbitrary base.
The diagonal witness follows mathlib's `Matrix.GeneralLinearGroup.det_surjective`
(introduced by Whysoserioushah in a file that also credits Chris Birkbeck,
whose Apache-2.0 notice is retained above). Unlike pointwise surjectivity, the
result here is a natural, multiplicative morphism of group schemes over any
commutative base.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, XIII §3, item 3.14
  (a one-pivot field-base determinant section in a functorial product
  decomposition, with the diagonal factor on the right).
* Mathlib, `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`,
  `Matrix.GeneralLinearGroup.det_surjective` (Whysoserioushah's one-pivot
  lemma in the GL module also credited to Chris Birkbeck), and
  `Data/Matrix/Mul.lean` (diagonal multiplication identities).
  The local finite GL/multiplicative-group point comparisons and Mathlib's
  `AlgebraicGeometry/Group/Affine.lean` (`hopfSpec`) support the group-scheme
  upgrade, which requires a specified `pivot : n`.
-/

public section

noncomputable section

open CategoryTheory TauCeti.GeneralLinear
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The invertible diagonal matrix carrying a unit at the distinguished index,
following Mathlib's `Matrix.GeneralLinearGroup.det_surjective`
(Whysoserioushah). -/
@[expose] def generalLinearDiagonalUnit {R : Type u} [CommRing R] (pivot : n) (unit : Rˣ) :
    Matrix.GeneralLinearGroup n R :=
  ⟨Matrix.diagonal (fun j ↦ if j = pivot then (unit : R) else 1),
    Matrix.diagonal (fun j ↦ if j = pivot then ((unit⁻¹ : Rˣ) : R) else 1),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [Matrix.diagonal_eq_one]
      funext j
      by_cases hj : j = pivot <;> simp [hj],
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [Matrix.diagonal_eq_one]
      funext j
      by_cases hj : j = pivot <;> simp [hj]⟩

@[simp] theorem generalLinearDiagonalUnit_apply {R : Type u} [CommRing R]
    (pivot : n) (unit : Rˣ) (i j : n) :
    generalLinearDiagonalUnit n pivot unit i j =
      if i = j then (if i = pivot then (unit : R) else 1) else 0 := rfl

/-- A multiplicative, one-pivot diagonal section on native matrix groups. -/
def generalLinearDiagonalHom {R : Type u} [CommRing R] (pivot : n) :
    Rˣ →* Matrix.GeneralLinearGroup n R where
  toFun := generalLinearDiagonalUnit n pivot
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [generalLinearDiagonalUnit_apply, Matrix.one_apply]
  map_mul' unit other := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (Matrix.diagonal (fun k ↦ if k = pivot then ((unit * other : Rˣ) : R) else 1))
      i j = (Matrix.diagonal (fun k ↦ if k = pivot then (unit : R) else 1) *
        Matrix.diagonal (fun k ↦ if k = pivot then (other : R) else 1)) i j
    rw [Matrix.diagonal_mul_diagonal]
    by_cases hij : i = j <;> simp [hij, mul_ite, ite_mul]
    by_cases hip : j = pivot <;> simp [hip]

@[simp] theorem generalLinearDiagonalHom_apply {R : Type u} [CommRing R]
    (pivot : n) (unit : Rˣ) (i j : n) :
    generalLinearDiagonalHom n pivot unit i j =
      if i = j then (if i = pivot then (unit : R) else 1) else 0 :=
  generalLinearDiagonalUnit_apply n pivot unit i j

/-- The native unit-valued determinant of a one-pivot diagonal matrix. -/
@[simp] theorem generalLinearDiagonalHom_det {R : Type u} [CommRing R]
    (pivot : n) (unit : Rˣ) :
    Matrix.GeneralLinearGroup.det (generalLinearDiagonalHom n pivot unit) = unit := by
  apply Units.ext
  simp [generalLinearDiagonalHom, generalLinearDiagonalUnit, Matrix.det_diagonal]

/-- The diagonal construction commutes with coefficient-ring maps. -/
theorem generalLinearDiagonalHom_natural {R S : Type u} [CommRing R] [CommRing S]
    (pivot : n) (f : R →+* S) (unit : Rˣ) :
    Matrix.GeneralLinearGroup.map f (generalLinearDiagonalHom n pivot unit) =
      generalLinearDiagonalHom n pivot (Units.map f unit) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change f (generalLinearDiagonalUnit n pivot unit i j) =
    generalLinearDiagonalUnit n pivot (Units.map f unit) i j
  rw [generalLinearDiagonalUnit_apply, generalLinearDiagonalUnit_apply]
  by_cases hij : i = j
  · subst j
    by_cases hip : i = pivot <;> simp [hip]
  · simp [hij]


/-- The one-pivot diagonal section is natural in the coefficient algebra. -/
def generalLinearDeterminantSectionFunctorHom (pivot : n) :
    multiplicativeGroupFunctor K ⟶ generalLinearIndexedFunctor K n where
  app R := GrpCat.ofHom (generalLinearDiagonalHom n pivot)
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro unit
    exact (generalLinearDiagonalHom_natural n pivot f.hom.toRingHom unit).symm


/-- The diagonal section on convolution points of the canonical coordinate Hopf algebras. -/
def generalLinearDeterminantSectionPoints (A : Type u) [CommRing A] [Algebra K A]
    (pivot : n) :
    WithConv (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐ[K] A) →*
      WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A) :=
  (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n A).symm.toMonoidHom.comp
    ((generalLinearDiagonalHom n pivot).comp
      (((TauCeti.DiagonalizableGroup.pointsMulEquiv
        (R := K) (A := A) (G := ULift.{u} (Multiplicative ℤ))).trans
        (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv Aˣ).symm).toMonoidHom))

/-- The one-pivot section commutes with every coefficient-algebra map. -/
theorem generalLinearDeterminantSectionPoints_mapValue
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (pivot : n) (φ : A →ₐ[K] B)
    (q : WithConv (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐ[K] A)) :
    AlgHom.mapValue φ (generalLinearDeterminantSectionPoints K n A pivot q) =
      generalLinearDeterminantSectionPoints K n B pivot (AlgHom.mapValue φ q) := by
  apply (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n B).injective
  rw [TauCeti.GeneralLinear.reindexedPointsMulEquiv_mapValue]
  simp only [generalLinearDeterminantSectionPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [generalLinearDiagonalHom_natural]
  congr 1
  apply Units.ext
  simp only [TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe, Units.coe_map,
    AlgHom.mapValue_apply, AlgHom.comp_apply]
  rfl

/-- The diagonal section as a natural map of convolution-points functors. -/
def generalLinearDeterminantSectionPointsMap (pivot : n) :
    TauCeti.HopfAlgebra.pointsFunctor (R := K)
      (H := MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) ⟶
    TauCeti.HopfAlgebra.pointsFunctor (R := K)
      (H := TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) where
  app A := GrpCat.ofHom (generalLinearDeterminantSectionPoints K n A pivot)
  naturality A B φ := by
    ext q
    exact (generalLinearDeterminantSectionPoints_mapValue K n pivot φ.hom q).symm

/-- The coordinate Hopf morphism of the native one-pivot section. -/
def generalLinearDeterminantSectionCoordinateMap (pivot : n) :
    TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) ⟶
      CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) :=
  TauCeti.CommHopfAlgCat.homOfPointsMap
    (generalLinearDeterminantSectionPointsMap K n pivot)


/-- The recovered coordinate map acts on every convolution point as the native section. -/
theorem generalLinearDeterminantSectionCoordinateMap_points
    (A : Type u) [CommRing A] [Algebra K A] (pivot : n)
    (q : WithConv (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐ[K] A)) :
    WithConv.toConv (q.ofConv.comp
      (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom) =
        generalLinearDeterminantSectionPoints K n A pivot q := by
  have h := congrArg (fun α => α.app (CommAlgCat.of K A))
    (TauCeti.CommHopfAlgCat.mapPointsFunctor_homOfPointsMap
      (H := CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))))
      (K := TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))
      (generalLinearDeterminantSectionPointsMap K n pivot))
  have hq := congrArg (fun f => (ConcreteCategory.hom f) q) h
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hq
  exact hq

/-- The coordinate section reads a matrix entry as the corresponding diagonal monomial. -/
theorem generalLinearDeterminantSectionCoordinateMap_entry (pivot i j : n) :
    (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) =
      if i = j then (if i = pivot then
        MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1 else 1) else 0 := by
  have h := congrArg
    (fun q => q.ofConv (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j))
    (generalLinearDeterminantSectionCoordinateMap_points K n
      (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) pivot
        (WithConv.toConv (AlgHom.id K _)))
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    generalLinearDeterminantSectionPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply] at h
  rw [TauCeti.GeneralLinear.reindexedPointsMulEquiv_symm_apply,
    generalLinearDiagonalHom_apply] at h
  simpa only [TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe,
    WithConv.ofConv_toConv, AlgHom.id_apply] using h


/-- The coordinate section sends the generic determinant to the lifted standard monomial. -/
theorem generalLinearDeterminantSectionCoordinateMap_det (pivot : n) :
    (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det =
        MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1 := by
  have h := congrArg (fun q => q.ofConv
    (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det)
      (generalLinearDeterminantSectionCoordinateMap_points K n
        (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) pivot
          (WithConv.toConv (AlgHom.id K _)))
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    generalLinearDeterminantSectionPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply] at h
  rw [TauCeti.GeneralLinear.reindexedPointsMulEquiv_symm_apply_det,
    ← Matrix.GeneralLinearGroup.val_det_apply, generalLinearDiagonalHom_det] at h
  simpa only [TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe,
    WithConv.ofConv_toConv, AlgHom.id_apply] using h


/-- The inverse determinant pulls back to the inverse standard monomial. -/
theorem generalLinearDeterminantSectionCoordinateMap_inverse (pivot : n) :
    (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom
      (Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det) =
        MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-1 : ℤ))) 1 := by
  rw [(TauCeti.GeneralLinear.isUnit_det_reindexedGenericMatrix K n).map_ringInverse,
    generalLinearDeterminantSectionCoordinateMap_det]
  exact Ring.inverse_unit ((MonoidAlgebra.of K (ULift.{u} (Multiplicative ℤ))).toHomUnits
    (ULift.up (Multiplicative.ofAdd (1 : ℤ))))

/-- The determinant following the one-pivot section is the identity on coordinate algebras. -/
theorem generalLinearDeterminantSectionCoordinateMap_comp_det (pivot : n) :
    (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom.comp
      (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom =
        AlgHom.id K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) := by
  apply WithConv.toConv_injective
  apply (((TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K)
      (A := MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)))
      (G := ULift.{u} (Multiplicative ℤ))).trans
      (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv
        (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)))ˣ).symm)).injective
  apply Units.ext
  simp only [MulEquiv.trans_apply,
    TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe,
    AlgHom.comp_apply, AlgHom.id_apply]
  erw [generalLinearDeterminantSchemeCoordinateMap_generator,
    generalLinearDeterminantSectionCoordinateMap_det]

/-- The section as a morphism between the canonical group schemes. -/
def generalLinearDeterminantSectionSchemeHom (pivot : n) :
    TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K ⟶
      TauCeti.GeneralLinear.groupScheme K (Fintype.card n) := by
  change (hopfSpec (.of K)).obj
      (.op (CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))))) ⟶
    (hopfSpec (.of K)).obj
      (.op (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)))
  exact (hopfSpec (.of K)).map (.op (generalLinearDeterminantSectionCoordinateMap K n pivot))

/-- The underlying section is the spectrum map of its canonical coordinate morphism. -/
@[simp]
theorem generalLinearDeterminantSectionSchemeHom_left (pivot : n) :
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom.toRingHom) := by
  unfold generalLinearDeterminantSectionSchemeHom
  exact (show ∀ f : TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) ⟶
      CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))),
      ((hopfSpec (.of K)).map f.op).hom.hom.left =
        Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) from fun f => rfl) _


/-- Pulling back a generic entry along the section gives its diagonal monomial. -/
theorem generalLinearDeterminantSection_preimage_entry (pivot i j : n) :
    (Spec.preimage (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j) =
      if i = j then (if i = pivot then
        MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1 else 1) else 0 := by
  rw [generalLinearDeterminantSectionSchemeHom_left]
  erw [Spec.preimage_map]
  exact generalLinearDeterminantSectionCoordinateMap_entry K n pivot i j

/-- Pulling back the inverse determinant along the section gives its inverse monomial. -/
theorem generalLinearDeterminantSection_preimage_detInverse (pivot : n) :
    (Spec.preimage (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (Ring.inverse (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det) =
        MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-1 : ℤ))) 1 := by
  rw [generalLinearDeterminantSectionSchemeHom_left]
  erw [Spec.preimage_map]
  exact generalLinearDeterminantSectionCoordinateMap_inverse K n pivot

/-- The section sends each unit-valued affine point to its one-pivot diagonal matrix. -/
theorem generalLinearDeterminantSection_point
    (R : Type u) [CommRing R] [Algebra K R] (pivot : n) (unit : Rˣ) :
    (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := K) (A := R)).symm unit ≫
      (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom =
    TauCeti.GeneralLinear.groupSchemePointMulEquiv (Fintype.card n) R
      ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm
        (generalLinearDiagonalHom n pivot unit)) := by
  let q : WithConv (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐ[K] R) :=
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K) (A := R)).symm
      (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv Rˣ unit)
  have hu : (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := K) (A := R)).symm unit =
      (TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := K) (A := R) TauCeti.DiagonalizableGroup.multiplicativeCharacterGroup).symm q := by
    apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := K) (A := R)).injective
    rw [MulEquiv.apply_symm_apply,
      TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_apply,
      TauCeti.DiagonalizableGroup.schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv,
      MulEquiv.apply_symm_apply]
    simp only [q, MulEquiv.apply_symm_apply]
    simpa only [toAdd_ofAdd, zpow_one] using
      (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_apply Rˣ unit
        (Multiplicative.ofAdd (1 : ℤ))).symm
  have h := congrArg WithConv.ofConv
    (generalLinearDeterminantSectionCoordinateMap_points K n R pivot q)
  have hpoint : q.ofConv.comp
      (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom =
      ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm
        (generalLinearDiagonalHom n pivot unit)).ofConv := by
    simpa only [generalLinearDeterminantSectionPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, q,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply,
      WithConv.ofConv_toConv] using h
  rw [hu]
  apply Over.OverMorphism.ext
  rw [Over.comp_left,
    TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_symm_apply_left,
    generalLinearDeterminantSectionSchemeHom_left,
    TauCeti.GeneralLinear.groupSchemePointMulEquiv_apply_left]
  change Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm
          (generalLinearDiagonalHom n pivot unit)).ofConv.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) hpoint

/-- Determinant has a one-pivot section over every commutative base ring. -/
theorem generalLinearDeterminantSectionSchemeHom_comp_det (pivot : n) :
    generalLinearDeterminantSectionSchemeHom K n pivot ≫
      generalLinearDeterminantSchemeHom K n =
        𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left ≫
    (generalLinearDeterminantSchemeHom K n).hom.hom.left = 𝟙 _
  rw [generalLinearDeterminantSectionSchemeHom_left,
    generalLinearDeterminantSchemeHom_left]
  erw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((generalLinearDeterminantSectionCoordinateMap K n pivot).hom.toAlgHom.comp
      (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom).toRingHom)) = 𝟙 _
  rw [generalLinearDeterminantSectionCoordinateMap_comp_det]
  exact Spec.map_id _

/-- The explicit one-pivot witness that determinant is a split epimorphism. -/
def generalLinearDeterminantSplitEpi (pivot : n) :
    CategoryTheory.SplitEpi (generalLinearDeterminantSchemeHom K n) where
  section_ := generalLinearDeterminantSectionSchemeHom K n pivot
  id := generalLinearDeterminantSectionSchemeHom_comp_det K n pivot

omit [DecidableEq n] in
theorem generalLinearDeterminant_isSplitEpi (pivot : n) :
    CategoryTheory.IsSplitEpi (generalLinearDeterminantSchemeHom K n) := by
  classical
  exact CategoryTheory.IsSplitEpi.mk' (generalLinearDeterminantSplitEpi K n pivot)

/-- The section identity holds on points of every test scheme, without affineness assumptions. -/
theorem generalLinearDeterminantSection_testScheme (pivot : n)
    (T : Over (Spec (.of K)))
    (point : T ⟶ (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X) :
    (point ≫ (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom = point := by
  have h := congrArg (fun morphism : TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K ⟶
      TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K ↦ morphism.hom.hom)
    (generalLinearDeterminantSectionSchemeHom_comp_det K n pivot)
  change (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom ≫
    (generalLinearDeterminantSchemeHom K n).hom.hom = 𝟙 _ at h
  rw [Category.assoc, h, Category.comp_id]

end AlgebraicGeometry
