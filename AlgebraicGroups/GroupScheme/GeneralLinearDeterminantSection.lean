/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Chris Birkbeck, Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant

/-!
# A one-pivot section of the determinant character

For a specified matrix index `pivot`, the multiplicative group scheme embeds into the
finite general linear group scheme by placing a unit in that diagonal position and
ones in all other diagonal positions. The explicit pivot is essential: in rank zero,
the determinant is constant one and need not have a section over an arbitrary base.
The diagonal witness follows the construction in mathlib's
`Matrix.GeneralLinearGroup.det_surjective` (Chris Birkbeck, Apache-2.0); unlike
pointwise surjectivity, the result here is a natural, multiplicative morphism of
native group schemes over any commutative base.
-/

public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The invertible diagonal matrix carrying a unit at the distinguished index. -/
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

/-- The invertible Laurent coordinate, represented as a unit. -/
def generalLinearSectionLaurentUnit : (multiplicativeGroupCoordinateRing K)ˣ :=
  (multiplicativeGroupCoordinate_isUnit K).unit

@[simp] theorem generalLinearSectionLaurentUnit_val :
    (generalLinearSectionLaurentUnit K : multiplicativeGroupCoordinateRing K) =
      multiplicativeGroupCoordinate K :=
  (multiplicativeGroupCoordinate_isUnit K).unit_spec

/-- The contravariant coordinate map of the diagonal section. -/
@[expose] def generalLinearDeterminantSectionCoordinateMap (pivot : n) :
    CoordinateRing K n →ₐ[K] multiplicativeGroupCoordinateRing K :=
  evaluate (generalLinearDiagonalHom n pivot (generalLinearSectionLaurentUnit K))

theorem generalLinearDeterminantSectionCoordinateMap_entry (pivot i j : n) :
    generalLinearDeterminantSectionCoordinateMap K n pivot (matrix K n i j) =
      if i = j then (if i = pivot then multiplicativeGroupCoordinate K else 1) else 0 := by
  unfold generalLinearDeterminantSectionCoordinateMap
  rw [evaluate_matrix]
  change generalLinearDiagonalUnit n pivot (generalLinearSectionLaurentUnit K) i j = _
  rw [generalLinearDiagonalUnit_apply, generalLinearSectionLaurentUnit_val]

/-- The section's coordinate map sends inverse determinant to inverse Laurent coordinate. -/
theorem generalLinearDeterminantSectionCoordinateMap_detInverse (pivot : n) :
    generalLinearDeterminantSectionCoordinateMap K n pivot (detInverse K n) =
      ((generalLinearSectionLaurentUnit K)⁻¹ : (multiplicativeGroupCoordinateRing K)ˣ) := by
  change evaluate (generalLinearDiagonalHom n pivot (generalLinearSectionLaurentUnit K))
    (detInverse K n) = _
  rw [evaluate_detInverse, generalLinearDiagonalHom_det]

/-- The inverse of the universal Laurent unit is the inverse Laurent coordinate. -/
theorem generalLinearSectionLaurentUnit_inv_val :
    (↑((generalLinearSectionLaurentUnit K)⁻¹) : multiplicativeGroupCoordinateRing K) =
      LaurentPolynomial.T (-1) := by
  have hinv : (multiplicativeGroupCoordinate K) * LaurentPolynomial.T (-1) = 1 := by
    change (LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) :
      LaurentPolynomial K) = 1
    rw [← LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  have hv : (multiplicativeGroupCoordinate K) *
      (↑((generalLinearSectionLaurentUnit K)⁻¹) : multiplicativeGroupCoordinateRing K) = 1 := by
    rw [← generalLinearSectionLaurentUnit_val]
    exact (generalLinearSectionLaurentUnit K).mul_inv
  apply (generalLinearSectionLaurentUnit K).isUnit.mul_left_cancel
  exact hv.trans hinv.symm

/-- Readback of the inverse determinant through the diagonal section. -/
theorem generalLinearDeterminantSectionCoordinateMap_inverse (pivot : n) :
    generalLinearDeterminantSectionCoordinateMap K n pivot (detInverse K n) =
      LaurentPolynomial.T (-1) := by
  rw [generalLinearDeterminantSectionCoordinateMap_detInverse,
    generalLinearSectionLaurentUnit_inv_val]

/-- The section's coordinate map sends determinant to the distinguished Laurent coordinate. -/
theorem generalLinearDeterminantSectionCoordinateMap_det (pivot : n) :
    generalLinearDeterminantSectionCoordinateMap K n pivot (matrix K n).det =
      multiplicativeGroupCoordinate K := by
  change evaluate (generalLinearDiagonalHom n pivot (generalLinearSectionLaurentUnit K))
    (matrix K n).det = _
  rw [evaluate_det, ← Matrix.GeneralLinearGroup.val_det_apply,
    generalLinearDiagonalHom_det, generalLinearSectionLaurentUnit_val]

/-- Compatibility with the native counit and comultiplication of the GL and
multiplicative-group coordinate Hopf algebras. -/
@[expose] def generalLinearDeterminantSectionBialgHom (pivot : n) :
    CoordinateRing K n →ₐc[K] multiplicativeGroupCoordinateRing K :=
  BialgHom.ofAlgHom (generalLinearDeterminantSectionCoordinateMap K n pivot)
    (by
      apply hom_ext (K := K) (n := n)
      intro i j
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
        generalLinearDeterminantSectionCoordinateMap_entry,
        native_counit_matrix, Matrix.one_apply]
      by_cases hij : i = j
      · subst j
        by_cases hip : i = pivot <;> simp [hip, multiplicativeGroupCoordinate_counit]
      · simp [hij])
    (by
      apply hom_ext (K := K) (n := n)
      intro i j
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        native_comul_matrix, map_sum, Algebra.TensorProduct.map_tmul,
        generalLinearDeterminantSectionCoordinateMap_entry]
      by_cases hij : i = j
      · subst j
        by_cases hip : i = pivot
        · simp [hip, multiplicativeGroupCoordinate_comul,
            TensorProduct.ite_tmul, TensorProduct.tmul_ite]
        · simp [hip, TensorProduct.ite_tmul, TensorProduct.tmul_ite,
            Algebra.TensorProduct.one_def]
      · simp [hij, TensorProduct.ite_tmul, TensorProduct.tmul_ite])

/-- The one-pivot diagonal section as an actual native group-scheme morphism. -/
@[expose] def generalLinearDeterminantSectionSchemeHom (pivot : n) :
    multiplicativeGroupScheme K ⟶ generalLinearGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom
      (generalLinearDeterminantSectionBialgHom K n pivot)))

private theorem generalLinearSection_laurent_ext {R : Type u} [CommRing R]
    [Algebra K R] {f g : multiplicativeGroupCoordinateRing K →ₐ[K] R}
    (h : f (multiplicativeGroupCoordinate K) = g (multiplicativeGroupCoordinate K)) :
    f = g := by
  let equiv := multiplicativeGroupMulEquivAlgHom K R
  let uf := equiv.symm (WithConv.toConv f)
  let ug := equiv.symm (WithConv.toConv g)
  have hu : uf = ug := by
    apply Units.ext
    rw [← multiplicativeGroupMulEquivAlgHom_coordinate K R uf,
      ← multiplicativeGroupMulEquivAlgHom_coordinate K R ug]
    simpa [uf, ug, equiv] using h
  have := congrArg (fun unit : Rˣ ↦ (equiv unit).ofConv) hu
  simpa [uf, ug, equiv] using this

/-- On coordinate rings, the determinant following the section is the identity. -/
theorem generalLinearDeterminantSectionCoordinateMap_comp_det (pivot : n) :
    (generalLinearDeterminantSectionCoordinateMap K n pivot).comp
      (generalLinearDeterminantCoordinateMap K n) =
      AlgHom.id K (multiplicativeGroupCoordinateRing K) := by
  apply generalLinearSection_laurent_ext K
  simp only [AlgHom.comp_apply, AlgHom.id_apply,
    generalLinearDeterminantCoordinateMap_coordinate,
    generalLinearDeterminantSectionCoordinateMap_det]

/-- Determinant has an actual section in group schemes over `Spec K`. -/
theorem generalLinearDeterminantSectionSchemeHom_comp_det (pivot : n) :
    generalLinearDeterminantSectionSchemeHom K n pivot ≫
      generalLinearDeterminantSchemeHom K n = 𝟙 (multiplicativeGroupScheme K) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left ≫
    (generalLinearDeterminantSchemeHom K n).hom.hom.left = 𝟙 _
  change Spec.map (CommRingCat.ofHom
    (generalLinearDeterminantSectionCoordinateMap K n pivot).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantCoordinateMap K n).toRingHom) = 𝟙 _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((generalLinearDeterminantSectionCoordinateMap K n pivot).comp
      (generalLinearDeterminantCoordinateMap K n)).toRingHom)) = 𝟙 _
  rw [generalLinearDeterminantSectionCoordinateMap_comp_det]
  change Spec.map (𝟙 (CommRingCat.of (multiplicativeGroupCoordinateRing K))) = 𝟙 _
  exact Spec.map_id _

/-- The explicit diagonal witness for the split epimorphism. -/
def generalLinearDeterminantSplitEpi (pivot : n) :
    CategoryTheory.SplitEpi (generalLinearDeterminantSchemeHom K n) where
  section_ := generalLinearDeterminantSectionSchemeHom K n pivot
  id := generalLinearDeterminantSectionSchemeHom_comp_det K n pivot

theorem generalLinearDeterminant_isSplitEpi (pivot : n) :
    CategoryTheory.IsSplitEpi (generalLinearDeterminantSchemeHom K n) :=
  CategoryTheory.IsSplitEpi.mk' (generalLinearDeterminantSplitEpi K n pivot)

/-- The underlying affine section is the spectrum of the explicit coordinate map. -/
@[simp] theorem generalLinearDeterminantSectionSchemeHom_left (pivot : n) :
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSectionCoordinateMap K n pivot).toRingHom) := rfl

/-- Pullback of the universal matrix entry along the actual affine section. -/
theorem generalLinearDeterminantSection_preimage_entry (pivot i j : n) :
    (Spec.preimage (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (matrix K n i j) =
      if i = j then (if i = pivot then multiplicativeGroupCoordinate K else 1) else 0 := by
  rw [generalLinearDeterminantSectionSchemeHom_left, Spec.preimage_map]
  exact generalLinearDeterminantSectionCoordinateMap_entry K n pivot i j

/-- Pullback of inverse determinant is the inverse Laurent coordinate. -/
theorem generalLinearDeterminantSection_preimage_detInverse (pivot : n) :
    (Spec.preimage (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom.left).hom
      (detInverse K n) = LaurentPolynomial.T (-1) := by
  rw [generalLinearDeterminantSectionSchemeHom_left, Spec.preimage_map]
  exact generalLinearDeterminantSectionCoordinateMap_inverse K n pivot

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The actual section sends the native scheme point of a unit to its diagonal
GL point, not merely to an abstractly isomorphic point. -/
theorem generalLinearDeterminantSection_point (pivot : n) (unit : Rˣ) :
    multiplicativeGroupMulEquivPoints K R unit ≫
      (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom =
    generalLinearGroupMulEquivPoints K n R (generalLinearDiagonalHom n pivot unit) := by
  have h : (multiplicativeGroupMulEquivAlgHom K R unit).ofConv.comp
      (generalLinearDeterminantSectionCoordinateMap K n pivot) =
      (generalLinearGroupMulEquivAlgHom K n R
        (generalLinearDiagonalHom n pivot unit)).ofConv := by
    apply hom_ext (K := K) (n := n)
    intro i j
    rw [AlgHom.comp_apply, generalLinearDeterminantSectionCoordinateMap_entry,
      generalLinearGroupMulEquivAlgHom_apply_matrix]
    by_cases hij : i = j
    · subst j
      by_cases hip : i = pivot
      · simp [hip, multiplicativeGroupMulEquivAlgHom_coordinate,
          generalLinearDiagonalHom, generalLinearDiagonalUnit_apply]
      · simp [hip, generalLinearDiagonalHom, generalLinearDiagonalUnit_apply]
    · simp [hij, generalLinearDiagonalHom, generalLinearDiagonalUnit_apply]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, multiplicativeGroupMulEquivPoints_apply_left,
    generalLinearGroupMulEquivPoints_apply_left,
    generalLinearDeterminantSectionSchemeHom_left]
  change Spec.map (CommRingCat.ofHom
      (multiplicativeGroupMulEquivAlgHom K R unit).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSectionCoordinateMap K n pivot).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (generalLinearGroupMulEquivAlgHom K n R
          (generalLinearDiagonalHom n pivot unit)).ofConv.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun hom : CoordinateRing K n →ₐ[K] R ↦
    Spec.map (CommRingCat.ofHom hom.toRingHom)) h

/-- The diagonal section, restricted to affine schemes, is natural in the
coefficient algebra. -/
def generalLinearDeterminantSectionFunctorHom (pivot : n) :
    multiplicativeGroupFunctor K ⟶ generalLinearGroupFunctor K n where
  app R := GrpCat.ofHom (generalLinearDiagonalHom n pivot)
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro unit
    exact (generalLinearDiagonalHom_natural n pivot f.hom.toRingHom unit).symm

/-- Section followed by determinant is the identity on points of *every* test
scheme over `Spec K`, with no affineness assumption on the test scheme. -/
theorem generalLinearDeterminantSection_testScheme (pivot : n)
    (T : Over (Spec (.of K)))
    (point : T ⟶ multiplicativeGroupUnderlyingScheme K) :
    (point ≫ (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom = point := by
  have h := congrArg (fun morphism : multiplicativeGroupScheme K ⟶
      multiplicativeGroupScheme K ↦ morphism.hom.hom)
    (generalLinearDeterminantSectionSchemeHom_comp_det K n pivot)
  change (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom ≫
    (generalLinearDeterminantSchemeHom K n).hom.hom = 𝟙 _ at h
  rw [Category.assoc, h, Category.comp_id]

end AlgebraicGeometry

#lint
