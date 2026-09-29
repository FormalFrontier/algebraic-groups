/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import AlgebraicGroups.GroupObject.SplitKernelSemidirect

/-! # The upper-triangular group scheme in unitriangular-first coordinates -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

theorem upperTriangularSection_over :
    (upperTriangularDiagonalSection K n).hom.hom ≫
      (upperTriangularDiagonalProjection K n).hom.hom =
        𝟙 (diagonalGroupUnderlyingScheme K n) := by
  simpa using congrArg (fun f : diagonalGroupScheme K n ⟶ diagonalGroupScheme K n =>
    f.hom.hom) (upperTriangularDiagonal_section K n)

/-- Conjugation by the represented diagonal section, restricted to the actual
unitriangular kernel in schemes over `Spec K`. -/
def upperTriangularDiagonalConj :
    diagonalGroupUnderlyingScheme K n ⊗ unitriangularGroupUnderlyingScheme K n ⟶
      unitriangularGroupUnderlyingScheme K n :=
  splitKernelConj (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
    (upperTriangularSection_over K n)

/-- The inclusion reads represented conjugation as multiplication in the
upper-triangular group, for arrows from any test scheme. -/
theorem upperTriangularDiagonalConj_lift_comp_inclusion
    {test : Over (Spec (.of K))}
    (diag : test ⟶ diagonalGroupUnderlyingScheme K n)
    (unit : test ⟶ unitriangularGroupUnderlyingScheme K n) :
    (lift diag unit ≫ upperTriangularDiagonalConj K n) ≫
        (unitriangularToUpperTriangular K n).hom.hom =
      (diag ≫ (upperTriangularDiagonalSection K n).hom.hom) *
        (unit ≫ (unitriangularToUpperTriangular K n).hom.hom) *
        (diag ≫ (upperTriangularDiagonalSection K n).hom.hom)⁻¹ :=
  splitKernelConj_lift_comp_i _ _ _ _ _ diag unit

/-- The published section-first kernel product, specialized to the represented
upper-triangular group. Its multiplication convention differs from the U-first iso. -/
def upperTriangularSectionFirstIso :
    unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n ≅
      upperTriangularGroupUnderlyingScheme K n :=
  splitKernelProductIso (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
    (upperTriangularSection_over K n)

private theorem upperTriangularConj_cancel_left
    {test : Over (Spec (.of K))}
    (diag : test ⟶ diagonalGroupUnderlyingScheme K n)
    (unit : test ⟶ unitriangularGroupUnderlyingScheme K n) :
    lift diag (lift diag⁻¹ unit ≫ upperTriangularDiagonalConj K n) ≫
      upperTriangularDiagonalConj K n = unit := by
  have action := splitKernelConj_mul
    (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
    (upperTriangularSection_over K n) diag diag⁻¹ unit
  change lift (diag * diag⁻¹) unit ≫ upperTriangularDiagonalConj K n = _ at action
  rw [mul_inv_cancel] at action
  exact action.symm.trans (splitKernelConj_one _ _ _ _ _ unit)

private theorem upperTriangularConj_cancel_right
    {test : Over (Spec (.of K))}
    (diag : test ⟶ diagonalGroupUnderlyingScheme K n)
    (unit : test ⟶ unitriangularGroupUnderlyingScheme K n) :
    lift diag⁻¹ (lift diag unit ≫ upperTriangularDiagonalConj K n) ≫
      upperTriangularDiagonalConj K n = unit := by
  have action := splitKernelConj_mul
    (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
    (upperTriangularSection_over K n) diag⁻¹ diag unit
  change lift (diag⁻¹ * diag) unit ≫ upperTriangularDiagonalConj K n = _ at action
  rw [inv_mul_cancel] at action
  exact action.symm.trans (splitKernelConj_one _ _ _ _ _ unit)

/-- Change from unitriangular-first to section-first coordinates. The inverse
uses the forward diagonal action, and both maps are scheme morphisms. -/
def upperTriangularCoordinateChange :
    unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n ≅
      unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n where
  hom := lift
    (lift (snd _ _)⁻¹ (fst _ _) ≫ upperTriangularDiagonalConj K n)
    (snd _ _)
  inv := lift
    (lift (snd _ _) (fst _ _) ≫ upperTriangularDiagonalConj K n)
    (snd _ _)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [← Category.assoc, comp_lift, lift_fst, lift_snd, Category.id_comp] using
        upperTriangularConj_cancel_left K n (snd _ _) (fst _ _)
    · simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [← Category.assoc, comp_lift, lift_fst, lift_snd, GrpObj.comp_inv,
        Category.id_comp] using
        upperTriangularConj_cancel_right K n (snd _ _) (fst _ _)
    · simp

/-- The underlying U-first product isomorphism `U × D ≅ T` over `Spec K`.
Its forward arrow is unitriangular inclusion followed by diagonal section. -/
def upperTriangularUFirstIso :
    unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n ≅
      upperTriangularGroupUnderlyingScheme K n :=
  upperTriangularCoordinateChange K n ≪≫ upperTriangularSectionFirstIso K n

/-- The U-first forward arrow multiplies inclusion on the left and section on
the right, unlike the published section-first product. -/
theorem upperTriangularUFirstIso_hom :
    (upperTriangularUFirstIso K n).hom =
      (fst (unitriangularGroupUnderlyingScheme K n)
        (diagonalGroupUnderlyingScheme K n) ≫
          (unitriangularToUpperTriangular K n).hom.hom) *
      (snd (unitriangularGroupUnderlyingScheme K n)
        (diagonalGroupUnderlyingScheme K n) ≫
          (upperTriangularDiagonalSection K n).hom.hom) := by
  change (upperTriangularCoordinateChange K n).hom ≫
    (upperTriangularSectionFirstIso K n).hom = _
  rw [upperTriangularSectionFirstIso, splitKernelProductIso_hom]
  change (lift
    (lift (snd _ _)⁻¹ (fst _ _) ≫ upperTriangularDiagonalConj K n)
    (snd _ _)) ≫
      ((snd _ _ ≫ (upperTriangularDiagonalSection K n).hom.hom) *
        (fst _ _ ≫ (unitriangularToUpperTriangular K n).hom.hom)) = _
  simp only [MonObj.comp_mul, ← Category.assoc, lift_snd, lift_fst]
  rw [upperTriangularDiagonalConj_lift_comp_inclusion]
  rw [GrpObj.inv_comp]
  group

/-- The diagonal of the forward U-first product is its second projection. -/
theorem upperTriangularUFirstIso_hom_comp_diagonal :
    (upperTriangularUFirstIso K n).hom ≫
      (upperTriangularDiagonalProjection K n).hom.hom =
        snd (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) := by
  rw [upperTriangularUFirstIso_hom, MonObj.mul_comp]
  have kernel : (unitriangularToUpperTriangular K n).hom.hom ≫
      (upperTriangularDiagonalProjection K n).hom.hom =
        toUnit (unitriangularGroupUnderlyingScheme K n) ≫
          η[diagonalGroupUnderlyingScheme K n] :=
    (upperTriangularDiagonalSquare_isPullback_over K n).w
  simp only [Category.assoc, kernel, upperTriangularSection_over, Category.comp_id]
  rw [← Category.assoc, comp_toUnit]
  change lift (toUnit _ ≫ η[diagonalGroupUnderlyingScheme K n])
    (snd (unitriangularGroupUnderlyingScheme K n)
      (diagonalGroupUnderlyingScheme K n)) ≫
      μ[diagonalGroupUnderlyingScheme K n] = _
  exact MonObj.lift_comp_one_left _ _

/-- The second inverse coordinate is precisely the diagonal projection. -/
theorem upperTriangularUFirstIso_inv_comp_snd :
    (upperTriangularUFirstIso K n).inv ≫
      snd (unitriangularGroupUnderlyingScheme K n)
        (diagonalGroupUnderlyingScheme K n) =
      (upperTriangularDiagonalProjection K n).hom.hom := by
  have sectionSnd :
      (upperTriangularSectionFirstIso K n).inv ≫
        snd (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) =
        (upperTriangularDiagonalProjection K n).hom.hom :=
    splitKernelProductIso_inv_comp_snd
      (unitriangularToUpperTriangular K n).hom.hom
      (upperTriangularDiagonalProjection K n).hom.hom
      (upperTriangularDiagonalSection K n).hom.hom
      (upperTriangularDiagonalSquare_isPullback_over K n)
      (upperTriangularSection_over K n)
  have changeSnd :
      (upperTriangularCoordinateChange K n).inv ≫
        snd (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) =
        snd (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) := by
    change lift (lift (snd _ _) (fst _ _) ≫ upperTriangularDiagonalConj K n)
      (snd _ _) ≫ snd _ _ = _
    exact lift_snd _ _
  change (upperTriangularSectionFirstIso K n).inv ≫
    (upperTriangularCoordinateChange K n).inv ≫ snd _ _ = _
  rw [changeSnd, sectionSnd]

/-- Right normalization characterizes the first inverse coordinate after its
unitriangular inclusion. -/
theorem upperTriangularUFirstIso_inv_fst_comp_inclusion :
    ((upperTriangularUFirstIso K n).inv ≫
      fst (unitriangularGroupUnderlyingScheme K n)
        (diagonalGroupUnderlyingScheme K n)) ≫
        (unitriangularToUpperTriangular K n).hom.hom =
      𝟙 (upperTriangularGroupUnderlyingScheme K n) *
        ((upperTriangularDiagonalProjection K n).hom.hom ≫
          (upperTriangularDiagonalSection K n).hom.hom)⁻¹ := by
  have factor := (upperTriangularUFirstIso K n).inv_hom_id
  rw [upperTriangularUFirstIso_hom, MonObj.comp_mul] at factor
  have factor' :
      (((upperTriangularUFirstIso K n).inv ≫ fst _ _) ≫
        (unitriangularToUpperTriangular K n).hom.hom) *
        ((upperTriangularDiagonalProjection K n).hom.hom ≫
          (upperTriangularDiagonalSection K n).hom.hom) =
        𝟙 (upperTriangularGroupUnderlyingScheme K n) := by
    simpa only [← Category.assoc, upperTriangularUFirstIso_inv_comp_snd] using factor
  calc
    _ = ((((upperTriangularUFirstIso K n).inv ≫ fst _ _) ≫
          (unitriangularToUpperTriangular K n).hom.hom) *
        ((upperTriangularDiagonalProjection K n).hom.hom ≫
          (upperTriangularDiagonalSection K n).hom.hom)) *
        ((upperTriangularDiagonalProjection K n).hom.hom ≫
          (upperTriangularDiagonalSection K n).hom.hom)⁻¹ := by group
    _ = _ := by rw [factor']

/-- The U-first twisted law holds as an equality of morphisms from every test
scheme over `Spec K`, not only as a law on affine or rational points. -/
theorem upperTriangularUFirstIso_mul_lift
    {test : Over (Spec (.of K))}
    (unit unit' : test ⟶ unitriangularGroupUnderlyingScheme K n)
    (diag diag' : test ⟶ diagonalGroupUnderlyingScheme K n) :
    lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
        (diag * diag') ≫ (upperTriangularUFirstIso K n).hom =
      (lift unit diag ≫ (upperTriangularUFirstIso K n).hom) *
        (lift unit' diag' ≫ (upperTriangularUFirstIso K n).hom) := by
  simp only [upperTriangularUFirstIso_hom, MonObj.comp_mul,
    ← Category.assoc, lift_fst, lift_snd, MonObj.mul_comp]
  rw [upperTriangularDiagonalConj_lift_comp_inclusion]
  group

/-- The twisted U-first multiplication on the underlying product. This is not
the canonical direct-product group law. -/
def upperTriangularUFirstTwistedMul :
    (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n) ⊗
      (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n) ⟶
        unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n :=
  let first := fst (unitriangularGroupUnderlyingScheme K n ⊗
    diagonalGroupUnderlyingScheme K n)
    (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n)
  let second := snd (unitriangularGroupUnderlyingScheme K n ⊗
    diagonalGroupUnderlyingScheme K n)
    (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n)
  let unit := first ≫ fst _ _
  let diag := first ≫ snd _ _
  let unit' := second ≫ fst _ _
  let diag' := second ≫ snd _ _
  lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
    (diag * diag')

/-- The U-first twisted product diagram is an equality of represented scheme
morphisms on the product of two coordinate spaces. -/
theorem upperTriangularUFirstTwistedMul_comp_hom :
    upperTriangularUFirstTwistedMul K n ≫ (upperTriangularUFirstIso K n).hom =
      ((upperTriangularUFirstIso K n).hom ⊗ₘ
        (upperTriangularUFirstIso K n).hom) ≫
        μ[upperTriangularGroupUnderlyingScheme K n] := by
  let first := fst (unitriangularGroupUnderlyingScheme K n ⊗
    diagonalGroupUnderlyingScheme K n)
    (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n)
  let second := snd (unitriangularGroupUnderlyingScheme K n ⊗
    diagonalGroupUnderlyingScheme K n)
    (unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n)
  let unit := first ≫ fst _ _
  let diag := first ≫ snd _ _
  let unit' := second ≫ fst _ _
  let diag' := second ≫ snd _ _
  change lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
    (diag * diag') ≫ (upperTriangularUFirstIso K n).hom = _
  rw [upperTriangularUFirstIso_mul_lift K n unit unit' diag diag']
  simp [unit, unit', diag, diag', first, second, Hom.mul_def, tensorHom_def]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The represented action agrees with the native diagonal action on every
commutative coefficient algebra over `K`. -/
theorem upperTriangularDiagonalConj_point
    (diag : Matrix.DiagonalGroup n R) (unit : Matrix.UnitriangularGroup n R) :
    lift (diagonalGroupMulEquivPoints K n R diag)
        (unitriangularGroupMulEquivPoints K n R unit) ≫
          upperTriangularDiagonalConj K n =
      unitriangularGroupMulEquivPoints K n R
        (Matrix.UpperTriangularGroup.diagonalAction diag unit) := by
  apply (upperTriangularDiagonalSquare_isPullback_over K n).hom_ext
  · calc
      (lift (diagonalGroupMulEquivPoints K n R diag)
          (unitriangularGroupMulEquivPoints K n R unit) ≫
          upperTriangularDiagonalConj K n) ≫
          (unitriangularToUpperTriangular K n).hom.hom =
        (diagonalGroupMulEquivPoints K n R diag ≫
          (upperTriangularDiagonalSection K n).hom.hom) *
        (unitriangularGroupMulEquivPoints K n R unit ≫
          (unitriangularToUpperTriangular K n).hom.hom) *
        (diagonalGroupMulEquivPoints K n R diag ≫
          (upperTriangularDiagonalSection K n).hom.hom)⁻¹ :=
            upperTriangularDiagonalConj_lift_comp_inclusion K n _ _
      _ = upperTriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonalSection diag *
            Matrix.UnitriangularGroup.inUpperTriangular unit *
            (Matrix.UpperTriangularGroup.diagonalSection diag)⁻¹) := by
              rw [upperTriangularDiagonalSection_point,
                unitriangularToUpperTriangular_point]
              simp
      _ = unitriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonalAction diag unit) ≫
            (unitriangularToUpperTriangular K n).hom.hom := by
              rw [unitriangularToUpperTriangular_point,
                Matrix.UpperTriangularGroup.inUpperTriangular_diagonalAction]
  · simp

/-- Every affine point of the U-first scheme iso is the native semidirect
factorization, over arbitrary commutative `K`-algebras. -/
theorem upperTriangularUFirstIso_point
    (unit : Matrix.UnitriangularGroup n R) (diag : Matrix.DiagonalGroup n R) :
    lift (unitriangularGroupMulEquivPoints K n R unit)
        (diagonalGroupMulEquivPoints K n R diag) ≫
          (upperTriangularUFirstIso K n).hom =
      upperTriangularGroupMulEquivPoints K n R
        (Matrix.UpperTriangularGroup.semidirEquiv
          (⟨unit, diag⟩ : Matrix.UnitriangularGroup n R ⋊[Matrix.UpperTriangularGroup.diagonalAction]
            Matrix.DiagonalGroup n R)) := by
  rw [upperTriangularUFirstIso_hom]
  simp only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  rw [unitriangularToUpperTriangular_point,
    upperTriangularDiagonalSection_point]
  simp

/-- Both inverse coordinates recover the native unipotent and diagonal
factorization on every commutative coefficient algebra. -/
theorem upperTriangularUFirstIso_inv_point (matrix : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R matrix ≫
      (upperTriangularUFirstIso K n).inv =
        lift (unitriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.unipotentPart matrix))
          (diagonalGroupMulEquivPoints K n R
            (Matrix.UpperTriangularGroup.diagonal matrix)) := by
  have forward :
      lift (unitriangularGroupMulEquivPoints K n R
        (Matrix.UpperTriangularGroup.unipotentPart matrix))
        (diagonalGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonal matrix)) ≫
          (upperTriangularUFirstIso K n).hom =
        upperTriangularGroupMulEquivPoints K n R matrix := by
    rw [upperTriangularUFirstIso_point]
    simp
  calc
    _ = (lift (unitriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.unipotentPart matrix))
          (diagonalGroupMulEquivPoints K n R
            (Matrix.UpperTriangularGroup.diagonal matrix)) ≫
            (upperTriangularUFirstIso K n).hom) ≫
          (upperTriangularUFirstIso K n).inv := by rw [forward]
    _ = _ := by rw [Category.assoc, (upperTriangularUFirstIso K n).hom_inv_id,
      Category.comp_id]

/-- The first inverse coordinate is native column-normalized unipotent part. -/
theorem upperTriangularUFirstIso_inv_fst_point (matrix : Matrix.UpperTriangularGroup n R) :
    (upperTriangularGroupMulEquivPoints K n R matrix ≫
      (upperTriangularUFirstIso K n).inv) ≫
        fst (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) =
      unitriangularGroupMulEquivPoints K n R
        (Matrix.UpperTriangularGroup.unipotentPart matrix) := by
  rw [upperTriangularUFirstIso_inv_point]
  exact lift_fst _ _

/-- The second inverse coordinate is the native diagonal projection. -/
theorem upperTriangularUFirstIso_inv_snd_point (matrix : Matrix.UpperTriangularGroup n R) :
    (upperTriangularGroupMulEquivPoints K n R matrix ≫
      (upperTriangularUFirstIso K n).inv) ≫
        snd (unitriangularGroupUnderlyingScheme K n)
          (diagonalGroupUnderlyingScheme K n) =
      diagonalGroupMulEquivPoints K n R
        (Matrix.UpperTriangularGroup.diagonal matrix) := by
  rw [upperTriangularUFirstIso_inv_point]
  exact lift_snd _ _




end AlgebraicGeometry
