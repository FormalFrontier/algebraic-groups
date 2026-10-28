/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import AlgebraicGroups.GroupObject.SplitKernelSemidirect
public import AlgebraicGroups.GroupTheory.UpperTriangular

/-!
# The upper-triangular group scheme in unitriangular-first coordinates

The split unitriangular kernel first gives a section-first product. A
categorical coordinate change then yields the U-first underlying scheme
isomorphism `(u,d) ↦ i(u)e(d)` and its conjugation-twisted multiplication
diagram for every test scheme over `Spec K`. This is not the direct-product
group law or a transported group-object structure on the product.

## References

* J. S. Milne, *Algebraic Groups* (course notes, version 2.00), §§2.20–2.21:
  the field-base split triangular group and its semidirect-product law.
  The represented U-first arrow and arbitrary-commutative-base scheme-level
  diagram here are additional constructions, not assertions of those passages.
* `AlgebraicGroups.GroupObject.SplitKernelProduct` and
  `AlgebraicGroups.GroupObject.SplitKernelSemidirect`: earlier formalized
  categorical kernel trivialization and conjugation/action laws specialized
  here; `AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel`: the
  represented kernel and section.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: group objects
  and their multiplication on arbitrary test arrows.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

open TauCeti.GeneralLinear.UpperTriangular

variable (K : Type u) [CommRing K] (n : ℕ)

private theorem upperTriangularSection_over :
    (diagonalTorus K n).hom.hom ≫
      (diagonalProjection K n).hom.hom =
        𝟙 ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) := by
  exact congrArg (fun f : TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) ⟶
    TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) =>
    f.hom.hom) (diagonalTorus_comp_diagonalProjection K n)

/-- Conjugation by the represented diagonal section, restricted to the actual
unitriangular kernel in schemes over `Spec K`. -/
def upperTriangularDiagonalConj :
    (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X ⊗
      (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⟶
      (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X :=
  splitKernelConj (unitriangularInclusion K n).hom.hom
    (diagonalProjection K n).hom.hom
    (diagonalTorus K n).hom.hom
    (isPullback_diagonalProjection_over K n)
    (by
      exact congrArg (fun f : TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) ⟶
        TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) => f.hom.hom)
        (diagonalTorus_comp_diagonalProjection K n))

/-- The inclusion reads represented conjugation as multiplication in the
upper-triangular group, for arrows from any test scheme. -/
theorem upperTriangularDiagonalConj_lift_comp_inclusion
    {test : Over (Spec (.of K))}
    (diag : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    (unit : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) :
    (lift diag unit ≫ upperTriangularDiagonalConj K n) ≫
        (unitriangularInclusion K n).hom.hom =
      (diag ≫ (diagonalTorus K n).hom.hom) *
        (unit ≫ (unitriangularInclusion K n).hom.hom) *
        (diag ≫ (diagonalTorus K n).hom.hom)⁻¹ :=
  splitKernelConj_lift_comp_i _ _ _ _ _ diag unit

/-- The generic split-kernel section-first product specialized to the
represented upper-triangular group: `F(v,d) = e(d)i(v)`. Its multiplication
convention differs from the U-first isomorphism. Compare Milne,
*Algebraic Groups* (course notes, version 2.00), §§2.20–2.21 for the
field-base split triangular group. -/
def upperTriangularSectionFirstIso :
    (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X ≅
      (groupScheme K n).X :=
  splitKernelProductIso (unitriangularInclusion K n).hom.hom
    (diagonalProjection K n).hom.hom
    (diagonalTorus K n).hom.hom
    (isPullback_diagonalProjection_over K n)
    (by
      exact congrArg (fun f : TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) ⟶
        TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n)) => f.hom.hom)
        (diagonalTorus_comp_diagonalProjection K n))

private theorem upperTriangularConj_cancel_left
    {test : Over (Spec (.of K))}
    (diag : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    (unit : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) :
    lift diag (lift diag⁻¹ unit ≫ upperTriangularDiagonalConj K n) ≫
      upperTriangularDiagonalConj K n = unit := by
  have action := splitKernelConj_mul
    (unitriangularInclusion K n).hom.hom
    (diagonalProjection K n).hom.hom
    (diagonalTorus K n).hom.hom
    (isPullback_diagonalProjection_over K n)
    (upperTriangularSection_over K n) diag diag⁻¹ unit
  change lift (diag * diag⁻¹) unit ≫ upperTriangularDiagonalConj K n = _ at action
  rw [mul_inv_cancel] at action
  exact action.symm.trans (splitKernelConj_one _ _ _ _ _ unit)

private theorem upperTriangularConj_cancel_right
    {test : Over (Spec (.of K))}
    (diag : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    (unit : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) :
    lift diag⁻¹ (lift diag unit ≫ upperTriangularDiagonalConj K n) ≫
      upperTriangularDiagonalConj K n = unit := by
  have action := splitKernelConj_mul
    (unitriangularInclusion K n).hom.hom
    (diagonalProjection K n).hom.hom
    (diagonalTorus K n).hom.hom
    (isPullback_diagonalProjection_over K n)
    (upperTriangularSection_over K n) diag⁻¹ diag unit
  change lift (diag⁻¹ * diag) unit ≫ upperTriangularDiagonalConj K n = _ at action
  rw [inv_mul_cancel] at action
  exact action.symm.trans (splitKernelConj_one _ _ _ _ _ unit)

/-- Change from unitriangular-first to section-first coordinates. The inverse
uses the forward diagonal action, and both maps are scheme morphisms. -/
def upperTriangularCoordinateChange :
    (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X ≅
      (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
        (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X where
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
Its forward arrow multiplies unitriangular inclusion on the left by diagonal
section on the right; its inverse extracts the diagonal and normalizes each
column by the inverse diagonal unit. The field-base semidirect antecedent is
Milne, *Algebraic Groups* (course notes, version 2.00), §2.20; the categorical
isomorphism here works over arbitrary commutative base rings. -/
def upperTriangularUFirstIso :
    (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X ≅
      (groupScheme K n).X :=
  upperTriangularCoordinateChange K n ≪≫ upperTriangularSectionFirstIso K n

/-- The U-first forward arrow multiplies inclusion on the left and section on
the right, unlike the generic section-first product. -/
theorem upperTriangularUFirstIso_hom :
    (upperTriangularUFirstIso K n).hom =
      (fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
        ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ≫
          (unitriangularInclusion K n).hom.hom) *
      (snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
        ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ≫
          (diagonalTorus K n).hom.hom) := by
  change (upperTriangularCoordinateChange K n).hom ≫
    (upperTriangularSectionFirstIso K n).hom = _
  rw [upperTriangularSectionFirstIso, splitKernelProductIso_hom]
  change (lift
    (lift (snd _ _)⁻¹ (fst _ _) ≫ upperTriangularDiagonalConj K n)
    (snd _ _)) ≫
      ((snd _ _ ≫ (diagonalTorus K n).hom.hom) *
        (fst _ _ ≫ (unitriangularInclusion K n).hom.hom)) = _
  simp only [MonObj.comp_mul, ← Category.assoc, lift_snd, lift_fst]
  rw [upperTriangularDiagonalConj_lift_comp_inclusion]
  rw [GrpObj.inv_comp]
  group

/-- The diagonal of the forward U-first product is its second projection. -/
theorem upperTriangularUFirstIso_hom_comp_diagonal :
    (upperTriangularUFirstIso K n).hom ≫
      (diagonalProjection K n).hom.hom =
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) := by
  rw [upperTriangularUFirstIso_hom, MonObj.mul_comp]
  have kernel : (unitriangularInclusion K n).hom.hom ≫
      (diagonalProjection K n).hom.hom =
        toUnit ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) ≫
          η[(TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X] :=
    (isPullback_diagonalProjection_over K n).w
  simp only [Category.assoc, kernel, upperTriangularSection_over, Category.comp_id]
  rw [← Category.assoc, comp_toUnit]
  change lift (toUnit _ ≫ η[(TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X])
    (snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
      ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)) ≫
      μ[(TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X] = _
  exact MonObj.lift_comp_one_left _ _

/-- The second inverse coordinate is precisely the diagonal projection. -/
theorem upperTriangularUFirstIso_inv_comp_snd :
    (upperTriangularUFirstIso K n).inv ≫
      snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
        ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) =
      (diagonalProjection K n).hom.hom := by
  have sectionSnd :
      (upperTriangularSectionFirstIso K n).inv ≫
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) =
        (diagonalProjection K n).hom.hom :=
    splitKernelProductIso_inv_comp_snd
      (unitriangularInclusion K n).hom.hom
      (diagonalProjection K n).hom.hom
      (diagonalTorus K n).hom.hom
      (isPullback_diagonalProjection_over K n)
      (upperTriangularSection_over K n)
  have changeSnd :
      (upperTriangularCoordinateChange K n).inv ≫
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) =
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) := by
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
      fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
        ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)) ≫
        (unitriangularInclusion K n).hom.hom =
      𝟙 ((groupScheme K n).X) *
        ((diagonalProjection K n).hom.hom ≫
          (diagonalTorus K n).hom.hom)⁻¹ := by
  have factor := (upperTriangularUFirstIso K n).inv_hom_id
  rw [upperTriangularUFirstIso_hom, MonObj.comp_mul] at factor
  have factor' :
      (((upperTriangularUFirstIso K n).inv ≫ fst _ _) ≫
        (unitriangularInclusion K n).hom.hom) *
        ((diagonalProjection K n).hom.hom ≫
          (diagonalTorus K n).hom.hom) =
        𝟙 ((groupScheme K n).X) := by
    simpa only [← Category.assoc, upperTriangularUFirstIso_inv_comp_snd] using factor
  calc
    _ = ((((upperTriangularUFirstIso K n).inv ≫ fst _ _) ≫
          (unitriangularInclusion K n).hom.hom) *
        ((diagonalProjection K n).hom.hom ≫
          (diagonalTorus K n).hom.hom)) *
        ((diagonalProjection K n).hom.hom ≫
          (diagonalTorus K n).hom.hom)⁻¹ := by group
    _ = _ := by rw [factor']

/-- The U-first twisted law holds as an equality of morphisms from every test
scheme over `Spec K`, not only as a law on affine or rational points. Its
field-base group-law antecedent is Milne, *Algebraic Groups* (course notes,
version 2.00), §§2.20–2.21. -/
theorem upperTriangularUFirstIso_mul_lift
    {test : Over (Spec (.of K))}
    (unit unit' : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
    (diag diag' : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) :
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
    ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ⊗
      ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
        (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ⟶
        (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
          (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X :=
  let first := fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
    (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
  let second := snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
    (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
  let unit := first ≫ fst _ _
  let diag := first ≫ snd _ _
  let unit' := second ≫ fst _ _
  let diag' := second ≫ snd _ _
  lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
    (diag * diag')

/-- The U-first twisted product diagram is an equality of represented scheme
morphisms on the product of two coordinate spaces, extending the field-base
triangular semidirect law of Milne, *Algebraic Groups* (course notes,
version 2.00), §§2.20–2.21. It does not assert that the underlying product
has the canonical direct-product group law. -/
theorem upperTriangularUFirstTwistedMul_comp_hom :
    upperTriangularUFirstTwistedMul K n ≫ (upperTriangularUFirstIso K n).hom =
      ((upperTriangularUFirstIso K n).hom ⊗ₘ
        (upperTriangularUFirstIso K n).hom) ≫
        μ[(groupScheme K n).X] := by
  let first := fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
    (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
  let second := snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
    (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
    ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X ⊗
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X)
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
    (diag : (Fin n → Rˣ)) (unit : TauCeti.upperUnitriangularGroup (Fin n) R) :
    lift (X := (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) (Y :=
      (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) ((Spec.mapMulEquiv
      ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ := ULift.{u} (Fin n))).symm
      (fun i => diag i.down))))
        ((Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A :=
          R)).symm unit))) ≫
          upperTriangularDiagonalConj K n =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm
        ((TauCeti.UpperTriangularGroup.diagonalAction (diag))
          unit))) := by
  apply (isPullback_diagonalProjection_over K n).hom_ext
  · erw [upperTriangularDiagonalConj_lift_comp_inclusion K n]
    erw [unitriangularInclusion_point K n unit]
    erw [diagonalTorus_point K n (fun i => diag i.down)]
    erw [unitriangularInclusion_point K n
      (TauCeti.UpperTriangularGroup.diagonalAction diag unit)]
    rw [TauCeti.UpperTriangularGroup.inUpperTriangular_diagonalAction]
    change _ = Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := R)).symm
      (TauCeti.UpperTriangularGroup.diagonalHom diag *
        (Subgroup.inclusion
          TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) unit *
        (TauCeti.UpperTriangularGroup.diagonalHom diag)⁻¹))
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rfl
  · exact (comp_toUnit _).trans (comp_toUnit _).symm

private theorem upperTriangularUFirstIso_lift
    {test : Over (Spec (.of K))}
    (unit : test ⟶ (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
    (diag : test ⟶ (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) :
    lift unit diag ≫ (upperTriangularUFirstIso K n).hom =
      (unit ≫ (unitriangularInclusion K n).hom.hom) *
        (diag ≫ (diagonalTorus K n).hom.hom) := by
  rw [upperTriangularUFirstIso_hom]
  simp only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]

/-- Every affine point of the U-first scheme iso is the native semidirect
factorization, over arbitrary commutative `K`-algebras. -/
theorem upperTriangularUFirstIso_point
    (unit : TauCeti.upperUnitriangularGroup (Fin n) R) (diag : (Fin n → Rˣ)) :
    lift (X := (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) (Y :=
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ((Spec.mapMulEquiv
      ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm unit)))
        ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ :=
          ULift.{u} (Fin n))).symm (fun i => diag i.down)))) ≫
          (upperTriangularUFirstIso K n).hom =
      (Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n :=
        n) (A := R)).symm (TauCeti.UpperTriangularGroup.semidirEquiv
          (⟨unit, diag⟩ :
            TauCeti.upperUnitriangularGroup (Fin n) R ⋊[TauCeti.UpperTriangularGroup.diagonalAction]
              (Fin n → Rˣ))))) := by
  erw [upperTriangularUFirstIso_lift]
  erw [unitriangularInclusion_point K n unit]
  erw [diagonalTorus_point K n (fun i => diag i.down)]
  rw [TauCeti.UpperTriangularGroup.semidirEquiv_apply]
  exact (((pointsMulEquiv (R := K) (n := n) (A := R)).symm.trans
    (Spec.mapMulEquiv (R := K) (S := coordinateHopfAlgebra K n) (T := R))).map_mul
      ((Subgroup.inclusion
        TauCeti.UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) unit)
      (TauCeti.UpperTriangularGroup.diagonalHom diag)).symm

/-- Both inverse coordinates recover the native unipotent and diagonal
factorization on every commutative coefficient algebra. -/
theorem upperTriangularUFirstIso_inv_point (matrix : TauCeti.upperTriangularGroup (Fin n) R) :
    (Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n)
      (A := R)).symm matrix)) ≫
      (upperTriangularUFirstIso K n).inv =
        lift (X := (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) (Y :=
          (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ((Spec.mapMulEquiv
          ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm
          (TauCeti.UpperTriangularGroup.unipotentPart matrix))))
          ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ :=
            ULift.{u} (Fin n))).symm (fun i => (TauCeti.UpperTriangularGroup.diag matrix) i.down))))
              := by
  have forward :
      lift (X := (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) (Y :=
        (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ((Spec.mapMulEquiv
        ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm
        (TauCeti.UpperTriangularGroup.unipotentPart matrix))))
        ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ :=
          ULift.{u} (Fin n))).symm (fun i => (TauCeti.UpperTriangularGroup.diag matrix) i.down)))) ≫
          (upperTriangularUFirstIso K n).hom =
        (Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n
          := n) (A := R)).symm matrix)) := by
    rw [upperTriangularUFirstIso_point]
    simp
    rfl
  calc
    _ = (lift (X := (TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X) (Y :=
      (TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) ((Spec.mapMulEquiv
      ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm
      (TauCeti.UpperTriangularGroup.unipotentPart matrix))))
          ((Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ :=
            ULift.{u} (Fin n))).symm (fun i => (TauCeti.UpperTriangularGroup.diag matrix)
            i.down)))) ≫
            (upperTriangularUFirstIso K n).hom) ≫
          (upperTriangularUFirstIso K n).inv := by
      rw [forward]
      rfl
    _ = _ := by erw [Category.assoc, (upperTriangularUFirstIso K n).hom_inv_id,
      Category.comp_id]

/-- The first inverse coordinate is native column-normalized unipotent part. -/
theorem upperTriangularUFirstIso_inv_fst_point (matrix : TauCeti.upperTriangularGroup (Fin n) R) :
    ((Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n :=
      n) (A := R)).symm matrix)) ≫
      (upperTriangularUFirstIso K n).inv) ≫
        fst ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) =
      (Spec.mapMulEquiv ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin n) (A := R)).symm
        (TauCeti.UpperTriangularGroup.unipotentPart matrix))) := by
  rw [upperTriangularUFirstIso_inv_point]
  exact lift_fst _ _

/-- The second inverse coordinate is the native diagonal projection. -/
theorem upperTriangularUFirstIso_inv_snd_point (matrix : TauCeti.upperTriangularGroup (Fin n) R) :
    ((Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n :=
      n) (A := R)).symm matrix)) ≫
      (upperTriangularUFirstIso K n).inv) ≫
        snd ((TauCeti.UpperUnitriangular.groupScheme K (Fin n)).X)
          ((TauCeti.SplitTorus.groupScheme K (ULift.{u} (Fin n))).X) =
      (Spec.mapMulEquiv ((TauCeti.SplitTorus.pointsMulEquiv (R := K) (A := R) (σ := ULift.{u}
        (Fin n))).symm (fun i => (TauCeti.UpperTriangularGroup.diag matrix) i.down))) := by
  rw [upperTriangularUFirstIso_inv_point]
  exact lift_snd _ _




end AlgebraicGeometry
