/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinear
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# The canonical special linear group is the determinant kernel

Tau Ceti's general Hopf-kernel theorem supplies the pullback on arbitrary test
schemes. Relabelling the infinite cyclic character group by its same-universe
lift is surjective, so it preserves the determinant kernel Hopf ideal. The
coordinate algebra and the special-linear inclusion are the canonical objects.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, VII §4, Example 4.3.
* Tau Ceti contributors, `HopfIdeal.Scheme.Kernel` and
  `CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n]

/-- The canonical same-universe determinant character has the defining SL Hopf ideal. -/
theorem generalLinearDeterminantSchemeCoordinateMap_kernel :
    TauCeti.CommHopfAlgCat.kernelHopfIdeal
      (generalLinearDeterminantSchemeCoordinateMap K n) =
        TauCeti.SpecialLinear.definingHopfIdeal K (Fintype.card n) := by
  let e := MonoidAlgebra.domCongrBialgEquiv K K
    (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ)
  have he : Function.Surjective (CommHopfAlgCat.ofHom e.toBialgHom).hom := by
    rw [CommHopfAlgCat.hom_ofHom]
    exact e.surjective
  have hmap : generalLinearDeterminantSchemeCoordinateMap K n =
      CommHopfAlgCat.ofHom e.toBialgHom ≫
        TauCeti.GeneralLinear.determinantCoordinateMap K (Fintype.card n) := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    rfl
  rw [hmap, TauCeti.CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective _ he]

/-- The special-linear square is the determinant kernel on group schemes. -/
theorem specialLinearDeterminantSquare_isPullback_group :
    IsPullback (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n))
      (0 : TauCeti.SpecialLinear.groupScheme K (Fintype.card n) ⟶
        Grp.trivial (Over (Spec (.of K))))
      (generalLinearDeterminantSchemeHom K n)
      (0 : Grp.trivial (Over (Spec (.of K))) ⟶
        TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) := by
  let P (I : TauCeti.HopfIdeal K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) : Prop :=
    IsPullback (TauCeti.CommHopfAlgCat.quotientSpecι
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) I)
      (0 : TauCeti.CommHopfAlgCat.quotientSpec
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) I ⟶
          Grp.trivial (Over (Spec (.of K))))
      ((hopfSpec (.of K)).map (generalLinearDeterminantSchemeCoordinateMap K n).op)
      (0 : Grp.trivial (Over (Spec (.of K))) ⟶
        (hopfSpec (.of K)).obj (.op (CommHopfAlgCat.of K
          (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))))))
  have h : P (TauCeti.CommHopfAlgCat.kernelHopfIdeal
      (generalLinearDeterminantSchemeCoordinateMap K n)) := by
    simpa only [P, TauCeti.CommHopfAlgCat.kernelSpecι_def]
      using TauCeti.CommHopfAlgCat.isPullback_kernelSpec
        (generalLinearDeterminantSchemeCoordinateMap K n)
  have hcanonical : P (TauCeti.SpecialLinear.definingHopfIdeal K (Fintype.card n)) :=
    (congrArg P (generalLinearDeterminantSchemeCoordinateMap_kernel K n)).mp h
  rw [TauCeti.SpecialLinear.groupSchemeι_def,
    TauCeti.CommHopfAlgCat.kernelSpecι_def]
  convert hcanonical using 1 <;> rfl

/-- Forgetting the group structure gives the kernel square on arbitrary base schemes. -/
theorem specialLinearDeterminantSquare_isPullback_over :
    IsPullback (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom
      (toUnit (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
      (generalLinearDeterminantSchemeHom K n).hom.hom
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] := by
  have h := (specialLinearDeterminantSquare_isPullback_group K n).map
    (Grp.forget (Over (Spec (.of K))))
  change IsPullback (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom
    (toUnit (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X)
    (generalLinearDeterminantSchemeHom K n).hom.hom
    (toUnit (𝟙_ (Over (Spec (.of K)))) ≫
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X]) at h
  simpa only [toUnit_unit, Category.id_comp] using h

/-- The determinant square is a pullback of underlying schemes over the base. -/
theorem specialLinearDeterminantSquare_isPullback :
    IsPullback (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom.left
      (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X.hom
      (generalLinearDeterminantSchemeHom K n).hom.hom.left
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X].left := by
  simpa only [Over.forget_map, Over.toUnit_left] using
    (specialLinearDeterminantSquare_isPullback_over K n).map
      (Over.forget (Spec (.of K)))

/-- The canonical determinant-one coordinate algebra is the ring pushout along
its character counit, including for arbitrary commutative target rings. -/
theorem specialLinearDeterminantSquare_isPushout :
    IsPushout
      (CommRingCat.ofHom
        (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom (Bialgebra.counitAlgHom K
        (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)))).toRingHom)
      (CommRingCat.ofHom
        (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom (algebraMap K
        (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)))) := by
  have h := specialLinearDeterminantSquare_isPullback K n
  simp only [TauCeti.SpecialLinear.groupSchemeι_def,
    TauCeti.CommHopfAlgCat.kernelSpecι_def, TauCeti.CommHopfAlgCat.quotientSpecι_def] at h
  change IsPullback
    (Spec.map (CommRingCat.ofHom
      (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap K
      (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)))))
    (Spec.map (CommRingCat.ofHom
      (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom.toRingHom))
    (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K
      (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)))).toRingHom)) at h
  exact (IsPullback.of_map_of_faithful Scheme.Spec h).unop.flip

/-- The kernel condition has a unique lift on every test scheme over the base. -/
theorem specialLinearSchemeKernel_universal
    (T : Over (Spec (.of K)))
    (f : T ⟶ (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X)
    (hf : f ≫ (generalLinearDeterminantSchemeHom K n).hom.hom =
      toUnit T ≫ η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X]) :
    ∃! lift : T ⟶ (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X,
      lift ≫ (TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n)).hom.hom = f := by
  let square := specialLinearDeterminantSquare_isPullback_over K n
  refine ⟨square.lift f (toUnit T) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _

/-- The kernel lift preserves group structure for every test group scheme. -/
theorem specialLinearGroupKernel_universal
    (H : Grp (Over (Spec (.of K))))
    (f : H ⟶ TauCeti.GeneralLinear.groupScheme K (Fintype.card n))
    (hf : f ≫ generalLinearDeterminantSchemeHom K n =
      toUnit H ≫ (0 : Grp.trivial (Over (Spec (.of K))) ⟶
        TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) :
    ∃! lift : H ⟶ TauCeti.SpecialLinear.groupScheme K (Fintype.card n),
      lift ≫ TauCeti.SpecialLinear.groupSchemeι K (Fintype.card n) = f := by
  let square := specialLinearDeterminantSquare_isPullback_group K n
  refine ⟨square.lift f (toUnit H) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _

end AlgebraicGeometry
