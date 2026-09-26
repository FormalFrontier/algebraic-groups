/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinear
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# The scheme-theoretic determinant-one kernel

The determinant-one affine scheme is the actual pullback of the finite GL
determinant character along the unit of the multiplicative group scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory GeneralLinearCoordinateRing
  SpecialLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

private theorem laurentCoordinateHom_ext {R : Type u} [CommRing R] [Algebra K R]
    {f g : multiplicativeGroupCoordinateRing K →ₐ[K] R}
    (h : f (multiplicativeGroupCoordinate K) = g (multiplicativeGroupCoordinate K)) :
    f = g := by
  let equivalence := multiplicativeGroupMulEquivAlgHom K R
  let unitF := equivalence.symm (WithConv.toConv f)
  let unitG := equivalence.symm (WithConv.toConv g)
  have hUnits : unitF = unitG := by
    apply Units.ext
    rw [← multiplicativeGroupMulEquivAlgHom_coordinate K R unitF,
      ← multiplicativeGroupMulEquivAlgHom_coordinate K R unitG]
    simpa [unitF, unitG, equivalence] using h
  have := congrArg (fun unit : Rˣ ↦ (equivalence unit).ofConv) hUnits
  simpa [unitF, unitG, equivalence] using this

/-- The determinant coordinate character becomes the counit after the Hopf quotient. -/
theorem specialLinearDeterminant_eq_unitCoordinate :
    (quotient K n).comp (generalLinearDeterminantCoordinateMap K n) =
      (Algebra.ofId K (SpecialLinearCoordinateRing.CoordinateRing K n)).comp
        (Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K)) := by
  apply laurentCoordinateHom_ext K
  rw [AlgHom.comp_apply, generalLinearDeterminantCoordinateMap_coordinate, quotient_det]
  change 1 = algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n)
      (Coalgebra.counit (R := K) (multiplicativeGroupCoordinate K))
  rw [multiplicativeGroupCoordinate_counit, map_one]

/-- The square of the determinant coordinate map, unit counit, and determinant-one
quotient commutes as a square of commutative rings. -/
theorem specialLinearDeterminantSquare_commutes :
    CommRingCat.ofHom (generalLinearDeterminantCoordinateMap K n).toRingHom ≫
      CommRingCat.ofHom (quotient K n).toRingHom =
      CommRingCat.ofHom
        (Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K)).toRingHom ≫
          CommRingCat.ofHom
            (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n)) := by
  apply CommRingCat.hom_ext
  change ((quotient K n).comp (generalLinearDeterminantCoordinateMap K n)).toRingHom =
    ((Algebra.ofId K (SpecialLinearCoordinateRing.CoordinateRing K n)).comp
      (Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K))).toRingHom
  exact congrArg AlgHom.toRingHom (specialLinearDeterminant_eq_unitCoordinate K n)

/-- The actual determinant-one quotient is the pushout of the published
determinant coordinate map along the multiplicative-group counit. -/
theorem specialLinearDeterminantSquare_isPushout :
    IsPushout
      (CommRingCat.ofHom (generalLinearDeterminantCoordinateMap K n).toRingHom)
      (CommRingCat.ofHom
        (Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K)).toRingHom)
      (CommRingCat.ofHom (quotient K n).toRingHom)
      (CommRingCat.ofHom
        (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n))) := by
  refine IsPushout.mk' (specialLinearDeterminantSquare_commutes K n) ?_ ?_
  · intro T phi psi hphi _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := congrArg (fun h : CommRingCat.of
        (GeneralLinearCoordinateRing.CoordinateRing K n) ⟶ T ↦ h.hom y) hphi
    exact h
  · intro T a b hcompatible
    have hdet : a.hom (matrix K n).det = 1 := by
      have h := congrArg (fun hom : CommRingCat.of (multiplicativeGroupCoordinateRing K) ⟶ T ↦
        hom.hom (multiplicativeGroupCoordinate K)) hcompatible
      change a.hom ((generalLinearDeterminantCoordinateMap K n)
        (multiplicativeGroupCoordinate K)) =
        b.hom ((Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K))
          (multiplicativeGroupCoordinate K)) at h
      rw [generalLinearDeterminantCoordinateMap_coordinate,
        Bialgebra.counitAlgHom_apply, multiplicativeGroupCoordinate_counit,
        map_one] at h
      exact h
    have hbase (r : K) : a.hom (algebraMap K
        (GeneralLinearCoordinateRing.CoordinateRing K n) r) = b.hom r := by
      have h := congrArg (fun hom : CommRingCat.of (multiplicativeGroupCoordinateRing K) ⟶ T ↦
        hom.hom (algebraMap K (multiplicativeGroupCoordinateRing K) r)) hcompatible
      change a.hom ((generalLinearDeterminantCoordinateMap K n)
        (algebraMap K (multiplicativeGroupCoordinateRing K) r)) =
        b.hom ((Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K))
          (algebraMap K (multiplicativeGroupCoordinateRing K) r)) at h
      rw [AlgHom.commutes] at h
      simpa only [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply] using h
    let lift : SpecialLinearCoordinateRing.CoordinateRing K n →+* T :=
      Ideal.Quotient.lift (determinantOneIdeal K n) a.hom (by
        intro element membership
        obtain ⟨multiplier, hmultiplier⟩ := Ideal.mem_span_singleton'.mp membership
        rw [← hmultiplier, map_mul, map_sub, map_one, hdet, sub_self, mul_zero])
    refine ⟨CommRingCat.ofHom lift, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro element
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change lift (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n) r) = b.hom r
      exact hbase r

/-- Contravariant `Spec` turns the actual coordinate pushout into the scheme
pullback of determinant along the multiplicative-group unit. -/
theorem specialLinearDeterminantSquare_isPullback :
    IsPullback (specialLinearInclusion K n).hom.hom.left
      (specialLinearGroupUnderlyingScheme K n).hom
      (generalLinearDeterminantSchemeHom K n).hom.hom.left
      η[multiplicativeGroupUnderlyingScheme K].left := by
  change IsPullback
    (Spec.map (CommRingCat.ofHom (quotient K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n))))
    (Spec.map (CommRingCat.ofHom
      (generalLinearDeterminantCoordinateMap K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom K (multiplicativeGroupCoordinateRing K)).toRingHom))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (specialLinearDeterminantSquare_isPushout K n)

/-- The determinant-one square is a pullback over the base, not merely a
pointwise kernel on affine test rings. -/
theorem specialLinearDeterminantSquare_isPullback_over :
    IsPullback (specialLinearInclusion K n).hom.hom
      (toUnit (specialLinearGroupScheme K n).toMon.X)
      (generalLinearDeterminantSchemeHom K n).hom.hom
      η[(multiplicativeGroupScheme K).toMon.X] := by
  exact IsPullback.of_map_of_faithful (F := Over.forget (Spec (.of K)))
    (specialLinearDeterminantSquare_isPullback K n)

/-- The unique group-scheme morphism to the trivial group scheme over `Spec K`. -/
def specialLinearToTrivialGroupHom :
    specialLinearGroupScheme K n ⟶ Grp.trivial (Over (Spec (.of K))) :=
  Grp.homMk' (default : (specialLinearGroupScheme K n).toMon ⟶
    Mon.trivial (Over (Spec (.of K))))

/-- The unit of `Gₘ` as an actual morphism from the trivial group scheme. -/
def multiplicativeUnitGroupHom :
    Grp.trivial (Over (Spec (.of K))) ⟶ multiplicativeGroupScheme K :=
  Grp.homMk' (0 : Mon.trivial (Over (Spec (.of K))) ⟶
    (multiplicativeGroupScheme K).toMon)

/-- The determinant-one group scheme is the categorical kernel square of the
published determinant character, for arbitrary test group schemes. -/
theorem specialLinearDeterminantSquare_isPullback_group :
    IsPullback (specialLinearInclusion K n) (specialLinearToTrivialGroupHom K n)
      (generalLinearDeterminantSchemeHom K n) (multiplicativeUnitGroupHom K) := by
  apply IsPullback.of_map_of_faithful (Grp.forget (Over (Spec (.of K))))
  change IsPullback (specialLinearInclusion K n).hom.hom
    (toUnit (specialLinearGroupScheme K n).toMon.X)
    (generalLinearDeterminantSchemeHom K n).hom.hom
    (toUnit (MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K)))) ≫
      η[(multiplicativeGroupScheme K).toMon.X])
  simpa only [toUnit_unit, Category.id_comp]
    using specialLinearDeterminantSquare_isPullback_over K n

/-- The pullback represents the determinant-one condition on *every* scheme
over `Spec K`, with no affineness or reducedness hypothesis on the test scheme. -/
theorem specialLinearSchemeKernel_universal
    (T : Over (Spec (.of K)))
    (f : T ⟶ generalLinearGroupUnderlyingScheme K n)
    (hf : f ≫ (generalLinearDeterminantSchemeHom K n).hom.hom =
      toUnit T ≫ η[(multiplicativeGroupScheme K).toMon.X]) :
    ∃! lift : T ⟶ specialLinearGroupUnderlyingScheme K n,
      lift ≫ (specialLinearInclusion K n).hom.hom = f := by
  let square := specialLinearDeterminantSquare_isPullback_over K n
  refine ⟨square.lift f (toUnit T) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _

/-- Universal property of the determinant kernel for arbitrary `K`-group
schemes: the lift is itself a group-scheme map, not merely a scheme map. -/
theorem specialLinearGroupKernel_universal
    (H : Grp (Over (Spec (.of K))))
    (f : H ⟶ generalLinearGroupScheme K n)
    (hf : f ≫ generalLinearDeterminantSchemeHom K n =
      toUnit H ≫ multiplicativeUnitGroupHom K) :
    ∃! lift : H ⟶ specialLinearGroupScheme K n,
      lift ≫ specialLinearInclusion K n = f := by
  let square := specialLinearDeterminantSquare_isPullback_group K n
  refine ⟨square.lift f (toUnit H) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _

end AlgebraicGeometry

#lint
