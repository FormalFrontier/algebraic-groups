/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageKernel
public import AlgebraicGroups.Algebra.UnitriangularStagePolynomial
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Data.ZMod.Basic

/-!
# Clients of unitriangular stage factorization and kernels

These examples instantiate the positive-stage over-scheme pullback square at
rank three and at degenerate ranks and bases, including the empty product.
Over the rationals, the rank-two zero-stage factorization is an isomorphism
boundary with two distinct points, whereas the rank-three second stage is a
proper closed successor with a nonzero central coordinate.
-/

@[expose] public section

noncomputable section

open UnitriangularStageCoordinateRing
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

variable (K : Type) [CommRing K]

example : IsPullback (unitriangularStageSuccessor K 3 1).hom.hom
    (toUnit (unitriangularStageScheme K 3 2).toMon.X)
    (unitriangularStageCoordinateMap K 3 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 3 1 =>
      TauCeti.AdditiveGroup.groupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 3 1 (by omega)

example {T : Over (Spec (.of K))}
    (first second : T ⟶ (unitriangularStageScheme K 3 2).toMon.X)
    (hsame : first ≫ (unitriangularStageSuccessor K 3 1).hom.hom =
      second ≫ (unitriangularStageSuccessor K 3 1).hom.hom) : first = second := by
  apply (unitriangularStageCoordinateMap_isPullback K 3 1 (by omega)).hom_ext hsame
  exact toUnit_unique _ _

example : IsPullback (unitriangularStageSuccessor K 0 1).hom.hom
    (toUnit (unitriangularStageScheme K 0 2).toMon.X)
    (unitriangularStageCoordinateMap K 0 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 0 1 =>
      TauCeti.AdditiveGroup.groupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 0 1 (by omega)

example : IsPullback (unitriangularStageSuccessor K 1 1).hom.hom
    (toUnit (unitriangularStageScheme K 1 2).toMon.X)
    (unitriangularStageCoordinateMap K 1 1 (by omega)).hom.hom
    η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 1 1 =>
      TauCeti.AdditiveGroup.groupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 1 1 (by omega)

example : IsPullback (unitriangularStageSuccessor K 3 3).hom.hom
    (toUnit (unitriangularStageScheme K 3 4).toMon.X)
    (unitriangularStageCoordinateMap K 3 3 (by omega)).hom.hom
    η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 3 3 =>
      TauCeti.AdditiveGroup.groupScheme K).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback K 3 3 (by omega)

example : IsPullback (unitriangularStageSuccessor (ZMod 1) 0 2).hom.hom
    (toUnit (unitriangularStageScheme (ZMod 1) 0 3).toMon.X)
    (unitriangularStageCoordinateMap (ZMod 1) 0 2 (by omega)).hom.hom
    η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 0 2 =>
      TauCeti.AdditiveGroup.groupScheme (ZMod 1)).toMon.X)] :=
  unitriangularStageCoordinateMap_isPullback (ZMod 1) 0 2 (by omega)

private def rankTwoEvaluation (q : ℚ) : CoordinateRing ℚ 2 0 →ₐ[ℚ] ℚ :=
  (MvPolynomial.aeval (fun _ : SurvivingPair 2 0 => q)).comp
    (polynomialEquiv ℚ 2 0).toAlgHom

private theorem rankTwoEvaluation_entry (q : ℚ) :
    rankTwoEvaluation q (quotient ℚ 2 0 (entry ℚ 2 0 1)) = q := by
  change MvPolynomial.aeval (fun _ : SurvivingPair 2 0 => q)
    (polynomialEquiv ℚ 2 0 (quotient ℚ 2 0 (entry ℚ 2 0 1))) = q
  rw [polynomialEquiv_surviving ℚ 2 0
    (⟨⟨(0, 1), by decide⟩, by decide⟩ : SurvivingPair 2 0), MvPolynomial.aeval_X]

private def rankTwoPoint (q : ℚ) :
    Spec (.of ℚ) ⟶ Spec (.of (CoordinateRing ℚ 2 0)) :=
  Spec.map (CommRingCat.ofHom (rankTwoEvaluation q).toRingHom)

example : rankTwoPoint 1 ≠ rankTwoPoint 0 := by
  intro heq
  have h := Spec.map_injective heq
  have hentry := congrArg
    (fun f : CommRingCat.of (CoordinateRing ℚ 2 0) ⟶ CommRingCat.of ℚ =>
      f.hom (quotient ℚ 2 0 (entry ℚ 2 0 1))) h
  change rankTwoEvaluation 1 (quotient ℚ 2 0 (entry ℚ 2 0 1)) =
    rankTwoEvaluation 0 (quotient ℚ 2 0 (entry ℚ 2 0 1)) at hentry
  rw [rankTwoEvaluation_entry, rankTwoEvaluation_entry] at hentry
  exact one_ne_zero hentry

example : quotient ℚ 2 0 (entry ℚ 2 0 1) ≠ 0 := by
  intro hzero
  have h := congrArg (rankTwoEvaluation 1) hzero
  rw [rankTwoEvaluation_entry, map_zero] at h
  exact one_ne_zero h

example : Nonempty (Spec (.of (CoordinateRing ℚ 2 0))) := by
  let : Nontrivial (CoordinateRing ℚ 2 0) :=
    (rankTwoEvaluation 1).toRingHom.domain_nontrivial
  infer_instance

example : Nonempty (TauCeti.UpperUnitriangularGroup.superdiagonalIndex 2 0) :=
  ⟨⟨(0, 0), by decide⟩⟩

example : IsIso (unitriangularStageSuccessor ℚ 2 0).hom.hom.left := by
  rw [unitriangularStageSuccessor_left]
  apply isIso_SpecMap_iff.mpr
  let h : ideal ℚ 2 0 = ideal ℚ 2 (0 + 1) :=
    (ideal_zero ℚ 2).trans (ideal_one ℚ 2).symm
  change Function.Bijective (successor ℚ 2 0)
  have heq : successor ℚ 2 0 = (Ideal.quotientEquivAlgOfEq ℚ h).toAlgHom :=
    (Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ ℚ h).symm
  rw [heq]
  exact (Ideal.quotientEquivAlgOfEq ℚ h).bijective

example : ∃! g : Spec (.of (CoordinateRing ℚ 2 0)) ⟶
    Spec (.of (CoordinateRing ℚ 2 1)),
    g ≫ (unitriangularStageSuccessor ℚ 2 0).hom.hom.left =
      𝟙 (Spec (.of (CoordinateRing ℚ 2 0))) := by
  apply unitriangularStageSuccessor_existsUnique_of_coordinates ℚ 2 0
  intro ij hij
  have hgap := ij.2
  change ij.1.1.val < ij.1.2.val at hij
  omega

private def centralEvaluation : CoordinateRing ℚ 3 2 →ₐ[ℚ] ℚ :=
  (MvPolynomial.aeval (fun _ : SurvivingPair 3 2 => (1 : ℚ))).comp
    (polynomialEquiv ℚ 3 2).toAlgHom

private theorem centralEvaluation_entry :
    centralEvaluation (quotient ℚ 3 2 (entry ℚ 3 0 2)) = 1 := by
  change MvPolynomial.aeval (fun _ : SurvivingPair 3 2 => (1 : ℚ))
    (polynomialEquiv ℚ 3 2 (quotient ℚ 3 2 (entry ℚ 3 0 2))) = 1
  rw [polynomialEquiv_surviving ℚ 3 2
    (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2), MvPolynomial.aeval_X]

example : quotient ℚ 3 2 (entry ℚ 3 0 2) ≠ 0 := by
  intro hzero
  have h := congrArg centralEvaluation hzero
  rw [centralEvaluation_entry, map_zero] at h
  exact one_ne_zero h

example : Nonempty (Spec (.of (CoordinateRing ℚ 3 2))) := by
  let : Nontrivial (CoordinateRing ℚ 3 2) := centralEvaluation.toRingHom.domain_nontrivial
  infer_instance

example : Spec (.of ℚ) ⟶ Spec (.of (CoordinateRing ℚ 3 2)) :=
  Spec.map (CommRingCat.ofHom centralEvaluation.toRingHom)

/-- The rational central stage has a unique self-factorization through its
closed successor into the first stage. -/
theorem unitriangularStageSuccessor_rat_three_factorization :
    ∃! g : Spec (.of (CoordinateRing ℚ 3 2)) ⟶ Spec (.of (CoordinateRing ℚ 3 2)),
      g ≫ (unitriangularStageSuccessor ℚ 3 1).hom.hom.left =
        (unitriangularStageSuccessor ℚ 3 1).hom.hom.left := by
  apply unitriangularStageSuccessor_existsUnique_of_coordinates ℚ 3 1
  intro ij _
  rw [unitriangularStageSuccessor_left, ← Scheme.ΓSpecIso_inv_naturality]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  change (Scheme.ΓSpecIso (.of (CoordinateRing ℚ 3 2))).inv.hom
    ((successor ℚ 3 1) (coordinate ℚ 3 1 ij)) = 0
  rw [successor_coordinate ℚ 3 1 (by decide) ij, map_zero]

example (g : Spec (.of (CoordinateRing ℚ 3 2)) ⟶ Spec (.of (CoordinateRing ℚ 3 2))) :
    g ≫ (unitriangularStageSuccessor ℚ 3 1).hom.hom.left =
      (unitriangularStageSuccessor ℚ 3 1).hom.hom.left ↔ g = 𝟙 _ := by
  constructor
  · intro hg
    obtain ⟨factor, _, hunique⟩ := unitriangularStageSuccessor_rat_three_factorization
    exact (hunique g hg).trans (hunique (𝟙 _) (Category.id_comp _)).symm
  · rintro rfl
    exact Category.id_comp _

example : IsClosedImmersion (unitriangularStageSuccessor ℚ 3 1).hom.hom.left :=
  unitriangularStageSuccessor_isClosedImmersion ℚ 3 1

example : ¬ IsIso (unitriangularStageSuccessor ℚ 3 1).hom.hom.left := by
  intro hIso
  rw [unitriangularStageSuccessor_left] at hIso
  have hinjective := (isIso_SpecMap_iff.mp hIso).injective
  let ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex 3 1 := ⟨(0, 1), by decide⟩
  have hzero : coordinate ℚ 3 1 ij = 0 :=
    hinjective ((successor_coordinate ℚ 3 1 (by decide) ij).trans (map_zero _).symm)
  have h := congrArg (polynomialEquiv ℚ 3 1) hzero
  change polynomialEquiv ℚ 3 1 (quotient ℚ 3 1 (entry ℚ 3 0 1)) =
    polynomialEquiv ℚ 3 1 0 at h
  rw [polynomialEquiv_surviving ℚ 3 1
    (⟨⟨(0, 1), by decide⟩, by decide⟩ : SurvivingPair 3 1), map_zero] at h
  exact MvPolynomial.X_ne_zero _ h

end AlgebraicGeometry
