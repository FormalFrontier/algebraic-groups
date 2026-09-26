/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
import Mathlib.Data.ZMod.Basic

/-!
# Infinitesimal additive group regression checks

Named private declarations retain the original examples in the compiled test
without adding to the public mathematical API.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
  (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

private theorem testIdealIsHopfIdeal : Ideal.IsHopfIdeal K (infinitesimalAdditiveIdeal K p m) := inferInstance

@[instance_reducible] private def testCoordinateRingHopfAlgebra : HopfAlgebra K (infinitesimalAdditiveCoordinateRing K p m) := inferInstance

/-- Compare the whole stored structure with the original instance-valued expression. -/
private theorem testCoordinateRingHopfAlgebra_original
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ) :
    testCoordinateRingHopfAlgebra K p m =
      (inferInstance : HopfAlgebra K (infinitesimalAdditiveCoordinateRing K p m)) := by
  rfl

omit [Fact p.Prime] [CharP K p] in
private theorem testCoordinateRingFiniteType :
    Algebra.FiniteType K (infinitesimalAdditiveCoordinateRing K p m) :=
  infinitesimalAdditiveCoordinateRing_finiteType K p m

omit [Fact p.Prime] [CharP K p] in
private theorem testUnderlyingSchemeLocallyFiniteType :
    LocallyOfFiniteType (infinitesimalAdditiveUnderlyingScheme K p m).hom :=
  inferInstance

omit [Fact p.Prime] [CharP K p] in
private theorem testUnderlyingSchemeQuasiCompact :
    QuasiCompact (infinitesimalAdditiveUnderlyingScheme K p m).hom :=
  inferInstance

private def testGroupScheme : Grp (Over (Spec (.of K))) := infinitesimalAdditiveGroupScheme K p m

omit [Fact p.Prime] [CharP K p] in
private theorem testCoordinatePow :
    infinitesimalAdditiveCoordinate K p m ^ (p ^ m) = 0 :=
  infinitesimalAdditiveCoordinate_pow K p m

private theorem testCoordinateComul : CoalgebraStruct.comul (infinitesimalAdditiveCoordinate K p m) =
    infinitesimalAdditiveCoordinate K p m ⊗ₜ[K] 1 +
      1 ⊗ₜ[K] infinitesimalAdditiveCoordinate K p m :=
  infinitesimalAdditiveCoordinate_comul K p m

private theorem testCoordinateCounit : CoalgebraStruct.counit (R := K) (infinitesimalAdditiveCoordinate K p m) = 0 :=
  infinitesimalAdditiveCoordinate_counit K p m

private theorem testCoordinateAntipode : (HopfAlgebraStruct.antipode K) (infinitesimalAdditiveCoordinate K p m) =
    -infinitesimalAdditiveCoordinate K p m :=
  infinitesimalAdditiveCoordinate_antipode K p m

private def testSubgroupElement (r : R) (hr : r ^ (p ^ m) = 0) :
    infinitesimalAdditiveSubgroup K p m R := ⟨r, hr⟩

private theorem testAlgHomCoordinate (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv
      (infinitesimalAdditiveCoordinate K p m) = r.val :=
  infinitesimalAdditiveMulEquivAlgHom_coordinate K p m R r

private theorem testAlgHomSymmCoordinate (f : WithConv (infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R)) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R).symm f).toAdd.val =
      f.ofConv (infinitesimalAdditiveCoordinate K p m) :=
  infinitesimalAdditiveMulEquivAlgHom_symm_coordinate K p m R f

private theorem testAlgHomApplySymmApply (f : WithConv (infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R)) :
    infinitesimalAdditiveMulEquivAlgHom K p m R
        ((infinitesimalAdditiveMulEquivAlgHom K p m R).symm f) = f :=
  (infinitesimalAdditiveMulEquivAlgHom K p m R).apply_symm_apply f

private theorem testConvolutionCoordinate (r s : infinitesimalAdditiveSubgroup K p m R) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r) *
      infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd s)).ofConv
        (infinitesimalAdditiveCoordinate K p m)) = r.val + s.val :=
  infinitesimalAdditiveConvolution_coordinate K p m R r s

private theorem testAlgHomAddition (r s : infinitesimalAdditiveSubgroup K p m R) :
    infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd (r + s)) =
      infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r) *
        infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd s) :=
  infinitesimalAdditiveMulEquivAlgHom_add K p m R r s

private theorem testAlgHomNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivAlgHom K p m S
      (.ofAdd (infinitesimalAdditiveMap K p m R f r))).ofConv =
        f.comp (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv :=
  infinitesimalAdditiveMulEquivAlgHom_naturality K p m R f r

private def testPointsFunctorIso : infinitesimalAdditiveFunctor K p m ≅ infinitesimalAdditivePointsFunctor K p m :=
  infinitesimalAdditivePointsIso K p m

private def testPointsEquiv : Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (infinitesimalAdditiveGroupScheme K p m).X) :=
  infinitesimalAdditiveMulEquivPoints K p m R

private theorem testPointsApplyLeft (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivPoints K p m R (.ofAdd r)).left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv.toRingHom) :=
  infinitesimalAdditiveMulEquivPoints_apply_left K p m R r

private theorem testPointsSymmCoordinate (f : (Spec (.of R)).asOver (Spec (.of K)) ⟶
    (infinitesimalAdditiveGroupScheme K p m).X) :
    ((infinitesimalAdditiveMulEquivPoints K p m R).symm f).toAdd.val =
      ((Spec.mapMulEquiv (R := K) (S := infinitesimalAdditiveCoordinateRing K p m)
        (T := R)).symm f).ofConv (infinitesimalAdditiveCoordinate K p m) :=
  infinitesimalAdditiveMulEquivPoints_symm_coordinate K p m R f

private theorem testSubgroupZeroBot : infinitesimalAdditiveSubgroup K p 0 R = ⊥ :=
  infinitesimalAdditiveSubgroup_zero_eq_bot K p R

private theorem testSubgroupZeroElement (r : infinitesimalAdditiveSubgroup K p 0 R) : r = 0 :=
  infinitesimalAdditiveSubgroup_zero_eq_zero K p R r

omit [Fact p.Prime] [CharP K p] in
private theorem testCoordinateFirstPower :
    infinitesimalAdditiveCoordinate K p 0 = 0 := by
  simpa using infinitesimalAdditiveCoordinate_pow K p 0

private theorem testZModTwoCoordinatePow : infinitesimalAdditiveCoordinate (ZMod 2) 2 1 ^ (2 ^ 1) = 0 :=
  infinitesimalAdditiveCoordinate_pow (ZMod 2) 2 1

private theorem testZModThreeCoordinatePow : infinitesimalAdditiveCoordinate (ZMod 3) 3 2 ^ (3 ^ 2) = 0 :=
  infinitesimalAdditiveCoordinate_pow (ZMod 3) 3 2

private theorem testPolynomialCoordinatePow : infinitesimalAdditiveCoordinate (Polynomial (ZMod 2)) 2 2 ^ (2 ^ 2) = 0 :=
  infinitesimalAdditiveCoordinate_pow (Polynomial (ZMod 2)) 2 2

@[instance_reducible] private def testPolynomialHopfAlgebra : HopfAlgebra (Polynomial (ZMod 2))
    (infinitesimalAdditiveCoordinateRing (Polynomial (ZMod 2)) 2 2) := inferInstance

/-- Compare all fields of the polynomial-base Hopf structure in this module's instance context. -/
private theorem testPolynomialHopfAlgebra_original :
    testPolynomialHopfAlgebra =
      (inferInstance : HopfAlgebra (Polynomial (ZMod 2))
        (infinitesimalAdditiveCoordinateRing (Polynomial (ZMod 2)) 2 2)) := by
  rfl

/- Keep the original subsingleton-context regressions: these general equivalences
do not need `[Subsingleton R]`, but removing it would change the tested statements.
Only these two declarations are exempt from `unusedArguments`. -/
@[nolint unusedArguments]
private def testSubsingletonAlgHomEquiv [Subsingleton R] : Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
    WithConv (infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R) :=
  infinitesimalAdditiveMulEquivAlgHom K p m R

@[nolint unusedArguments]
private def testSubsingletonPointsEquiv [Subsingleton R] : Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (infinitesimalAdditiveGroupScheme K p m).X) :=
  infinitesimalAdditiveMulEquivPoints K p m R

private def testZeroTargetAlgHomEquiv : Multiplicative (infinitesimalAdditiveSubgroup (ZMod 2) 2 1 PUnit) ≃*
    WithConv (infinitesimalAdditiveCoordinateRing (ZMod 2) 2 1 →ₐ[ZMod 2] PUnit) :=
  infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 1 PUnit

/-- Compare the whole zero-target equivalence with its original literal right-hand side. -/
private theorem testZeroTargetAlgHomEquiv_original :
    testZeroTargetAlgHomEquiv =
      (infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 1 PUnit :
        Multiplicative (infinitesimalAdditiveSubgroup (ZMod 2) 2 1 PUnit) ≃*
          WithConv (infinitesimalAdditiveCoordinateRing (ZMod 2) 2 1 →ₐ[ZMod 2] PUnit)) := by
  rfl

private def testZeroTargetPointsEquiv : Multiplicative (infinitesimalAdditiveSubgroup (ZMod 3) 3 2 PUnit) ≃*
    ((Spec (.of PUnit)).asOver (Spec (.of (ZMod 3))) ⟶
      (infinitesimalAdditiveGroupScheme (ZMod 3) 3 2).X) :=
  infinitesimalAdditiveMulEquivPoints (ZMod 3) 3 2 PUnit

/-- Compare the whole zero-target points equivalence, including dependent and computational data. -/
private theorem testZeroTargetPointsEquiv_original :
    testZeroTargetPointsEquiv =
      (infinitesimalAdditiveMulEquivPoints (ZMod 3) 3 2 PUnit :
        Multiplicative (infinitesimalAdditiveSubgroup (ZMod 3) 3 2 PUnit) ≃*
          ((Spec (.of PUnit)).asOver (Spec (.of (ZMod 3))) ⟶
            (infinitesimalAdditiveGroupScheme (ZMod 3) 3 2).X)) := by
  rfl

private theorem zero_target_coordinate_test
    (r : infinitesimalAdditiveSubgroup (ZMod 2) 2 1 PUnit) :
    (infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 1 PUnit (.ofAdd r)).ofConv
      (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) = r.val :=
  infinitesimalAdditiveMulEquivAlgHom_coordinate (ZMod 2) 2 1 PUnit r

private theorem first_power_coordinate_test
    (r : infinitesimalAdditiveSubgroup K p 0 R) :
    (infinitesimalAdditiveMulEquivAlgHom K p 0 R (.ofAdd r)).ofConv
      (infinitesimalAdditiveCoordinate K p 0) = 0 := by
  rw [infinitesimalAdditiveMulEquivAlgHom_coordinate]
  exact congrArg Subtype.val (infinitesimalAdditiveSubgroup_zero_eq_zero K p R r)

#print axioms zero_target_coordinate_test
#print axioms first_power_coordinate_test

end AlgebraicGeometry

#print axioms Bialgebra.IsPrimitiveElem.isHopfIdeal_span_pow_char_pow
#print axioms Bialgebra.Quotient.comul_mk
#print axioms Bialgebra.Quotient.counit_mk
#print axioms HopfAlgebra.Quotient.antipode_mk
#print axioms HopfAlgebra.Quotient.instQuotientIdeal
#print axioms AlgHom.convMul_comp_bialgHom_distrib
#print axioms CharP.cast_eq_zero
#print axioms Ideal.mem_span_singleton'
#print axioms Ideal.Quotient.eq_zero_iff_mem
#print axioms Ideal.Quotient.liftₐ
#print axioms Ideal.Quotient.algHom_ext
#print axioms AlgebraicGeometry.additiveGroupMulEquivAlgHom
#print axioms AlgebraicGeometry.additiveGroupMulEquivAlgHom_coordinate
#print axioms AlgebraicGeometry.additiveGroupMulEquivAlgHom_naturality
#print axioms AlgebraicGeometry.additiveGroupCoordinate_comul
#print axioms AlgebraicGeometry.additiveGroupCoordinate_counit
#print axioms AlgebraicGeometry.additiveGroupCoordinate_antipode
#print axioms AlgebraicGeometry.Spec.mapMulEquiv
