/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AlgebraicGroups.GroupScheme.Additive

/-!
# Private additive-group regression clients

These named, private declarations keep the original additive-group examples in
the compiled test module without exporting an additional mathematical API.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R]

private theorem testCoordinateRingFiniteType :
    Algebra.FiniteType K (additiveGroupCoordinateRing K) :=
  inferInstance

private theorem testUnderlyingSchemeLocallyFiniteType :
    LocallyOfFiniteType (additiveGroupUnderlyingScheme K).hom :=
  inferInstance

private theorem testUnderlyingSchemeQuasiCompact :
    QuasiCompact (additiveGroupUnderlyingScheme K).hom :=
  inferInstance

private def testAdditiveGroupScheme : Grp (Over (Spec (.of K))) :=
  additiveGroupScheme K

private def testPointsFunctorIso : additiveGroupFunctor K ≅ additiveGroupPointsFunctor K :=
  additiveGroupPointsIso K

private theorem testFunctorMap {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : R) :
    (additiveGroupFunctor K).map (CommAlgCat.ofHom f) (.ofAdd r) = .ofAdd (f r) :=
  rfl

private theorem testCoordinatePolynomial :
    additiveGroupCoordinateAlgEquiv K (additiveGroupCoordinate K) =
    Polynomial.X :=
  additiveGroupCoordinateAlgEquiv_coordinate K

private def testMultiplicativeAlgHomEquiv : Multiplicative R ≃*
    WithConv (additiveGroupCoordinateRing K →ₐ[K] R) :=
  additiveGroupMulEquivAlgHom K R

private theorem testCoordinateEvaluation (r : R) :
    (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv
        (additiveGroupCoordinate K) = r :=
  additiveGroupMulEquivAlgHom_coordinate K R r

private theorem testMultiplicativeHom (r s : R) :
    additiveGroupMulEquivAlgHom K R (.ofAdd (r + s)) =
      additiveGroupMulEquivAlgHom K R (.ofAdd r) *
        additiveGroupMulEquivAlgHom K R (.ofAdd s) :=
  (additiveGroupMulEquivAlgHom K R).map_mul (.ofAdd r) (.ofAdd s)

private theorem testNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : R) :
    (additiveGroupMulEquivAlgHom K S (.ofAdd (f r))).ofConv =
      f.comp (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv :=
  additiveGroupMulEquivAlgHom_naturality K R f r

private def testMultiplicativePointsEquiv : Multiplicative R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ additiveGroupUnderlyingScheme K) :=
  additiveGroupMulEquivPoints K R

private theorem testPointsApplyLeft (r : R) :
    (additiveGroupMulEquivPoints K R (.ofAdd r)).left =
      Spec.map (CommRingCat.ofHom
        (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv.toRingHom) :=
  additiveGroupMulEquivPoints_apply_left K R r

private theorem testCoordinateComul :
    CoalgebraStruct.comul (additiveGroupCoordinate K) =
      additiveGroupCoordinate K ⊗ₜ[K] 1 +
        1 ⊗ₜ[K] additiveGroupCoordinate K :=
  additiveGroupCoordinate_comul K

private theorem testCoordinateCounit :
    CoalgebraStruct.counit (R := K) (additiveGroupCoordinate K) = (0 : K) :=
  additiveGroupCoordinate_counit K

private theorem testCoordinateAntipode :
    (HopfAlgebraStruct.antipode K) (additiveGroupCoordinate K) =
      -additiveGroupCoordinate K :=
  additiveGroupCoordinate_antipode K

-- The entire API remains available when the target algebra is subsingleton.
private def testSubsingletonPointsEquiv [Subsingleton R] : Multiplicative R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ additiveGroupUnderlyingScheme K) :=
  additiveGroupMulEquivPoints K R

private def testIntegerAlgHomEquiv : Multiplicative Int ≃*
    WithConv (additiveGroupCoordinateRing Int →ₐ[Int] Int) :=
  additiveGroupMulEquivAlgHom Int Int

private def testZModTwoAlgHomEquiv : Multiplicative (ZMod 2) ≃*
    WithConv (additiveGroupCoordinateRing (ZMod 2) →ₐ[ZMod 2] ZMod 2) :=
  additiveGroupMulEquivAlgHom (ZMod 2) (ZMod 2)

private def testZModOneAlgHomEquiv : Multiplicative (ZMod 1) ≃*
    WithConv (additiveGroupCoordinateRing (ZMod 1) →ₐ[ZMod 1] ZMod 1) :=
  additiveGroupMulEquivAlgHom (ZMod 1) (ZMod 1)

end AlgebraicGeometry
