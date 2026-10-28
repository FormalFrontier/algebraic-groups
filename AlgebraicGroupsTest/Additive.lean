/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.GroupScheme.Additive
import AlgebraicGroups.Examples.UnitStalkDimension
public import AlgebraicGroups.GroupScheme.Separated
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Additive-group regression clients

The coordinate-evaluation test records the value of the additive coordinate.
The remaining clients are private and include zero-ring targets. Over every
field, the bundled additive group is separated and has distinct zero and one
points. Arbitrary over-maps from it use separatedness of the structural map;
the tensor-unit group over the empty base gives a boundary case.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
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

/-- The algebra map represented by an additive point sends the coordinate to that point. -/
public theorem additiveGroup_coordinate_evaluation (r : R) :
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

-- The points API needs no nontriviality assumption on the target algebra.
private def testSubsingletonPointsEquiv : Multiplicative R ≃*
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

-- The group-object instance is the projection from the bundled additive group.
private theorem testAdditiveGroupSeparated (k : Type u) [Field k] :
    IsSeparated (additiveGroupScheme k).X.hom :=
  isSeparated_of_grpObj_of_subsingleton (additiveGroupScheme k).X

private theorem testAdditiveGroupDistinctPoints (k : Type u) [Field k] :
    additiveGroupMulEquivPoints k k (.ofAdd 0) ≠
      additiveGroupMulEquivPoints k k (.ofAdd 1) := by
  intro h
  exact (zero_ne_one : (0 : k) ≠ 1) (congrArg Multiplicative.toAdd
    ((additiveGroupMulEquivPoints k k).injective h))

-- The target need not carry a group structure, nor the map respect multiplication.
private theorem testAdditiveGroupMorphismSeparated (k : Type u) [Field k]
    {X : Over (Spec (.of k))} (f : (additiveGroupScheme k).X ⟶ X) :
    IsSeparated f.left := by
  have : IsSeparated (f.left ≫ X.hom) := by
    rw [Over.w f]
    exact isSeparated_of_grpObj_of_subsingleton (additiveGroupScheme k).X
  exact IsSeparated.of_comp f.left X.hom

private theorem testEmptyBaseGroupSeparated :
    IsSeparated (𝟙_ (Over (Spec (.of PUnit.{u + 1})))).hom :=
  isSeparated_of_grpObj_of_subsingleton _

end AlgebraicGeometry
