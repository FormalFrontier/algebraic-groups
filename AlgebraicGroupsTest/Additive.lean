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
    Algebra.FiniteType K ((SymmetricAlgebra K K)) :=
  inferInstance

private theorem testUnderlyingSchemeLocallyFiniteType :
    LocallyOfFiniteType ((TauCeti.AdditiveGroup.groupScheme K).X).hom :=
  inferInstance

private theorem testUnderlyingSchemeQuasiCompact :
    QuasiCompact ((TauCeti.AdditiveGroup.groupScheme K).X).hom :=
  inferInstance

private def testAdditiveGroupScheme : Grp (Over (Spec (.of K))) :=
  TauCeti.AdditiveGroup.groupScheme K

private def testPointsFunctorIso : additiveGroupFunctor K ≅
    TauCeti.GroupScheme.algebraPointsFunctor K (TauCeti.AdditiveGroup.groupScheme K) :=
  additiveGroupPointsIso K

private theorem testFunctorMap {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : R) :
    (additiveGroupFunctor K).map (CommAlgCat.ofHom f) (.ofAdd r) = .ofAdd (f r) :=
  rfl

private theorem testCoordinatePolynomial :
    additiveGroupCoordinateAlgEquiv K ((SymmetricAlgebra.ι K K 1)) =
    Polynomial.X :=
  additiveGroupCoordinateAlgEquiv_coordinate K

private def testMultiplicativeAlgHomEquiv : Multiplicative R ≃*
    WithConv ((SymmetricAlgebra K K) →ₐ[K] R) :=
  (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm

/-- The algebra map represented by an additive point sends the coordinate to that point. -/
public theorem additiveGroup_coordinate_evaluation (r : R) :
    ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd r)).ofConv
        ((SymmetricAlgebra.ι K K 1)) = r :=
  TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (.ofAdd r)

private theorem testMultiplicativeHom (r s : R) :
    (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd (r + s)) =
      (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd r) *
        (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd s) :=
  ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm).map_mul (.ofAdd r) (.ofAdd s)

private theorem testNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : R) :
    ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := S)).symm (.ofAdd (f r))).ofConv =
      f.comp ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd r)).ofConv :=
by
  apply AlgHom.ext
  intro x
  have h := congrArg (fun F => F.ofConv x)
    (TauCeti.AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply f (.ofAdd r))
  simpa only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    toAdd_ofAdd] using h.symm

private def testMultiplicativePointsEquiv : Multiplicative R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (TauCeti.AdditiveGroup.groupScheme K).X) :=
  (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm

private theorem testPointsApplyLeft (r : R) :
    ((TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm (.ofAdd r)).left =
      Spec.map (CommRingCat.ofHom
        ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K)
          (A := R)).symm (.ofAdd r)).ofConv.toRingHom) ≫
        eqToHom (TauCeti.AdditiveGroup.groupScheme_X_left K).symm := by
  rw [TauCeti.AdditiveGroup.schemePointsMulEquiv_symm_apply]
  exact TauCeti.AdditiveGroup.groupSchemePointMulEquiv_apply_left (R := K) R
    ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm (.ofAdd r))

private theorem testCoordinateComul :
    CoalgebraStruct.comul ((SymmetricAlgebra.ι K K 1)) =
      (SymmetricAlgebra.ι K K 1) ⊗ₜ[K] 1 +
        1 ⊗ₜ[K] (SymmetricAlgebra.ι K K 1) :=
  SymmetricAlgebra.comul_ι K K 1

private theorem testCoordinateCounit :
    CoalgebraStruct.counit (R := K) ((SymmetricAlgebra.ι K K 1)) = (0 : K) :=
  SymmetricAlgebra.counit_ι K K 1

private theorem testCoordinateAntipode :
    (HopfAlgebraStruct.antipode K) ((SymmetricAlgebra.ι K K 1)) =
      -(SymmetricAlgebra.ι K K 1) :=
  TauCeti.SymmetricAlgebra.antipode_ι K K 1

-- The entire API remains available when the target algebra is subsingleton.
private def testSubsingletonPointsEquiv : Multiplicative R ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (TauCeti.AdditiveGroup.groupScheme K).X) :=
  (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm

private def testIntegerAlgHomEquiv : Multiplicative Int ≃*
    WithConv ((SymmetricAlgebra Int Int) →ₐ[Int] Int) :=
  (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := Int) (A := Int)).symm

private def testZModTwoAlgHomEquiv : Multiplicative (ZMod 2) ≃*
    WithConv ((SymmetricAlgebra (ZMod 2) (ZMod 2)) →ₐ[ZMod 2] ZMod 2) :=
  (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := (ZMod 2)) (A := (ZMod 2))).symm

private def testZModOneAlgHomEquiv : Multiplicative (ZMod 1) ≃*
    WithConv ((SymmetricAlgebra (ZMod 1) (ZMod 1)) →ₐ[ZMod 1] ZMod 1) :=
  (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := (ZMod 1)) (A := (ZMod 1))).symm

-- The group-object instance is the projection from the bundled additive group.
private theorem testAdditiveGroupSeparated (k : Type u) [Field k] :
    IsSeparated (TauCeti.AdditiveGroup.groupScheme k).X.hom :=
  isSeparated_of_grpObj_of_subsingleton (TauCeti.AdditiveGroup.groupScheme k).X

private theorem testAdditiveGroupDistinctPoints (k : Type u) [Field k] :
    (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := k) k).symm (.ofAdd 0) ≠
      (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := k) k).symm (.ofAdd 1) := by
  intro h
  exact (zero_ne_one : (0 : k) ≠ 1) (congrArg Multiplicative.toAdd
    (((TauCeti.AdditiveGroup.schemePointsMulEquiv (R := k) k).symm).injective h))

-- The target need not carry a group structure, nor the map respect multiplication.
private theorem testAdditiveGroupMorphismSeparated (k : Type u) [Field k]
    {X : Over (Spec (.of k))} (f : (TauCeti.AdditiveGroup.groupScheme k).X ⟶ X) :
    IsSeparated f.left := by
  have : IsSeparated (f.left ≫ X.hom) := by
    rw [Over.w f]
    exact isSeparated_of_grpObj_of_subsingleton (TauCeti.AdditiveGroup.groupScheme k).X
  exact IsSeparated.of_comp f.left X.hom

private theorem testEmptyBaseGroupSeparated :
    IsSeparated (𝟙_ (Over (Spec (.of PUnit.{u + 1})))).hom :=
  isSeparated_of_grpObj_of_subsingleton _

end AlgebraicGeometry
