/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.Multiplicative
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Determinant

/-!
# The determinant character on the canonical general linear group scheme

The determinant Hopf morphism is supplied by Tau Ceti. The canonical
multiplicative group uses the same-universe lift of the infinite cyclic
character group, so its determinant morphism precomposes the existing
coordinate map with the existing character relabelling map.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, VII §4, Example 4.3.
* Tau Ceti contributors, `GeneralLinear.Determinant` and
  `DiagonalizableGroup.Scheme.Points`.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant coordinate morphism with the canonical same-universe
multiplicative character group as source. -/
def generalLinearDeterminantSchemeCoordinateMap :
    CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) ⟶
      TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) :=
  CommHopfAlgCat.ofHom
    ((TauCeti.GeneralLinear.determinantCoordinateMap K (Fintype.card n)).hom.comp
      (MonoidAlgebra.mapDomainBialgHom K
        (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom))

/-- The determinant character between the canonical general linear and
multiplicative group schemes, including the empty matrix index type. -/
def generalLinearDeterminantSchemeHom :
    TauCeti.GeneralLinear.groupScheme K (Fintype.card n) ⟶
      TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K := by
  change (hopfSpec (.of K)).obj
      (.op (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) ⟶
    (hopfSpec (.of K)).obj
      (.op (CommHopfAlgCat.of K (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)))))
  exact (hopfSpec (.of K)).map (.op (generalLinearDeterminantSchemeCoordinateMap K n))

omit [DecidableEq n] in
/-- The determinant scheme morphism is induced contravariantly by its canonical coordinate map. -/
@[simp]
theorem generalLinearDeterminantSchemeHom_left :
    (generalLinearDeterminantSchemeHom K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom.toRingHom) := rfl


/-- Relabelling the generic matrix does not change its determinant character. -/
theorem generalLinearReindexedGenericMatrix_det :
    (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det =
      (TauCeti.GeneralLinear.determinantGroupLike K (Fintype.card n) :
        TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) := by
  have hmatrix : TauCeti.GeneralLinear.genericMatrix K (Fintype.card n) =
      (TauCeti.GeneralLinear.localizedGenericMatrix K (Fintype.card n)).map
        (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)) := by
    ext i j
    simp only [TauCeti.GeneralLinear.genericMatrix_apply, Matrix.map_apply,
      TauCeti.GeneralLinear.localizedGenericMatrix_apply]
  rw [TauCeti.GeneralLinear.reindexedGenericMatrix, Matrix.det_reindex_self, hmatrix,
    ← AlgEquiv.mapMatrix_apply, ← AlgEquiv.map_det,
    TauCeti.GeneralLinear.determinantGroupLike_val]

/-- The lifted standard character pulls back to the generic determinant. -/
@[simp]
theorem generalLinearDeterminantSchemeCoordinateMap_generator :
    (generalLinearDeterminantSchemeCoordinateMap K n).hom
      (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1) =
        (TauCeti.GeneralLinear.reindexedGenericMatrix K n).det := by
  rw [generalLinearDeterminantSchemeCoordinateMap, CommHopfAlgCat.hom_ofHom,
    BialgHom.comp_apply, MonoidAlgebra.mapDomainBialgHom_single]
  change (TauCeti.GeneralLinear.determinantCoordinateMap K (Fintype.card n)).hom
    (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1) = _
  rw [TauCeti.GeneralLinear.determinantCoordinateMap_ofAdd_one,
    generalLinearReindexedGenericMatrix_det, TauCeti.GeneralLinear.determinantGroupLike_val]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The canonical determinant character sends every affine GL point to its
unit-valued determinant. -/
theorem generalLinearDeterminant_point (g : Matrix.GeneralLinearGroup n R) :
    TauCeti.GeneralLinear.groupSchemePointMulEquiv (Fintype.card n) R
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
    (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := K) (A := R)).symm (Matrix.GeneralLinearGroup.det g) := by
  let q : WithConv (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ)) →ₐ[K] R) :=
    WithConv.toConv (((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g).ofConv.comp
      (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom)
  have hp : TauCeti.GeneralLinear.groupSchemePointMulEquiv (Fintype.card n) R
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g) ≫
      (generalLinearDeterminantSchemeHom K n).hom.hom =
      (TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := K) (A := R) TauCeti.DiagonalizableGroup.multiplicativeCharacterGroup).symm q := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, TauCeti.GeneralLinear.groupSchemePointMulEquiv_apply_left,
      generalLinearDeterminantSchemeHom_left,
      TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_symm_apply_left]
    change Spec.map (CommRingCat.ofHom
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom q.ofConv.toRingHom)
    rw [← Spec.map_comp]
    rfl
  apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
    (R := K) (A := R)).injective
  rw [MulEquiv.apply_symm_apply, hp,
    TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe]
  change ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm g).ofConv
      ((generalLinearDeterminantSchemeCoordinateMap K n).hom.toAlgHom
        (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (1 : ℤ))) 1)) = _
  erw [generalLinearDeterminantSchemeCoordinateMap_generator,
    TauCeti.GeneralLinear.reindexedPointsMulEquiv_symm_apply_det]
  rfl

/-- The unit-valued determinant is natural in the coefficient algebra. -/
def generalLinearDeterminantFunctorHom :
    generalLinearIndexedFunctor K n ⟶ multiplicativeGroupFunctor K where
  app R := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact Matrix.GeneralLinearGroup.map_det f.hom.toRingHom g

end AlgebraicGeometry
