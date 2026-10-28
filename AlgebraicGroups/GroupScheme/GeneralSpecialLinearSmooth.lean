/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinear
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth

/-!
# Smoothness of finite general and special linear group schemes

The general linear coordinate algebra is a determinant localization of a finite
polynomial algebra. For a nonempty index type, multiplying its universal matrix
by a one-pivot diagonal matrix with inverse determinant gives a determinant-one
matrix. Evaluating the native special linear quotient at this matrix splits the
quotient as an algebra map (not as a Hopf-algebra map). Formal smoothness descends
along this retraction; finite presentation follows from the principal quotient.
For empty indices the determinant is one and the special linear quotient is
already isomorphic to the general linear coordinate algebra. No nonzero-ring or
rank hypothesis is needed for either result.

## References

* The Stacks Project, Tags 022W and 022X: finite positive-size `GL` as a
  determinant localization and the determinant group-scheme morphism.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), VII §4,
  Example 4.3 and XIII §3, item 3.14: the field-base `SL` quotient and a
  right-diagonal determinant section over all coefficient algebras. Here the
  normalization instead multiplies on the left, at a chosen pivot; the
  smoothness proof also covers empty indices and the zero ring.
* Mathlib, `RingTheory/Smooth/Basic`, `RingTheory/FinitePresentation` and
  `AlgebraicGeometry/Morphisms/Smooth`: square-zero lifting, finite
  presentation and the affine `Spec` smoothness criterion. The diagonal map
  reuses this library's determinant-section construction, which follows
  mathlib's `Matrix.GeneralLinearGroup.det_surjective`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TauCeti.GeneralLinear SpecialLinearCoordinateRing

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Normalize the universal GL matrix to determinant one by left multiplication
with the chosen one-pivot diagonal matrix. The diagonal construction follows
mathlib's `Matrix.GeneralLinearGroup.det_surjective`; compare Milne,
*Basic Theory of Affine Group Schemes*, XIII §3, item 3.14, which gives a
right-diagonal section. -/
def specialLinearNormalization (pivot : n) :
    Matrix.SpecialLinearGroup n ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)))
      :=
  ⟨(generalLinearDiagonalHom n pivot
      (Matrix.GeneralLinearGroup.det ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))))⁻¹ * (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _))) :
      Matrix.GeneralLinearGroup n ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card
        n)))), by
    change ((Matrix.GeneralLinearGroup.det
      (generalLinearDiagonalHom n pivot
        (Matrix.GeneralLinearGroup.det ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))))⁻¹ * (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _))))) :
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) = 1
    simp⟩

/-- The normalization defines an algebra map out of the native SL quotient. -/
def specialLinearNormalizationSection (pivot : n) :
    (TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) →ₐ[K]
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)) :=
  ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n _).symm
    (specialLinearNormalization K n pivot)).ofConv

/-- On a universal SL entry, the section evaluates the normalized GL matrix. -/
theorem specialLinearNormalizationSection_entry (pivot i j : n) :
    specialLinearNormalizationSection K n pivot (((TauCeti.SpecialLinear.coordinateMap K
      (Fintype.card n)).hom (TauCeti.GeneralLinear.reindexedGenericMatrix K n i j))) =
      (specialLinearNormalization K n pivot : Matrix n n
        ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n)))) i j := by
  exact TauCeti.SpecialLinear.reindexedPointsMulEquiv_symm_apply K n _
    (specialLinearNormalization K n pivot) i j

/-- After imposing determinant one, normalization fixes every matrix entry. -/
theorem specialLinearNormalizationSection_comp_quotient (pivot : n) :
    ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom).comp
      (specialLinearNormalizationSection K n pivot) =
      AlgHom.id K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) := by
  apply (AlgHom.cancel_right (CommHopfAlgCat.mkQuotient_surjective
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))
    (TauCeti.SpecialLinear.definingHopfIdeal K (Fintype.card n)))).mp
  rw [AlgHom.comp_assoc]
  change (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom.comp
      (((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n _).symm
        (specialLinearNormalization K n pivot)).ofConv.comp
          (TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom) = _
  rw [TauCeti.SpecialLinear.reindexedPointsMulEquiv_symm_comp_coordinateMap]
  apply TauCeti.GeneralLinear.reindexedGenericMatrix_algHom_ext K n
  intro i j
  rw [AlgHom.comp_apply, TauCeti.GeneralLinear.reindexedPointsMulEquiv_symm_apply]
  change ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom)
    ((generalLinearDiagonalHom n pivot
      (Matrix.GeneralLinearGroup.det
        (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
          (WithConv.toConv (AlgHom.id K _))))⁻¹ *
        TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
          (WithConv.toConv (AlgHom.id K _)) : Matrix.GeneralLinearGroup n
            (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) i j) = _
  have determinant_quotient :
      Units.map ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card
        n)).hom.toAlgHom).toRingHom.toMonoidHom
        (Matrix.GeneralLinearGroup.det ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _))))) = 1 := by
    apply Units.ext
    change ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom)
      ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
        (WithConv.toConv (AlgHom.id K _)) : Matrix.GeneralLinearGroup n
          (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) :
            Matrix n n _).det = 1
    have hm : ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
        (WithConv.toConv (AlgHom.id K _)) : Matrix.GeneralLinearGroup n
          (TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))) :
            Matrix n n _) = TauCeti.GeneralLinear.reindexedGenericMatrix K n := by
      ext a b
      rw [TauCeti.GeneralLinear.reindexedPointsMulEquiv_apply]
      rfl
    rw [hm, generalLinearReindexedGenericMatrix_det]
    exact TauCeti.SpecialLinear.coordinateMap_determinantGroupLike K (Fintype.card n)
  have normalized_quotient :
      Matrix.GeneralLinearGroup.map ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card
        n)).hom.toAlgHom).toRingHom
        (generalLinearDiagonalHom n pivot
          (Matrix.GeneralLinearGroup.det ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))))⁻¹ * (TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))) =
      Matrix.GeneralLinearGroup.map ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card
        n)).hom.toAlgHom).toRingHom
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))) := by
    have inverse_quotient :
        Units.map ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card
          n)).hom.toAlgHom).toRingHom.toMonoidHom
          (Matrix.GeneralLinearGroup.det ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _)))))⁻¹ = 1 := by
      rw [map_inv, determinant_quotient, inv_one]
    rw [map_mul, generalLinearDiagonalHom_natural]
    calc
      generalLinearDiagonalHom n pivot _ * _ =
          generalLinearDiagonalHom n pivot 1 * _ :=
        congrArg (fun unit : ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)))ˣ ↦
          generalLinearDiagonalHom n pivot unit *
            Matrix.GeneralLinearGroup.map ((TauCeti.SpecialLinear.coordinateMap K (Fintype.card
              n)).hom.toAlgHom).toRingHom
              ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n _
      (WithConv.toConv (AlgHom.id K _))))) inverse_quotient
      _ = _ := by simp
  have hentry := congrArg (fun g : Matrix.GeneralLinearGroup n
      ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))) ↦ g i j)
    normalized_quotient
  simp only [Matrix.GeneralLinearGroup.map_apply,
    TauCeti.GeneralLinear.reindexedPointsMulEquiv_apply,
    AlgHom.id_apply] at hentry
  convert hentry using 1
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  exact (TauCeti.SpecialLinear.coordinateMap_apply K (Fintype.card n) _).symm


/-- The finite GL structure morphism is smooth via mathlib's affine `Spec`
smoothness criterion and the smooth coordinate algebra. -/
instance generalLinearGroupUnderlyingScheme_smooth :
    Smooth ((TauCeti.GeneralLinear.groupScheme K (Fintype.card n)).X).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K ((TauCeti.GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The finite SL structure morphism is smooth via mathlib's affine `Spec`
smoothness criterion and the smooth coordinate algebra. -/
instance specialLinearGroupUnderlyingScheme_smooth :
    Smooth ((TauCeti.SpecialLinear.groupScheme K (Fintype.card n)).X).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K ((TauCeti.SpecialLinear.coordinateHopfAlgebra K (Fintype.card n))))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

end AlgebraicGeometry
