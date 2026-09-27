/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.SpecialLinear
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

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

The proof uses the published finite matrix-group and coordinate-ring APIs and
mathlib's smoothness and affine-scheme criteria. This module is an original
formal proof under Apache-2.0, not a transcription of third-party text.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The finite general linear coordinate algebra is smooth over any commutative base. -/
instance generalLinearCoordinateRing_smooth :
    Algebra.Smooth K (GeneralLinearCoordinateRing.CoordinateRing K n) where
  formallySmooth := inferInstance
  finitePresentation := GeneralLinearCoordinateRing.finitePresentation K n

/-- The determinant-one quotient has a finite presentation, including in rank zero. -/
instance specialLinearCoordinateRing_finitePresentation :
    Algebra.FinitePresentation K (SpecialLinearCoordinateRing.CoordinateRing K n) :=
  Algebra.FinitePresentation.of_surjective
    (f := SpecialLinearCoordinateRing.quotient K n)
    Ideal.Quotient.mk_surjective (by
      rw [show (SpecialLinearCoordinateRing.quotient K n).toRingHom =
        Ideal.Quotient.mkₐ K (SpecialLinearCoordinateRing.determinantOneIdeal K n) from rfl,
        Ideal.Quotient.mkₐ_ker]
      exact Submodule.fg_span_singleton _)

/-- A retract of a formally smooth algebra is formally smooth. -/
private theorem formallySmooth_of_retract {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Algebra.FormallySmooth K A]
    (quotient : A →ₐ[K] B) (split : B →ₐ[K] A)
    (split_quotient : quotient.comp split = AlgHom.id K B) :
    Algebra.FormallySmooth K B := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ I hI f ↦ ?_
  obtain ⟨lift, lift_eq⟩ :=
    Algebra.FormallySmooth.comp_surjective K A I hI (f.comp quotient)
  refine ⟨lift.comp split, ?_⟩
  calc
    (Ideal.Quotient.mkₐ K I).comp (lift.comp split) =
        ((Ideal.Quotient.mkₐ K I).comp lift).comp split := (AlgHom.comp_assoc ..).symm
    _ = (f.comp quotient).comp split := by rw [lift_eq]
    _ = f := by rw [AlgHom.comp_assoc, split_quotient, AlgHom.comp_id]

/-- Normalize the universal GL matrix to determinant one at the chosen pivot. -/
def specialLinearNormalization (pivot : n) :
    Matrix.SpecialLinearGroup n (GeneralLinearCoordinateRing.CoordinateRing K n) :=
  ⟨(generalLinearDiagonalHom n pivot
      (Matrix.GeneralLinearGroup.det (universal K n))⁻¹ * universal K n :
      Matrix.GeneralLinearGroup n (GeneralLinearCoordinateRing.CoordinateRing K n)), by
    change ((Matrix.GeneralLinearGroup.det
      (generalLinearDiagonalHom n pivot
        (Matrix.GeneralLinearGroup.det (universal K n))⁻¹ * universal K n)) :
        GeneralLinearCoordinateRing.CoordinateRing K n) = 1
    simp⟩

/-- The normalization defines an algebra map out of the native SL quotient. -/
def specialLinearNormalizationSection (pivot : n) :
    SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      GeneralLinearCoordinateRing.CoordinateRing K n :=
  specialLinearFromSL K n _ (specialLinearNormalization K n pivot)

/-- On a universal SL entry, the section evaluates the normalized GL matrix. -/
theorem specialLinearNormalizationSection_entry (pivot i j : n) :
    specialLinearNormalizationSection K n pivot (SpecialLinearCoordinateRing.entry K n i j) =
      (specialLinearNormalization K n pivot : Matrix n n
        (GeneralLinearCoordinateRing.CoordinateRing K n)) i j := by
  change (specialLinearFromSL K n _ (specialLinearNormalization K n pivot))
    ((SpecialLinearCoordinateRing.quotient K n) (matrix K n i j)) = _
  rw [← AlgHom.comp_apply, specialLinearFromSL_comp_quotient, evaluate_matrix]
  rfl

/-- After imposing determinant one, normalization fixes every matrix entry. -/
theorem specialLinearNormalizationSection_comp_quotient (pivot : n) :
    (SpecialLinearCoordinateRing.quotient K n).comp
      (specialLinearNormalizationSection K n pivot) =
      AlgHom.id K (SpecialLinearCoordinateRing.CoordinateRing K n) := by
  apply Ideal.Quotient.algHom_ext K
  change (SpecialLinearCoordinateRing.quotient K n).comp
    ((specialLinearFromSL K n _ (specialLinearNormalization K n pivot)).comp
      (SpecialLinearCoordinateRing.quotient K n)) =
    (AlgHom.id K _).comp (SpecialLinearCoordinateRing.quotient K n)
  rw [specialLinearFromSL_comp_quotient, AlgHom.id_comp]
  apply GeneralLinearCoordinateRing.hom_ext
  intro i j
  rw [AlgHom.comp_apply, evaluate_matrix]
  change (SpecialLinearCoordinateRing.quotient K n)
    ((generalLinearDiagonalHom n pivot
      (Matrix.GeneralLinearGroup.det (universal K n))⁻¹ * universal K n :
        Matrix.GeneralLinearGroup n (GeneralLinearCoordinateRing.CoordinateRing K n)) i j) =
      (SpecialLinearCoordinateRing.quotient K n) (matrix K n i j)
  have determinant_quotient :
      Units.map (SpecialLinearCoordinateRing.quotient K n).toRingHom.toMonoidHom
        (Matrix.GeneralLinearGroup.det (universal K n)) = 1 := by
    apply Units.ext
    change (SpecialLinearCoordinateRing.quotient K n) (matrix K n).det = 1
    exact SpecialLinearCoordinateRing.quotient_det K n
  have normalized_quotient :
      Matrix.GeneralLinearGroup.map (SpecialLinearCoordinateRing.quotient K n).toRingHom
        (generalLinearDiagonalHom n pivot
          (Matrix.GeneralLinearGroup.det (universal K n))⁻¹ * universal K n) =
      Matrix.GeneralLinearGroup.map (SpecialLinearCoordinateRing.quotient K n).toRingHom
        (universal K n) := by
    have inverse_quotient :
        Units.map (SpecialLinearCoordinateRing.quotient K n).toRingHom.toMonoidHom
          (Matrix.GeneralLinearGroup.det (universal K n))⁻¹ = 1 := by
      rw [map_inv, determinant_quotient, inv_one]
    rw [map_mul, generalLinearDiagonalHom_natural]
    calc
      generalLinearDiagonalHom n pivot _ * _ =
          generalLinearDiagonalHom n pivot 1 * _ :=
        congrArg (fun unit : (SpecialLinearCoordinateRing.CoordinateRing K n)ˣ ↦
          generalLinearDiagonalHom n pivot unit *
            Matrix.GeneralLinearGroup.map (SpecialLinearCoordinateRing.quotient K n).toRingHom
              (universal K n)) inverse_quotient
      _ = _ := by simp
  exact congrArg (fun g : Matrix.GeneralLinearGroup n
      (SpecialLinearCoordinateRing.CoordinateRing K n) ↦ g i j) normalized_quotient

set_option linter.style.haveILetI false

/-- The finite special linear coordinate algebra is smooth over any commutative base. -/
instance specialLinearCoordinateRing_smooth :
    Algebra.Smooth K (SpecialLinearCoordinateRing.CoordinateRing K n) where
  formallySmooth := by
    classical
    cases isEmpty_or_nonempty n with
    | inl emptyIndex =>
      letI : IsEmpty n := emptyIndex
      have determinant_one : (matrix K n).det = 1 := by
        exact Matrix.det_isEmpty
      have ideal_bot : SpecialLinearCoordinateRing.determinantOneIdeal K n = ⊥ := by
        simp [SpecialLinearCoordinateRing.determinantOneIdeal, determinant_one]
      exact Algebra.FormallySmooth.of_equiv
        ((AlgEquiv.quotientBot K (GeneralLinearCoordinateRing.CoordinateRing K n)).symm.trans
          (Ideal.quotientEquivAlgOfEq K ideal_bot.symm))
    | inr nonemptyIndex =>
      exact formallySmooth_of_retract K
        (SpecialLinearCoordinateRing.quotient K n)
        (specialLinearNormalizationSection K n (Classical.choice nonemptyIndex))
        (specialLinearNormalizationSection_comp_quotient K n _)
  finitePresentation := inferInstance

set_option linter.style.haveILetI true

/-- The actual finite GL structure morphism is smooth. -/
instance generalLinearGroupUnderlyingScheme_smooth :
    Smooth (generalLinearGroupUnderlyingScheme K n).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K (GeneralLinearCoordinateRing.CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The actual finite SL structure morphism is smooth. -/
instance specialLinearGroupUnderlyingScheme_smooth :
    Smooth (specialLinearGroupUnderlyingScheme K n).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

end AlgebraicGeometry
