/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.LocalizedCoordinateQuotient
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices

/-!
# Coordinate presentation and dimension of the finite upper-triangular group

The actual upper-triangular quotient of the determinant-localized general linear
coordinate ring eliminates precisely the entries below the diagonal. Its retained
polynomial coordinates form a localization over any commutative base ring. Over a
field, evaluating the retained diagonal entries at one and the remaining entries
at zero witnesses the dimension of this localization, even for an empty index type.

Milne describes the upper-triangular coordinate algebra over a field. The
equality of the two quotient ideals and the localization presentation here
hold over any commutative ring; the numerical dimension is proved only over
a field, using identity evaluation and a separate count of retained indices.

## References

* J. S. Milne, *Algebraic Groups* (2017), items 2.9 (triangular matrices) and
  2.40 (their field-case coordinate algebra).
* `AlgebraicGroups.Algebra.LocalizedCoordinateQuotient` (generic elimination),
  `AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension` (dimension
  with a supplied nonvanishing point), and
  `AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices` (index count);
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra` and
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic` supply
  the canonical defining quotient.
* Mathlib, `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.RingTheory.Spectrum.Prime.Topology` (ring and spectrum dimension).
-/

@[expose] public section

set_option warningAsError true

noncomputable section

universe u v

namespace TauCeti.GeneralLinear.UpperTriangular

/-- Matrix indices retained after eliminating the entries below the diagonal. -/
def retainedIndices (ι : Type v) [LT ι] : Set (ι × ι) := {index | ¬ index.2 < index.1}

section GenericEvaluation

variable (K : Type u) [CommRing K] (ι : Type v) [Fintype ι] [LinearOrder ι]

/-- The erased determinant evaluates to one at the identity matrix, with
retained diagonal entries one and strictly upper entries zero. -/
theorem erasedDeterminant_eval_one :
    MvPolynomial.eval
      (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
      (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        ((Matrix.mvPolynomialX ι ι K).det)) = 1 := by
  let evaluation : MvPolynomial (ι × ι) K →+* K :=
    (MvPolynomial.eval
      (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)).comp
      (MvPolynomial.eraseCoordinates K (retainedIndices ι)).toRingHom
  have hmatrix : (Matrix.mvPolynomialX ι ι K).map evaluation = (1 : Matrix ι ι K) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, Matrix.one_apply]
      change MvPolynomial.eval
        (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
        (MvPolynomial.eraseCoordinates K (retainedIndices ι) (MvPolynomial.X (i, i))) = 1
      rw [MvPolynomial.eraseCoordinates_X_mem K (retainedIndices ι) (i, i)
        (by simp [retainedIndices])]
      simp
    · simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, Matrix.one_apply,
        ite_eq_right hij]
      change MvPolynomial.eval
        (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
        (MvPolynomial.eraseCoordinates K (retainedIndices ι) (MvPolynomial.X (i, j))) = 0
      by_cases hji : j < i
      · rw [MvPolynomial.eraseCoordinates_X_not_mem K (retainedIndices ι) (i, j)
          (by simpa [retainedIndices] using hji)]
        simp
      · rw [MvPolynomial.eraseCoordinates_X_mem K (retainedIndices ι) (i, j)
          (by simpa [retainedIndices] using hji)]
        simp [hij]
  change evaluation (Matrix.mvPolynomialX ι ι K).det = 1
  rw [RingHom.map_det]
  change ((Matrix.mvPolynomialX ι ι K).map evaluation).det = 1
  rw [hmatrix, Matrix.det_one]

end GenericEvaluation

variable (K : Type u) [CommRing K] (n : ℕ)

/-- The defining ideal is the image of the erased-coordinate ideal in the determinant
localization under the canonical general-linear coordinate equivalence. -/
theorem definingHopfIdeal_eq_map_localizedCoordinateIdeal :
    (definingHopfIdeal K n).toIdeal =
      Ideal.map (GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toRingHom
        (MvPolynomial.localizedCoordinateIdeal K (retainedIndices (Fin n))
          (Matrix.mvPolynomialX (Fin n) (Fin n) K).det) := by
  rw [definingHopfIdeal_toIdeal, MvPolynomial.localizedCoordinateIdeal, Ideal.map_span]
  congr 1
  ext x
  rw [mem_definingRelationSet_iff]
  constructor
  · rintro ⟨i, j, hji, rfl⟩
    refine ⟨algebraMap (MvPolynomial (Fin n × Fin n) K)
      (GeneralLinear.CoordinateRing K n) (MvPolynomial.X (i, j)), ?_, ?_⟩
    · exact ⟨⟨(i, j), by simpa [retainedIndices] using hji⟩, rfl⟩
    · simp only [GeneralLinear.coordinateRingMap_apply]
      rfl
  · rintro ⟨y, ⟨⟨⟨i, j⟩, hji⟩, rfl⟩, rfl⟩
    refine ⟨i, j, by simpa [retainedIndices] using hji, ?_⟩
    simp only [GeneralLinear.coordinateRingMap_apply]
    rfl

/-- The canonical upper-triangular coordinate algebra is a determinant localization
of its retained polynomial coordinates, over every commutative base. -/
def localizedPolynomialEquiv :
    coordinateHopfAlgebra K n ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
        (Matrix.mvPolynomialX (Fin n) (Fin n) K).det) := by
  let e := GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
  let I := MvPolynomial.localizedCoordinateIdeal K (retainedIndices (Fin n))
    (Matrix.mvPolynomialX (Fin n) (Fin n) K).det
  have hI : I = Ideal.map e.symm.toRingHom (definingHopfIdeal K n).toIdeal := by
    rw [definingHopfIdeal_eq_map_localizedCoordinateIdeal, Ideal.map_map]
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
      ext x
      exact e.symm_apply_apply x
    rw [he, Ideal.map_id]
  exact (Ideal.quotientEquivAlg _ _ e.symm hI).trans
    (MvPolynomial.localizedCoordinateQuotientEquiv K (retainedIndices (Fin n))
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det)

/-- A retained generic matrix entry maps to its localized polynomial variable. -/
theorem localizedPolynomialEquiv_entry (i j : Fin n) (hji : ¬ j < i) :
    localizedPolynomialEquiv K n ((coordinateMap K n).hom
      (GeneralLinear.genericMatrix K n i j)) =
      algebraMap (MvPolynomial (retainedIndices (Fin n)) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
          (Matrix.mvPolynomialX (Fin n) (Fin n) K).det))
        (MvPolynomial.X ⟨(i, j), hji⟩) := by
  rw [GeneralLinear.genericMatrix_apply, coordinateMap_apply]
  dsimp only [localizedPolynomialEquiv, id_eq, AlgEquiv.trans_apply]
  change (MvPolynomial.localizedCoordinateQuotientEquiv K (retainedIndices (Fin n))
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det)
    (Ideal.Quotient.mk _ ((GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).symm
      ((GeneralLinear.coordinateHopfAlgebraAlgEquiv K n)
        (GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))))) = _
  rw [AlgEquiv.symm_apply_apply]
  simp only [GeneralLinear.coordinateRingMap_apply]
  exact MvPolynomial.localizedCoordinateQuotientEquiv_coordinate K (retainedIndices (Fin n))
    (Matrix.mvPolynomialX (Fin n) (Fin n) K).det (i, j) hji

/-- Conversely, a localized retained variable maps to the corresponding quotient entry. -/
@[simp] theorem localizedPolynomialEquiv_symm_entry (i j : Fin n) (hji : ¬ j < i) :
    (localizedPolynomialEquiv K n).symm
      (algebraMap (MvPolynomial (retainedIndices (Fin n)) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
          (Matrix.mvPolynomialX (Fin n) (Fin n) K).det))
        (MvPolynomial.X ⟨(i, j), hji⟩)) =
      (coordinateMap K n).hom (GeneralLinear.genericMatrix K n i j) := by
  apply (localizedPolynomialEquiv K n).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (localizedPolynomialEquiv_entry K n i j hji).symm

end TauCeti.GeneralLinear.UpperTriangular

namespace AlgebraicGeometry

open TauCeti.GeneralLinear.UpperTriangular

variable (K : Type u) [Field K] (n : ℕ)

/-- Over every field, the canonical upper-triangular coordinate algebra has dimension
n plus n choose two. Identity evaluation witnesses nonvanishing of its localization. -/
theorem upperTriangularCoordinateRing_ringKrullDim :
    ringKrullDim (coordinateHopfAlgebra K n) = ((n + n.choose 2 : ℕ) : WithBot ℕ∞) := by
  classical
  rw [ringKrullDim_eq_of_ringEquiv (localizedPolynomialEquiv K n).toRingEquiv]
  have hne : MvPolynomial.eraseCoordinates K (retainedIndices (Fin n))
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det ≠ 0 := by
    intro hzero
    have heval := congrArg (MvPolynomial.eval
      (fun index => if index.1.1 = index.1.2 then 1 else 0)) hzero
    rw [erasedDeterminant_eval_one, map_zero] at heval
    exact one_ne_zero heval
  rw [TauCeti.ringKrullDim_localization_away K hne,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp only [zero_add, Nat.card_eq_fintype_card]
  have hcard : Fintype.card (retainedIndices (Fin n)) = n + n.choose 2 := by
    let e : retainedIndices (Fin n) ≃ {p : Fin n × Fin n // ¬ p.2 < p.1} :=
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun p => ⟨p.1, p.2⟩ }
    rw [Fintype.card_congr e]
    simpa only [Fintype.card_fin] using Matrix.card_upperTriangularRetainedIndices (Fin n)
  rw [hcard]

/-- The canonical group's underlying affine scheme has the coordinate-ring dimension. -/
theorem upperTriangularGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (groupScheme K n).X.left = ((n + n.choose 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (coordinateHopfAlgebra K n)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact upperTriangularCoordinateRing_ringKrullDim K n

end AlgebraicGeometry
