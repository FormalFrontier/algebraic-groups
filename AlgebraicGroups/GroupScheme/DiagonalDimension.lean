/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.LocalizedCoordinateQuotient
public import AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension
public import AlgebraicGroups.GroupScheme.Diagonal

/-!
# Dimension of the finite diagonal group scheme

The actual diagonal Hopf quotient of the determinant-localized general linear
coordinate algebra is a localization of the polynomial algebra in its retained
diagonal entries. Over a field, evaluation of those entries at one witnesses the
full dimension, including over finite fields and for an empty index type.

Milne's diagonal group over a field is the mathematical antecedent. Here the
two ideal inclusions identify the determinant-localized quotient over any
commutative ring; the field-only dimension calculation uses an explicit
identity evaluation, not a general dimension formula for products.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (diagonal matrices over a field).
* `AlgebraicGroups.Algebra.LocalizedCoordinateQuotient` (erasing coordinates in a
  localized quotient) and `AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension`
  (dimension of a polynomial localization with a specified nonvanishing point);
  `AlgebraicGroups.Algebra.DiagonalCoordinateRing` and
  `AlgebraicGroups.GroupScheme.Diagonal` supply the quotient and underlying scheme.
* Mathlib, `Mathlib.RingTheory.KrullDimension.Polynomial` and
  `Mathlib.RingTheory.Spectrum.Prime.Topology` (polynomial and affine-spectrum
  dimension), together with its matrix determinant and polynomial evaluation APIs.
-/

@[expose] public section

set_option warningAsError true

noncomputable section

universe u

namespace DiagonalCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- Indices of the retained diagonal polynomial coordinates. -/
def diagonalIndices : Set (ι × ι) := {index | index.1 = index.2}

/-- The off-diagonal GL quotient ideal equals the ideal of eliminated coordinates.
The diagonal-matrix equations in Milne, *Algebraic Groups* (2017), item 2.9,
are the field-case antecedent; both ideal inclusions are proved over `CommRing K`. -/
theorem ideal_eq_localizedCoordinateIdeal :
    ideal K ι = MvPolynomial.localizedCoordinateIdeal K (diagonalIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    by_cases hij : i = j
    · simp [relation, hij]
    · simp only [relation, hij, ite_false]
      change GeneralLinearCoordinateRing.matrix K ι i j ∈
        MvPolynomial.localizedCoordinateIdeal K (diagonalIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)
      rw [GeneralLinearCoordinateRing.matrix_apply]
      exact Ideal.subset_span ⟨⟨(i, j), by simpa [diagonalIndices] using hij⟩, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    have hne : i ≠ j := by simpa [diagonalIndices] using hij
    change GeneralLinearCoordinateRing.matrix K ι i j ∈ ideal K ι
    apply Ideal.subset_span
    exact ⟨(i, j), by simp [relation, hne]⟩

/-- The diagonal coordinate ring as a localization of the retained polynomial
coordinates, including over the zero ring. This specializes
`MvPolynomial.localizedCoordinateQuotientEquiv` to the identified GL quotient ideal;
Milne, *Algebraic Groups* (2017), item 2.9, treats diagonal groups over a field. -/
def localizedPolynomialEquiv :
    CoordinateRing K ι ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) :=
  (Ideal.quotientEquivAlgOfEq K (ideal_eq_localizedCoordinateIdeal K ι)).trans
    (MvPolynomial.localizedCoordinateQuotientEquiv K (diagonalIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι))

/-- The forward presentation sends a native diagonal entry to its retained variable. -/
@[simp] theorem localizedPolynomialEquiv_diagonal (i : ι) :
    localizedPolynomialEquiv K ι
      (quotient K ι (GeneralLinearCoordinateRing.matrix K ι i i)) =
    algebraMap (MvPolynomial (diagonalIndices ι) K)
      (Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)))
      (MvPolynomial.X ⟨(i, i), rfl⟩) := by
  simp only [localizedPolynomialEquiv, AlgEquiv.trans_apply, quotient,
    GeneralLinearCoordinateRing.matrix_apply]
  exact MvPolynomial.localizedCoordinateQuotientEquiv_coordinate K (diagonalIndices ι)
    (GeneralLinearCoordinateRing.determinant K ι) (i, i) rfl

/-- The inverse presentation sends a retained variable to the actual diagonal entry. -/
@[simp] theorem localizedPolynomialEquiv_symm_diagonal (i : ι) :
    (localizedPolynomialEquiv K ι).symm
      (algebraMap (MvPolynomial (diagonalIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)))
        (MvPolynomial.X ⟨(i, i), rfl⟩)) =
      quotient K ι (GeneralLinearCoordinateRing.matrix K ι i i) := by
  apply (localizedPolynomialEquiv K ι).injective
  rw [AlgEquiv.apply_symm_apply, localizedPolynomialEquiv_diagonal]

/-- The retained variables are indexed by precisely the original matrix indices. -/
def diagonalIndicesEquiv : diagonalIndices ι ≃ ι where
  toFun index := index.1.1
  invFun i := ⟨(i, i), rfl⟩
  left_inv index := by
    rcases index with ⟨⟨i, j⟩, hij⟩
    change i = j at hij
    cases hij
    rfl
  right_inv _ := rfl

/-- Evaluation of the retained variables at one takes the generic matrix to
the identity, so its determinant evaluates to one. -/
theorem erasedDeterminant_eval_one :
    MvPolynomial.eval (fun _ : diagonalIndices ι => (1 : K))
      (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) = 1 := by
  let evaluation : MvPolynomial (ι × ι) K →+* K :=
    (MvPolynomial.eval (fun _ : diagonalIndices ι => (1 : K))).comp
      (MvPolynomial.eraseCoordinates K (diagonalIndices ι)).toRingHom
  have hmatrix : (Matrix.mvPolynomialX ι ι K).map evaluation = (1 : Matrix ι ι K) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, Matrix.one_apply]
      change MvPolynomial.eval (fun _ : diagonalIndices ι => (1 : K))
        (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
          (MvPolynomial.X (i, i))) = 1
      rw [MvPolynomial.eraseCoordinates_X_mem K (diagonalIndices ι) (i, i)
        (by simp [diagonalIndices])]
      simp
    · simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, Matrix.one_apply,
        ite_eq_right hij]
      change MvPolynomial.eval (fun _ : diagonalIndices ι => (1 : K))
        (MvPolynomial.eraseCoordinates K (diagonalIndices ι)
          (MvPolynomial.X (i, j))) = 0
      rw [MvPolynomial.eraseCoordinates_X_not_mem K (diagonalIndices ι) (i, j)
        (by simpa [diagonalIndices] using hij)]
      simp
  change evaluation (Matrix.mvPolynomialX ι ι K).det = 1
  rw [RingHom.map_det]
  change ((Matrix.mvPolynomialX ι ι K).map evaluation).det = 1
  rw [hmatrix, Matrix.det_one]

end DiagonalCoordinateRing

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- The finite diagonal coordinate ring has dimension `card ι` over every field.
Milne, *Algebraic Groups* (2017), item 2.9, gives the field-case diagonal
description; the dimension proof applies the supplied-point polynomial-localization
theorem to the identity evaluation, then counts variables by `diagonalIndicesEquiv`. -/
theorem diagonalCoordinateRing_ringKrullDim :
    ringKrullDim (DiagonalCoordinateRing.CoordinateRing K ι) =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  classical
  calc
    ringKrullDim (DiagonalCoordinateRing.CoordinateRing K ι) =
        ringKrullDim (Localization.Away
          (MvPolynomial.eraseCoordinates K (DiagonalCoordinateRing.diagonalIndices ι)
            (GeneralLinearCoordinateRing.determinant K ι))) :=
      ringKrullDim_eq_of_ringEquiv
        (DiagonalCoordinateRing.localizedPolynomialEquiv K ι).toRingEquiv
    _ = ((Fintype.card (DiagonalCoordinateRing.diagonalIndices ι) : ℕ) : WithBot ℕ∞) :=
      MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero K
        (DiagonalCoordinateRing.diagonalIndices ι)
        (MvPolynomial.eraseCoordinates K (DiagonalCoordinateRing.diagonalIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)) (fun _ => 1)
        (by rw [DiagonalCoordinateRing.erasedDeterminant_eval_one]; exact one_ne_zero)
    _ = _ := by rw [Fintype.card_congr (DiagonalCoordinateRing.diagonalIndicesEquiv ι)]

/-- The diagonal group's underlying affine scheme has topological Krull
dimension `card ι` over every field. Milne, *Algebraic Groups* (2017),
item 2.9, gives the diagonal field-case antecedent; Mathlib's
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` transfers the ring result. -/
theorem diagonalGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (diagonalGroupUnderlyingScheme K ι).left =
      ((Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim
    (PrimeSpectrum (DiagonalCoordinateRing.CoordinateRing K ι)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact diagonalCoordinateRing_ringKrullDim K ι

end AlgebraicGeometry
