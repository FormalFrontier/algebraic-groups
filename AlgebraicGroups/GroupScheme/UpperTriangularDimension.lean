module

public import AlgebraicGroups.Algebra.LocalizedCoordinateQuotient
public import AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension
public import AlgebraicGroups.GroupScheme.UpperTriangular
public import AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices

/-!
# Coordinate presentation and dimension of the finite upper-triangular group

The actual upper-triangular quotient of the determinant-localized general linear
coordinate ring eliminates precisely the entries below the diagonal. Its retained
polynomial coordinates form a localization over any commutative base ring. Over a
field, evaluating the retained diagonal entries at one and the remaining entries
at zero witnesses the dimension of this localization, even for an empty index type.
-/

@[expose] public section

set_option warningAsError true

noncomputable section

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Matrix indices retained after eliminating the entries below the diagonal. -/
def retainedIndices : Set (ι × ι) := {index | ¬ index.2 < index.1}

/-- The native upper-triangular ideal is exactly the ideal of erased GL entries. -/
theorem ideal_eq_localizedCoordinateIdeal :
    ideal K ι = MvPolynomial.localizedCoordinateIdeal K (retainedIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    by_cases hji : j < i
    · simp only [relation, hji, ite_true]
      change GeneralLinearCoordinateRing.matrix K ι i j ∈
        MvPolynomial.localizedCoordinateIdeal K (retainedIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)
      rw [GeneralLinearCoordinateRing.matrix_apply]
      exact Ideal.subset_span ⟨⟨(i, j), by simpa [retainedIndices] using hji⟩, rfl⟩
    · simp [relation, hji]
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    have hji : j < i := by simpa [retainedIndices] using hij
    change GeneralLinearCoordinateRing.matrix K ι i j ∈ ideal K ι
    exact Ideal.subset_span ⟨(i, j), by simp [relation, hji]⟩

/-- The actual upper-triangular coordinate algebra is a localization of the
polynomial ring on retained coordinates, including over the zero ring. -/
def localizedPolynomialEquiv :
    CoordinateRing K ι ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) :=
  (Ideal.quotientEquivAlgOfEq K (ideal_eq_localizedCoordinateIdeal K ι)).trans
    (MvPolynomial.localizedCoordinateQuotientEquiv K (retainedIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι))

/-- A native retained GL entry maps to its localized polynomial variable. -/
@[simp] theorem localizedPolynomialEquiv_entry (i j : ι) (hji : ¬ j < i) :
    localizedPolynomialEquiv K ι
      (quotient K ι (GeneralLinearCoordinateRing.matrix K ι i j)) =
    algebraMap (MvPolynomial (retainedIndices ι) K)
      (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)))
      (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩) := by
  simp only [localizedPolynomialEquiv, AlgEquiv.trans_apply, quotient,
    GeneralLinearCoordinateRing.matrix_apply]
  exact MvPolynomial.localizedCoordinateQuotientEquiv_coordinate K (retainedIndices ι)
    (GeneralLinearCoordinateRing.determinant K ι) (i, j)
    (by simpa [retainedIndices] using hji)

/-- Conversely, a localized retained variable maps to the actual native entry. -/
@[simp] theorem localizedPolynomialEquiv_symm_entry (i j : ι) (hji : ¬ j < i) :
    (localizedPolynomialEquiv K ι).symm
      (algebraMap (MvPolynomial (retainedIndices ι) K)
        (Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι)))
        (MvPolynomial.X ⟨(i, j), by simpa [retainedIndices] using hji⟩)) =
      quotient K ι (GeneralLinearCoordinateRing.matrix K ι i j) := by
  apply (localizedPolynomialEquiv K ι).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (localizedPolynomialEquiv_entry K ι i j hji).symm

/-- The erased determinant evaluates to one at the identity matrix, with
retained diagonal entries one and strictly upper entries zero. -/
theorem erasedDeterminant_eval_one :
    MvPolynomial.eval
      (fun index : retainedIndices ι => if index.1.1 = index.1.2 then (1 : K) else 0)
      (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) = 1 := by
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

end UpperTriangularCoordinateRing

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The actual finite upper-triangular coordinate ring has dimension equal to
its number of retained polynomial variables. -/
theorem upperTriangularCoordinateRing_ringKrullDim :
    ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing K ι) =
      ((Fintype.card ι + (Fintype.card ι).choose 2 : ℕ) : WithBot ℕ∞) := by
  classical
  calc
    ringKrullDim (UpperTriangularCoordinateRing.CoordinateRing K ι) =
        ringKrullDim (Localization.Away
          (MvPolynomial.eraseCoordinates K (UpperTriangularCoordinateRing.retainedIndices ι)
            (GeneralLinearCoordinateRing.determinant K ι))) :=
      ringKrullDim_eq_of_ringEquiv
        (UpperTriangularCoordinateRing.localizedPolynomialEquiv K ι).toRingEquiv
    _ = ((Fintype.card (UpperTriangularCoordinateRing.retainedIndices ι) : ℕ) :
        WithBot ℕ∞) :=
      MvPolynomial.ringKrullDim_localizationAway_of_eval_ne_zero K
        (UpperTriangularCoordinateRing.retainedIndices ι)
        (MvPolynomial.eraseCoordinates K (UpperTriangularCoordinateRing.retainedIndices ι)
          (GeneralLinearCoordinateRing.determinant K ι))
        (fun index => if index.1.1 = index.1.2 then 1 else 0)
        (by rw [UpperTriangularCoordinateRing.erasedDeterminant_eval_one]; exact one_ne_zero)
    _ = _ := by
      have hcard : Fintype.card (UpperTriangularCoordinateRing.retainedIndices ι) =
          Fintype.card {p : ι × ι // ¬ p.2 < p.1} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
      rw [hcard, Matrix.card_upperTriangularRetainedIndices]

/-- The underlying native affine upper-triangular group scheme has the same
topological dimension as its coordinate ring. -/
theorem upperTriangularGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (upperTriangularGroupUnderlyingScheme K ι).left =
      ((Fintype.card ι + (Fintype.card ι).choose 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim
    (PrimeSpectrum (UpperTriangularCoordinateRing.CoordinateRing K ι)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact upperTriangularCoordinateRing_ringKrullDim K ι

end AlgebraicGeometry
