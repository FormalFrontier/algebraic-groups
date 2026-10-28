/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# The polynomial presentation of the canonical special linear coordinate algebra

Tau Ceti supplies the determinant-one Hopf ideal, its quotient Hopf algebra,
and its closed subgroup scheme. This file retains the independent presentation
by all matrix-entry polynomials modulo determinant minus one. The localization
universal property proves the presentation over every commutative base ring.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, VII §4, Example 4.3.
* Robert Hawkins, Mathlib, `HopfAlgebra.Quotient`.
* Mathlib contributors, the determinant localization universal property.
-/

@[expose] public section

noncomputable section

open TauCeti

universe u v

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n]

/-- The single determinant-one equation in canonical matrix coordinates. -/
def polynomialIdeal : Ideal (MatrixMonoid.CoordinateRing K (Fintype.card n)) :=
  Ideal.span {(Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det - 1}

/-- The all-entry polynomial presentation, before determinant localization. -/
abbrev PolynomialCoordinateRing :=
  MatrixMonoid.CoordinateRing K (Fintype.card n) ⧸ polynomialIdeal K n

/-- The defining polynomial determinant becomes one. -/
theorem polynomialQuotient_det :
    (Ideal.Quotient.mkₐ K (polynomialIdeal K n))
      (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det = 1 := by
  have hz : (Ideal.Quotient.mkₐ K (polynomialIdeal K n))
      ((Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  simpa only [map_sub, map_one, sub_eq_zero] using hz

/-- Determinant-one polynomial evaluation extends across the canonical GL localization. -/
def localizationToPolynomialQuotient :
    GeneralLinear.coordinateHopfAlgebra K (Fintype.card n) →ₐ[K]
      PolynomialCoordinateRing K n :=
  (IsLocalization.Away.liftAlgHom
    (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det
    (f := Ideal.Quotient.mkₐ K (polynomialIdeal K n))
    (by rw [polynomialQuotient_det]; exact isUnit_one)).comp
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)).symm.toAlgHom

/-- Polynomial coordinates evaluated in the canonical special-linear quotient. -/
def polynomialToCoordinateRing :
    MatrixMonoid.CoordinateRing K (Fintype.card n) →ₐ[K]
      SpecialLinear.coordinateHopfAlgebra K (Fintype.card n) :=
  (SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom.comp
    ((GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)).toAlgHom.comp
      (GeneralLinear.coordinateRingMap K (Fintype.card n)))

@[simp]
theorem polynomialToCoordinateRing_det :
    polynomialToCoordinateRing K n
      (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det = 1 := by
  change (SpecialLinear.coordinateMap K (Fintype.card n)).hom
    (GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)
      (GeneralLinear.coordinateRingMap K (Fintype.card n)
        (Matrix.mvPolynomialX (Fin (Fintype.card n)) (Fin (Fintype.card n)) K).det)) = 1
  rw [← GeneralLinear.det_localizedGenericMatrix,
    ← GeneralLinear.determinantGroupLike_val,
    SpecialLinear.coordinateMap_determinantGroupLike]

/-- The all-entry polynomial presentation maps to the canonical SL Hopf algebra. -/
def polynomialQuotientToCoordinateRing :
    PolynomialCoordinateRing K n →ₐ[K]
      SpecialLinear.coordinateHopfAlgebra K (Fintype.card n) :=
  Ideal.Quotient.liftₐ (polynomialIdeal K n) (polynomialToCoordinateRing K n) (by
    intro p hp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hp
    rw [← hq, map_mul, map_sub, map_one,
      polynomialToCoordinateRing_det, sub_self, mul_zero])

/-- The canonical SL quotient maps back to determinant-one polynomials. -/
def coordinateRingToPolynomialQuotient :
    SpecialLinear.coordinateHopfAlgebra K (Fintype.card n) →ₐ[K]
      PolynomialCoordinateRing K n :=
  Ideal.Quotient.liftₐ (SpecialLinear.definingHopfIdeal K (Fintype.card n)).toIdeal
    (localizationToPolynomialQuotient K n) (by
      intro p hp
      rw [SpecialLinear.definingHopfIdeal_toIdeal] at hp
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hp
      rw [← hq, map_mul, map_sub, map_one]
      have hdet : localizationToPolynomialQuotient K n
          (GeneralLinear.determinantGroupLike K (Fintype.card n)) = 1 := by
        rw [GeneralLinear.determinantGroupLike_val]
        simp only [localizationToPolynomialQuotient, AlgHom.comp_apply,
          AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
        rw [GeneralLinear.det_localizedGenericMatrix]
        simp only [GeneralLinear.coordinateRingMap_apply,
          IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
        exact polynomialQuotient_det K n
      rw [hdet, sub_self, mul_zero])

/-- The presentation map to polynomials extends the canonical SL quotient map. -/
theorem coordinateRingToPolynomialQuotient_comp_quotient :
    (coordinateRingToPolynomialQuotient K n).comp
      (SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom =
        localizationToPolynomialQuotient K n :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The polynomial presentation map extends evaluation of all matrix variables. -/
theorem polynomialQuotientToCoordinateRing_comp_quotient :
    (polynomialQuotientToCoordinateRing K n).comp
      (Ideal.Quotient.mkₐ K (polynomialIdeal K n)) =
        polynomialToCoordinateRing K n :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- Passing to the Hopf quotient and back fixes every determinant-one polynomial. -/
theorem coordinateRingToPolynomialQuotient_comp_polynomialQuotientTo :
    (coordinateRingToPolynomialQuotient K n).comp
      (polynomialQuotientToCoordinateRing K n) =
        AlgHom.id K (PolynomialCoordinateRing K n) := by
  apply Ideal.Quotient.algHom_ext K
  rw [AlgHom.comp_assoc, polynomialQuotientToCoordinateRing_comp_quotient]
  apply MvPolynomial.algHom_ext
  intro ij
  change (coordinateRingToPolynomialQuotient K n)
      ((SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)
          (GeneralLinear.coordinateRingMap K (Fintype.card n) (MvPolynomial.X ij)))) = _
  rw [← AlgHom.comp_apply, coordinateRingToPolynomialQuotient_comp_quotient]
  simp only [localizationToPolynomialQuotient, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    GeneralLinear.coordinateRingMap_apply,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Passing through determinant-one polynomials fixes the canonical SL quotient. -/
theorem polynomialQuotientToCoordinateRing_comp_coordinateRingTo :
    (polynomialQuotientToCoordinateRing K n).comp
      (coordinateRingToPolynomialQuotient K n) =
        AlgHom.id K (SpecialLinear.coordinateHopfAlgebra K (Fintype.card n)) := by
  apply (AlgHom.cancel_right (CommHopfAlgCat.mkQuotient_surjective
    (GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))
    (SpecialLinear.definingHopfIdeal K (Fintype.card n)))).mp
  rw [AlgHom.comp_assoc]
  change (polynomialQuotientToCoordinateRing K n).comp
      ((coordinateRingToPolynomialQuotient K n).comp
        (SpecialLinear.coordinateMap K (Fintype.card n)).hom.toAlgHom) = _
  rw [coordinateRingToPolynomialQuotient_comp_quotient]
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext K (Fintype.card n)
  intro i j
  change (polynomialQuotientToCoordinateRing K n)
      (localizationToPolynomialQuotient K n
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv K (Fintype.card n)
          (GeneralLinear.coordinateRingMap K (Fintype.card n) (MvPolynomial.X (i, j))))) = _
  simp only [localizationToPolynomialQuotient, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    GeneralLinear.coordinateRingMap_apply,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  change polynomialQuotientToCoordinateRing K n
    ((Ideal.Quotient.mkₐ K (polynomialIdeal K n)) (MvPolynomial.X (i, j))) = _
  rw [← AlgHom.comp_apply, polynomialQuotientToCoordinateRing_comp_quotient]
  simp only [polynomialToCoordinateRing, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    BialgHom.coe_toAlgHom,
    GeneralLinear.coordinateRingMap_apply, AlgHom.id_apply]
  exact SpecialLinear.coordinateMap_apply K (Fintype.card n) _

/-- The canonical special-linear Hopf algebra has the determinant-one
all-entry polynomial presentation over every commutative base ring. -/
def polynomialEquiv : PolynomialCoordinateRing K n ≃ₐ[K]
    SpecialLinear.coordinateHopfAlgebra K (Fintype.card n) :=
  AlgEquiv.ofAlgHom (polynomialQuotientToCoordinateRing K n)
    (coordinateRingToPolynomialQuotient K n)
    (polynomialQuotientToCoordinateRing_comp_coordinateRingTo K n)
    (coordinateRingToPolynomialQuotient_comp_polynomialQuotientTo K n)

end SpecialLinearCoordinateRing
