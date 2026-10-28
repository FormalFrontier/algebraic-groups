/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoefficientMatrixUnit
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Integer-weight coefficient matrix units under maps and reindexing

The diagonal matrix with group weights `3` and `7` over `ℕ[ℤ]` satisfies the
coefficient-matrix coproduct and counit laws. Its coefficient-matrix unit has
entrywise antipode as inverse, with weights `-3` and `-7`. Coefficient
observations distinguish this inverse from the original matrix, and distinguish
the original matrix from the identity. All four weights have coefficient `1`.

Doubling the group weights through a bialgebra homomorphism gives weights
`6,14` and inverse weights `-6,-14`. Simultaneously swapping rows and columns
gives weights `7,3` and inverse weights `-7,-3`. Coefficients distinguish both
images from the original and identity matrices. The counit supplies a
noninjective coefficient map: distinct group singles map to `1`, and the
coefficient-matrix unit maps to the identity unit.

The empty-index example retains arbitrary commutative-semiring scalars and a
possibly noncommutative semiring Hopf algebra. Its coefficient-matrix unit and
inverse are both the unique unit on the empty index. Coefficient-map naturality
also holds there, as does reindexing to an empty type in an independent universe.

## References

These examples use Mathlib's monoid-algebra Hopf structure,
`MonoidAlgebra.isGroupLikeElem_single_one`, `MonoidAlgebra.antipode_single`,
and its dedicated coefficient API, together with finite matrix sums and the
generic subsingleton-units instance. Transport uses
`MonoidAlgebra.mapDomainBialgHom`, `Bialgebra.counitBialgHom`, `Units.map`, and
`Matrix.reindexRingEquiv`. The matrix units are constructed and observed through
`HopfAlgebra.coefficientMatrixUnit` and its public API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public noncomputable section

open scoped BigOperators
open TensorProduct

universe u v
universe v' w

namespace HopfAlgebra

section IntegerWeights

/-- A two-dimensional diagonal matrix over `ℕ[ℤ]` with group weights `3` and `7`.
Both weights are group-basis singles with coefficient `1`. -/
def integerWeightMatrix : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ)) :=
  Matrix.diagonal fun i =>
    MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (3 : ℤ) else 7)) (1 : ℕ)

/-- The group-weight diagonal matrix satisfies the matrix comultiplication law. -/
theorem integerWeightMatrix_comul (i j : Fin 2) :
    Coalgebra.comul (R := ℕ) (integerWeightMatrix i j) =
      ∑ k, integerWeightMatrix i k ⊗ₜ[ℕ] integerWeightMatrix k j := by
  fin_cases i <;> fin_cases j <;>
    simp [integerWeightMatrix, Matrix.diagonal_apply, Fin.sum_univ_two]

/-- The group-weight diagonal matrix satisfies the counit Kronecker-delta law. -/
theorem integerWeightMatrix_counit (i j : Fin 2) :
    Coalgebra.counit (R := ℕ) (integerWeightMatrix i j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [integerWeightMatrix]

/-- The group-weight diagonal matrix, using the coefficient-matrix construction. -/
def integerWeightMatrixUnit :
    (Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ)))ˣ :=
  coefficientMatrixUnit (R := ℕ) integerWeightMatrix
    integerWeightMatrix_comul integerWeightMatrix_counit

/-- The unit's diagonal entries have supports `3,7`, and its inverse has supports `-3,-7`. -/
theorem integerWeightMatrixUnit_diagonal_entries :
    (↑integerWeightMatrixUnit : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0 =
        MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ) ∧
      (↑integerWeightMatrixUnit : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1 =
        MonoidAlgebra.single (Multiplicative.ofAdd (7 : ℤ)) (1 : ℕ) ∧
      (↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0 =
        MonoidAlgebra.single (Multiplicative.ofAdd (-3 : ℤ)) (1 : ℕ) ∧
      (↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1 =
        MonoidAlgebra.single (Multiplicative.ofAdd (-7 : ℤ)) (1 : ℕ) := by
  simp only [integerWeightMatrixUnit, coefficientMatrixUnit_apply,
    coefficientMatrixUnit_inv_apply]
  simp [integerWeightMatrix]

/-- The unit inverse is the diagonal matrix with group weights `-3` and `-7`. -/
theorem integerWeightMatrixUnit_inv_eq :
    (↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
      (MonoidAlgebra ℕ (Multiplicative ℤ))) =
      Matrix.diagonal (fun i : Fin 2 =>
        MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (-3 : ℤ) else -7)) (1 : ℕ)) := by
  rw [integerWeightMatrixUnit, coe_coefficientMatrixUnit_inv]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [integerWeightMatrix]

/-- Coefficients of the inverse entries distinguish negative and positive group supports. -/
theorem integerWeightMatrixUnit_inv_coefficients :
    ((↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (-3 : ℤ)) = 1 ∧
      ((↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1).coeff (Multiplicative.ofAdd (-7 : ℤ)) = 1 ∧
      ((↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (3 : ℤ)) = 0 := by
  rw [integerWeightMatrixUnit_diagonal_entries.2.2.1,
    integerWeightMatrixUnit_diagonal_entries.2.2.2]
  have hsupport : Multiplicative.ofAdd (-3 : ℤ) ≠ Multiplicative.ofAdd (3 : ℤ) := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · simp only [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · simp only [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hsupport]

/-- The group-weight coefficient matrix is not the identity matrix. -/
theorem integerWeightMatrix_ne_one : integerWeightMatrix ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ)) => M 0 0) h
  have hsingle : MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ) =
      MonoidAlgebra.single (1 : Multiplicative ℤ) (1 : ℕ) := by
    simpa [integerWeightMatrix, MonoidAlgebra.one_def] using h00
  have hsupport := (MonoidAlgebra.single_left_inj (by decide : (1 : ℕ) ≠ 0)).1 hsingle
  exact (by decide : Multiplicative.ofAdd (3 : ℤ) ≠ (1 : Multiplicative ℤ)) hsupport

/-- The inverse of the group-weight coefficient matrix unit differs from the input matrix. -/
theorem integerWeightMatrixUnit_inv_ne :
    (↑(integerWeightMatrixUnit⁻¹) : Matrix (Fin 2) (Fin 2)
      (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠ integerWeightMatrix := by
  intro h
  have hcoeff := integerWeightMatrixUnit_inv_coefficients.2.2
  rw [h] at hcoeff
  simp [integerWeightMatrix] at hcoeff

/-- The group-weight diagonal matrix is a unit over the semiring `ℕ[ℤ]`. -/
theorem isUnit_integerWeightMatrix : IsUnit integerWeightMatrix := by
  exact isUnit_coefficientMatrix (R := ℕ) integerWeightMatrix
    integerWeightMatrix_comul integerWeightMatrix_counit

end IntegerWeights

section IntegerWeightTransport

/-- Doubling a group weight maps its basis single to the doubled support. -/
private theorem doubleWeight_single (n : ℤ) :
    MonoidAlgebra.mapDomainBialgHom ℕ (powMonoidHom (α := Multiplicative ℤ) 2)
        (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : ℕ)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (n + n)) (1 : ℕ) := by
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  simp [powMonoidHom, pow_two]

/-- Coefficient-map naturality doubles the diagonal supports to `6,14` and the inverse
supports to `-6,-14`. The inverse computation uses the standard map on units. -/
theorem integerWeightMatrixUnit_map_double :
    let f := MonoidAlgebra.mapDomainBialgHom ℕ (powMonoidHom (α := Multiplicative ℤ) 2)
    let U := Units.map (RingHom.mapMatrix (m := Fin 2) f.toAlgHom.toRingHom).toMonoidHom
      integerWeightMatrixUnit
    U = coefficientMatrixUnit (R := ℕ) (integerWeightMatrix.map f)
        (Coalgebra.coefficientMatrix_comul_map integerWeightMatrix integerWeightMatrix_comul
          f.toCoalgHom)
        (Coalgebra.coefficientMatrix_counit_map integerWeightMatrix integerWeightMatrix_counit
          f.toCoalgHom) ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) =
        Matrix.diagonal (fun i : Fin 2 =>
          MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (6 : ℤ) else 14)) (1 : ℕ)) ∧
      (↑U⁻¹ : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) =
        Matrix.diagonal (fun i : Fin 2 =>
          MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (-6 : ℤ) else -14))
            (1 : ℕ)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [integerWeightMatrixUnit] using
      coefficientMatrixUnit_map (R := ℕ) integerWeightMatrix integerWeightMatrix_comul
        integerWeightMatrix_counit
        (MonoidAlgebra.mapDomainBialgHom ℕ (powMonoidHom (α := Multiplicative ℤ) 2))
  · rw [Units.coe_map]
    simp only [integerWeightMatrixUnit, coe_coefficientMatrixUnit,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    rw [integerWeightMatrix, Matrix.diagonal_map (map_zero _)]
    apply congrArg Matrix.diagonal
    funext i
    rw [doubleWeight_single]
    fin_cases i <;> rfl
  · rw [Units.coe_map_inv, integerWeightMatrixUnit_inv_eq]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    rw [Matrix.diagonal_map (map_zero _)]
    apply congrArg Matrix.diagonal
    funext i
    rw [doubleWeight_single]
    fin_cases i <;> rfl

/-- The four doubled supports have coefficient `1`; the original, identity and opposite-sign
supports at the first diagonal entry have coefficient `0`. -/
theorem integerWeightMatrixUnit_map_double_coefficients :
    let f := MonoidAlgebra.mapDomainBialgHom ℕ (powMonoidHom (α := Multiplicative ℤ) 2)
    let U := Units.map (RingHom.mapMatrix (m := Fin 2) f.toAlgHom.toRingHom).toMonoidHom
      integerWeightMatrixUnit
    ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (6 : ℤ)) = 1 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1).coeff (Multiplicative.ofAdd (14 : ℤ)) = 1 ∧
      ((↑U⁻¹ : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (-6 : ℤ)) = 1 ∧
      ((↑U⁻¹ : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1).coeff (Multiplicative.ofAdd (-14 : ℤ)) = 1 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (3 : ℤ)) = 0 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (0 : ℤ)) = 0 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (-6 : ℤ)) = 0 := by
  dsimp only
  rw [integerWeightMatrixUnit_map_double.2.1, integerWeightMatrixUnit_map_double.2.2]
  have hsupport : Multiplicative.ofAdd (6 : ℤ) ≠ (Multiplicative.ofAdd (6 : ℤ))⁻¹ := by
    decide
  simp [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hsupport]

/-- Coefficients show that doubling is not the identity coefficient morphism, that its matrix
image differs from the original and identity, and that the image and inverse differ. -/
theorem integerWeightMatrixUnit_map_double_ne :
    let f := MonoidAlgebra.mapDomainBialgHom ℕ (powMonoidHom (α := Multiplicative ℤ) 2)
    let U := Units.map (RingHom.mapMatrix (m := Fin 2) f.toAlgHom.toRingHom).toMonoidHom
      integerWeightMatrixUnit
    f ≠ BialgHom.id ℕ (MonoidAlgebra ℕ (Multiplicative ℤ)) ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠
        integerWeightMatrix ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠ 1 ∧
      (↑U⁻¹ : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠
        (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) := by
  dsimp only
  have hcoeff := integerWeightMatrixUnit_map_double_coefficients
  dsimp only at hcoeff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h6 := congrArg (fun g : MonoidAlgebra ℕ (Multiplicative ℤ) →ₐc[ℕ]
        MonoidAlgebra ℕ (Multiplicative ℤ) =>
      (g (MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ))).coeff
        (Multiplicative.ofAdd (6 : ℤ))) h
    rw [doubleWeight_single] at h6
    simp [MonoidAlgebra.coeff_single] at h6
  · intro h
    have h6 := hcoeff.1
    rw [h] at h6
    simp [integerWeightMatrix, MonoidAlgebra.coeff_single] at h6
  · intro h
    have h0 := hcoeff.2.2.2.2.2.1
    rw [h] at h0
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] at h0
  · intro h
    have hneg := hcoeff.2.2.1
    rw [h, hcoeff.2.2.2.2.2.2] at hneg
    exact Nat.zero_ne_one hneg

/-- Simultaneous row-and-column swapping interchanges the supports `3,7`, and also
interchanges the inverse supports `-3,-7`, as predicted by unit reindexing naturality. -/
theorem integerWeightMatrixUnit_reindex_swap :
    let e := Equiv.swap (0 : Fin 2) 1
    let U := Units.map
      (Matrix.reindexRingEquiv (MonoidAlgebra ℕ (Multiplicative ℤ)) e).toRingHom.toMonoidHom
      integerWeightMatrixUnit
    U = coefficientMatrixUnit (R := ℕ) (Matrix.reindex e e integerWeightMatrix)
        (Coalgebra.coefficientMatrix_comul_reindex integerWeightMatrix integerWeightMatrix_comul e)
        (Coalgebra.coefficientMatrix_counit_reindex integerWeightMatrix
          integerWeightMatrix_counit e) ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) =
        Matrix.diagonal (fun i : Fin 2 =>
          MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (7 : ℤ) else 3)) (1 : ℕ)) ∧
      (↑U⁻¹ : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) =
        Matrix.diagonal (fun i : Fin 2 =>
          MonoidAlgebra.single (Multiplicative.ofAdd (if i = 0 then (-7 : ℤ) else -3))
            (1 : ℕ)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [integerWeightMatrixUnit] using
      coefficientMatrixUnit_reindex (R := ℕ) integerWeightMatrix integerWeightMatrix_comul
        integerWeightMatrix_counit (Equiv.swap (0 : Fin 2) 1)
  · rw [Units.coe_map]
    simp only [integerWeightMatrixUnit, coe_coefficientMatrixUnit]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [integerWeightMatrix, Matrix.reindex_apply]
  · rw [Units.coe_map_inv, integerWeightMatrixUnit_inv_eq]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.reindex_apply]

/-- The swapped diagonal and inverse supports retain coefficient `1`, while the first
original, identity and opposite-sign supports have coefficient `0`. -/
theorem integerWeightMatrixUnit_reindex_swap_coefficients :
    let e := Equiv.swap (0 : Fin 2) 1
    let U := Units.map
      (Matrix.reindexRingEquiv (MonoidAlgebra ℕ (Multiplicative ℤ)) e).toRingHom.toMonoidHom
      integerWeightMatrixUnit
    ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (7 : ℤ)) = 1 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1).coeff (Multiplicative.ofAdd (3 : ℤ)) = 1 ∧
      ((↑U⁻¹ : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (-7 : ℤ)) = 1 ∧
      ((↑U⁻¹ : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 1 1).coeff (Multiplicative.ofAdd (-3 : ℤ)) = 1 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (3 : ℤ)) = 0 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (0 : ℤ)) = 0 ∧
      ((↑U : Matrix (Fin 2) (Fin 2)
        (MonoidAlgebra ℕ (Multiplicative ℤ))) 0 0).coeff (Multiplicative.ofAdd (-7 : ℤ)) = 0 := by
  dsimp only
  rw [integerWeightMatrixUnit_reindex_swap.2.1, integerWeightMatrixUnit_reindex_swap.2.2]
  have hsupport : Multiplicative.ofAdd (7 : ℤ) ≠ (Multiplicative.ofAdd (7 : ℤ))⁻¹ := by
    decide
  simp [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hsupport]

/-- The index swap is not the identity equivalence. Coefficients distinguish its matrix
image from the original and identity, and distinguish its inverse from the image. -/
theorem integerWeightMatrixUnit_reindex_swap_ne :
    let e := Equiv.swap (0 : Fin 2) 1
    let U := Units.map
      (Matrix.reindexRingEquiv (MonoidAlgebra ℕ (Multiplicative ℤ)) e).toRingHom.toMonoidHom
      integerWeightMatrixUnit
    e ≠ Equiv.refl (Fin 2) ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠
        integerWeightMatrix ∧
      (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠ 1 ∧
      (↑U⁻¹ : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) ≠
        (↑U : Matrix (Fin 2) (Fin 2) (MonoidAlgebra ℕ (Multiplicative ℤ))) := by
  dsimp only
  have hcoeff := integerWeightMatrixUnit_reindex_swap_coefficients
  dsimp only at hcoeff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun e : Fin 2 ≃ Fin 2 => e 0) h
    simp at h0
  · intro h
    have h7 := hcoeff.1
    rw [h] at h7
    simp [integerWeightMatrix, MonoidAlgebra.coeff_single] at h7
  · intro h
    have h0 := hcoeff.2.2.2.2.2.1
    rw [h] at h0
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] at h0
  · intro h
    have hneg := hcoeff.2.2.1
    rw [h, hcoeff.2.2.2.2.2.2] at hneg
    exact Nat.zero_ne_one hneg

/-- The counit identifies the distinct group singles at supports `0` and `3`, both with
image `1`. In particular, this coefficient morphism is not injective. -/
theorem integerWeight_counit_noninjective :
    let f := Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ (Multiplicative ℤ))
    f (MonoidAlgebra.single (Multiplicative.ofAdd (0 : ℤ)) (1 : ℕ)) = 1 ∧
      f (MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ)) = 1 ∧
      MonoidAlgebra.single (Multiplicative.ofAdd (0 : ℤ)) (1 : ℕ) ≠
        MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ) ∧
      ¬Function.Injective f := by
  dsimp only
  have hdistinct : MonoidAlgebra.single (Multiplicative.ofAdd (0 : ℤ)) (1 : ℕ) ≠
      MonoidAlgebra.single (Multiplicative.ofAdd (3 : ℤ)) (1 : ℕ) := by
    intro h
    have h0 := congrArg (fun a : MonoidAlgebra ℕ (Multiplicative ℤ) =>
      a.coeff (Multiplicative.ofAdd (0 : ℤ))) h
    simp [MonoidAlgebra.coeff_single] at h0
  refine ⟨by simp, by simp, hdistinct, ?_⟩
  intro h
  apply hdistinct
  apply h
  simp

/-- The noninjective counit maps the integer-weight matrix to the identity and, by
coefficient-map naturality, maps its coefficient-matrix unit to the identity unit. -/
theorem integerWeightMatrixUnit_map_counit :
    let f := Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ (Multiplicative ℤ))
    let U := Units.map (RingHom.mapMatrix (m := Fin 2) f.toAlgHom.toRingHom).toMonoidHom
      integerWeightMatrixUnit
    U = coefficientMatrixUnit (R := ℕ) (integerWeightMatrix.map f)
        (Coalgebra.coefficientMatrix_comul_map integerWeightMatrix integerWeightMatrix_comul
          f.toCoalgHom)
        (Coalgebra.coefficientMatrix_counit_map integerWeightMatrix integerWeightMatrix_counit
          f.toCoalgHom) ∧
      integerWeightMatrix.map f = 1 ∧ U = 1 ∧ U⁻¹ = 1 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa only [integerWeightMatrixUnit] using
      coefficientMatrixUnit_map (R := ℕ) integerWeightMatrix integerWeightMatrix_comul
        integerWeightMatrix_counit
        (Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ (Multiplicative ℤ)))
  · let f := Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ (Multiplicative ℤ))
    have hM : integerWeightMatrix.map f = 1 := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [integerWeightMatrix, f]
    have hU : Units.map (RingHom.mapMatrix (m := Fin 2)
        f.toAlgHom.toRingHom).toMonoidHom integerWeightMatrixUnit = 1 := by
      apply Units.ext
      simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        RingHom.mapMatrix_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        BialgHom.coe_toAlgHom, integerWeightMatrixUnit, coe_coefficientMatrixUnit,
        Units.val_one] using hM
    exact ⟨hM, hU, by rw [hU]; simp⟩

end IntegerWeightTransport

section EmptyIndex

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- The identity matrix on the empty index satisfies the matrix comultiplication law. -/
theorem emptyMatrix_comul (i j : Empty) :
    Coalgebra.comul (R := R) ((1 : Matrix Empty Empty A) i j) =
      ∑ k : Empty, (1 : Matrix Empty Empty A) i k ⊗ₜ[R] (1 : Matrix Empty Empty A) k j := by
  exact i.elim

/-- The identity matrix on the empty index satisfies the counit Kronecker-delta law. -/
theorem emptyMatrix_counit (i j : Empty) :
    Coalgebra.counit (R := R) ((1 : Matrix Empty Empty A) i j) = if i = j then 1 else 0 := by
  exact i.elim

/-- The coefficient-matrix unit on the empty index, with no nonempty-index premise. -/
def emptyCoefficientMatrixUnit : (Matrix Empty Empty A)ˣ :=
  coefficientMatrixUnit (R := R) (1 : Matrix Empty Empty A)
    (emptyMatrix_comul (R := R)) (emptyMatrix_counit (R := R))

/-- On the empty index, the coefficient-matrix unit and its inverse are the unique unit. -/
theorem emptyCoefficientMatrixUnit_eq :
    emptyCoefficientMatrixUnit (R := R) (A := A) = 1 ∧
      (emptyCoefficientMatrixUnit (R := R) (A := A))⁻¹ = 1 ∧
      ∀ U : (Matrix Empty Empty A)ˣ, U = emptyCoefficientMatrixUnit (R := R) := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, fun U => Subsingleton.elim U _⟩

end EmptyIndex

section EmptyIndexTransport

variable {R : Type u} {A : Type v} {B : Type v'}
  [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Semiring B] [HopfAlgebra R B]

/-- Coefficient-map naturality on the empty index sends its coefficient-matrix unit to the
empty-index unit over the target Hopf algebra, with inverse the identity. -/
theorem emptyCoefficientMatrixUnit_map (f : A →ₐc[R] B) :
    Units.map (RingHom.mapMatrix (m := Empty) f.toAlgHom.toRingHom).toMonoidHom
        (emptyCoefficientMatrixUnit (R := R) (A := A)) =
      emptyCoefficientMatrixUnit (R := R) (A := B) ∧
      (Units.map (RingHom.mapMatrix (m := Empty) f.toAlgHom.toRingHom).toMonoidHom
        (emptyCoefficientMatrixUnit (R := R) (A := A)))⁻¹ = 1 := by
  constructor
  · calc
      Units.map (RingHom.mapMatrix (m := Empty) f.toAlgHom.toRingHom).toMonoidHom
          (emptyCoefficientMatrixUnit (R := R) (A := A)) =
        coefficientMatrixUnit (R := R) ((1 : Matrix Empty Empty A).map f)
          (Coalgebra.coefficientMatrix_comul_map (1 : Matrix Empty Empty A)
            (emptyMatrix_comul (R := R)) f.toCoalgHom)
          (Coalgebra.coefficientMatrix_counit_map (1 : Matrix Empty Empty A)
            (emptyMatrix_counit (R := R)) f.toCoalgHom) := by
          simpa only [emptyCoefficientMatrixUnit] using
            coefficientMatrixUnit_map (R := R) (1 : Matrix Empty Empty A)
              (emptyMatrix_comul (R := R)) (emptyMatrix_counit (R := R)) f
      _ = emptyCoefficientMatrixUnit (R := R) (A := B) := Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end EmptyIndexTransport

section EmptyIndexReindex

variable {R : Type u} {A : Type v}
  [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Reindexing the empty coefficient-matrix unit into an independently chosen universe
again gives the identity unit and identity inverse. -/
theorem emptyCoefficientMatrixUnit_reindex_ulift :
    let e : Empty ≃ ULift.{w} Empty := Equiv.ulift.symm
    let U := Units.map (Matrix.reindexRingEquiv A e).toRingHom.toMonoidHom
      (emptyCoefficientMatrixUnit (R := R) (A := A))
    U = 1 ∧ U⁻¹ = 1 := by
  dsimp only
  constructor
  · calc
      Units.map (Matrix.reindexRingEquiv A
          (Equiv.ulift.symm : Empty ≃ ULift.{w} Empty)).toRingHom.toMonoidHom
          (emptyCoefficientMatrixUnit (R := R) (A := A)) =
        coefficientMatrixUnit (R := R)
          (Matrix.reindex (Equiv.ulift.symm : Empty ≃ ULift.{w} Empty) Equiv.ulift.symm
            (1 : Matrix Empty Empty A))
          (Coalgebra.coefficientMatrix_comul_reindex (1 : Matrix Empty Empty A)
            (emptyMatrix_comul (R := R)) Equiv.ulift.symm)
          (Coalgebra.coefficientMatrix_counit_reindex (1 : Matrix Empty Empty A)
            (emptyMatrix_counit (R := R)) Equiv.ulift.symm) := by
          simpa only [emptyCoefficientMatrixUnit] using
            coefficientMatrixUnit_reindex (R := R) (1 : Matrix Empty Empty A)
              (emptyMatrix_comul (R := R)) (emptyMatrix_counit (R := R))
              (Equiv.ulift.symm : Empty ≃ ULift.{w} Empty)
      _ = 1 := Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end EmptyIndexReindex

end HopfAlgebra
