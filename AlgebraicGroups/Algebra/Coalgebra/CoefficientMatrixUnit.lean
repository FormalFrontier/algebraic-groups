/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Units from finite Hopf coefficient matrices

A finite square matrix satisfying the matrix comultiplication and counit laws
has entrywise antipode as its two-sided inverse. The construction takes values
in the units of a matrix semiring, without a commutativity assumption on the
Hopf algebra or a nonempty-index assumption.

The two inverse identities are `HopfAlgebra.coefficientMatrix_mul_antipode` and
`HopfAlgebra.antipode_mul_coefficientMatrix`. The concrete unit
`HopfAlgebra.coefficientMatrixUnit` has value equal to the input matrix and
unit inverse equal to its entrywise antipode. Coercion and entry lemmas describe
both matrices without unfolding the construction. The coefficient laws transport
along coalgebra homomorphisms and simultaneous row-and-column reindexing.
The associated unit transports along bialgebra homomorphisms and index
equivalences via the standard maps on units.

## References

The proofs adapt Mathlib's `Coalgebra.Repr` and the antipode identities
`HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit` and
`HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit`, using Mathlib's matrix
and units APIs. Transport uses Mathlib's `CoalgHom` compatibility laws,
`TensorProduct.map`, equivalence reindexing of finite sums, `Units.map`, and
`Units.ext`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public noncomputable section

open scoped BigOperators
open TensorProduct

universe u v v' w w'

namespace Coalgebra

section CoefficientMatrixMap

variable {R : Type u} {A : Type v} {B : Type v'} {ι : Type w}
  [CommSemiring R]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]

/-- A coalgebra homomorphism preserves the comultiplication law of a coefficient matrix. -/
theorem coefficientMatrix_comul_map [Fintype ι]
    (M : Matrix ι ι A)
    (hΔ : ∀ i j, comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
    (f : A →ₗc[R] B) :
    ∀ i j, comul (R := R) ((M.map f) i j) =
      ∑ k, (M.map f) i k ⊗ₜ[R] (M.map f) k j := by
  intro i j
  simp only [Matrix.map_apply]
  calc
    comul (R := R) (f (M i j)) =
        _root_.TensorProduct.map f.toLinearMap f.toLinearMap (comul (R := R) (M i j)) :=
      (CoalgHomClass.map_comp_comul_apply f (M i j)).symm
    _ = ∑ k, f (M i k) ⊗ₜ[R] f (M k j) := by
      simp only [hΔ i j, map_sum, _root_.TensorProduct.map_tmul,
        CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap]

/-- A coalgebra homomorphism preserves the counit law of a coefficient matrix. -/
theorem coefficientMatrix_counit_map [DecidableEq ι]
    (M : Matrix ι ι A)
    (hε : ∀ i j, counit (R := R) (M i j) = if i = j then 1 else 0)
    (f : A →ₗc[R] B) :
    ∀ i j, counit (R := R) ((M.map f) i j) = if i = j then 1 else 0 := by
  intro i j
  simpa only [Matrix.map_apply, CoalgHomClass.counit_comp_apply] using hε i j

end CoefficientMatrixMap

section CoefficientMatrixReindex

variable {R : Type u} {A : Type v} {ι : Type w} {κ : Type w'}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

/-- Simultaneous reindexing preserves the comultiplication law of a coefficient matrix. -/
theorem coefficientMatrix_comul_reindex [Fintype ι] [Fintype κ]
    (M : Matrix ι ι A)
    (hΔ : ∀ i j, comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
    (e : ι ≃ κ) :
    ∀ i j, comul (R := R) (Matrix.reindex e e M i j) =
      ∑ k, Matrix.reindex e e M i k ⊗ₜ[R] Matrix.reindex e e M k j := by
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hΔ (e.symm i) (e.symm j)]
  exact (e.symm.sum_comp fun k => M (e.symm i) k ⊗ₜ[R] M k (e.symm j)).symm

/-- Simultaneous reindexing preserves the counit law of a coefficient matrix. -/
theorem coefficientMatrix_counit_reindex [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι ι A)
    (hε : ∀ i j, counit (R := R) (M i j) = if i = j then 1 else 0)
    (e : ι ≃ κ) :
    ∀ i j, counit (R := R) (Matrix.reindex e e M i j) = if i = j then 1 else 0 := by
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm.injective.eq_iff] using
    hε (e.symm i) (e.symm j)

end CoefficientMatrixReindex

end Coalgebra

namespace HopfAlgebra

section CoefficientMatrix

variable {R : Type u} {A : Type v} {ι : Type w}
  [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Fintype ι] [DecidableEq ι]
  (M : Matrix ι ι A)
  (hΔ : ∀ i j, Coalgebra.comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
  (hε : ∀ i j, Coalgebra.counit (R := R) (M i j) = if i = j then 1 else 0)

/-- The tensor-sum representation of a coefficient matrix entry. -/
private def entryRepr (i j : ι) : Coalgebra.Repr R (M i j) ι where
  index := Finset.univ
  left k := M i k
  right k := M k j
  eq := (hΔ i j).symm

include hΔ hε

/-- Applying the antipode entrywise gives a right inverse of a coefficient matrix. -/
theorem coefficientMatrix_mul_antipode : M * M.map (antipode R) = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply]
  calc
    ∑ k, M i k * antipode R (M k j) =
        algebraMap R A (Coalgebra.counit (R := R) (M i j)) :=
      sum_mul_antipode_eq_algebraMap_counit (entryRepr M hΔ i j)
    _ = if i = j then 1 else 0 := by
      rw [hε i j]
      split_ifs <;> simp

/-- Applying the antipode entrywise gives a left inverse of a coefficient matrix. -/
theorem antipode_mul_coefficientMatrix : M.map (antipode R) * M = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply]
  calc
    ∑ k, antipode R (M i k) * M k j =
        algebraMap R A (Coalgebra.counit (R := R) (M i j)) :=
      sum_antipode_mul_eq_algebraMap_counit (entryRepr M hΔ i j)
    _ = if i = j then 1 else 0 := by
      rw [hε i j]
      split_ifs <;> simp

/-- A finite Hopf coefficient matrix as a unit, with entrywise antipode as inverse. -/
def coefficientMatrixUnit : (Matrix ι ι A)ˣ :=
  Units.mk M (M.map (antipode R))
    (coefficientMatrix_mul_antipode M hΔ hε)
    (antipode_mul_coefficientMatrix M hΔ hε)

/-- The value of the coefficient matrix unit is the input matrix. -/
@[simp]
theorem coe_coefficientMatrixUnit :
    (↑(coefficientMatrixUnit M hΔ hε) : Matrix ι ι A) = M :=
  rfl

/-- The value of the unit inverse is the entrywise antipode, without a transpose. -/
@[simp]
theorem coe_coefficientMatrixUnit_inv :
    (↑((coefficientMatrixUnit M hΔ hε)⁻¹) : Matrix ι ι A) = M.map (antipode R) :=
  rfl

/-- An entry of the coefficient matrix unit is the corresponding input entry. -/
@[simp]
theorem coefficientMatrixUnit_apply (i j : ι) :
    (↑(coefficientMatrixUnit M hΔ hε) : Matrix ι ι A) i j = M i j := by
  simp only [coe_coefficientMatrixUnit]

/-- An entry of the unit inverse is the antipode of the corresponding input entry. -/
@[simp]
theorem coefficientMatrixUnit_inv_apply (i j : ι) :
    (↑((coefficientMatrixUnit M hΔ hε)⁻¹) : Matrix ι ι A) i j = antipode R (M i j) := by
  simp only [coe_coefficientMatrixUnit_inv, Matrix.map_apply]

/-- A finite Hopf coefficient matrix is a unit in the matrix semiring. -/
theorem isUnit_coefficientMatrix : IsUnit M := by
  exact (coefficientMatrixUnit M hΔ hε).isUnit

end CoefficientMatrix

section CoefficientMatrixMap

variable {R : Type u} {A : Type v} {B : Type v'} {ι : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Fintype ι] [DecidableEq ι]

/-- Mapping a coefficient matrix unit along a bialgebra homomorphism gives the unit
of the entrywise image matrix. -/
theorem coefficientMatrixUnit_map
    (M : Matrix ι ι A)
    (hΔ : ∀ i j, Coalgebra.comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
    (hε : ∀ i j, Coalgebra.counit (R := R) (M i j) = if i = j then 1 else 0)
    (f : A →ₐc[R] B) :
    Units.map (RingHom.mapMatrix (m := ι) f.toAlgHom.toRingHom).toMonoidHom
      (coefficientMatrixUnit (R := R) M hΔ hε) =
    coefficientMatrixUnit (R := R) (M.map f)
      (Coalgebra.coefficientMatrix_comul_map M hΔ f.toCoalgHom)
      (Coalgebra.coefficientMatrix_counit_map M hε f.toCoalgHom) := by
  apply Units.ext
  simp only [Units.coe_map, coe_coefficientMatrixUnit, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]

end CoefficientMatrixMap

section CoefficientMatrixReindex

variable {R : Type u} {A : Type v} {ι : Type w} {κ : Type w'}
  [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Simultaneous reindexing of a coefficient matrix unit gives the unit of the
reindexed matrix. -/
theorem coefficientMatrixUnit_reindex
    (M : Matrix ι ι A)
    (hΔ : ∀ i j, Coalgebra.comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
    (hε : ∀ i j, Coalgebra.counit (R := R) (M i j) = if i = j then 1 else 0)
    (e : ι ≃ κ) :
    Units.map (Matrix.reindexRingEquiv A e).toRingHom.toMonoidHom
      (coefficientMatrixUnit (R := R) M hΔ hε) =
    coefficientMatrixUnit (R := R) (Matrix.reindex e e M)
      (Coalgebra.coefficientMatrix_comul_reindex M hΔ e)
      (Coalgebra.coefficientMatrix_counit_reindex M hε e) := by
  apply Units.ext
  simp only [Units.coe_map, coe_coefficientMatrixUnit, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    Matrix.coe_reindexRingEquiv]

end CoefficientMatrixReindex

end HopfAlgebra
