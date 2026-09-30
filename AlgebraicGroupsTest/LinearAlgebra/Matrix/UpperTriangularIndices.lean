/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices

/-!
# Ordinary-import clients of upper-triangular indexing

Diagonal, strict and retained positions are exercised without a finite-index
assumption; cardinality examples use finite and empty index types.
-/

public section

set_option warningAsError true

namespace AlgebraicGroupsTest.LinearAlgebra.Matrix.UpperTriangularIndices

variable (ι : Type*) [LinearOrder ι]

example (i : ι) :
    Matrix.upperTriangularIndicesEquiv ι ⟨(i, i), le_rfl⟩ = Sum.inl i :=
  Matrix.upperTriangularIndicesEquiv_diagonal ι i

example (p : {p : ι × ι // p.1 < p.2}) :
    Matrix.upperTriangularIndicesEquiv ι ⟨p.1, p.2.le⟩ = Sum.inr p :=
  Matrix.upperTriangularIndicesEquiv_strict ι p

example (i : ι) :
    (Matrix.upperTriangularIndicesEquiv ι).symm (Sum.inl i) =
      ⟨(i, i), le_rfl⟩ :=
  Matrix.upperTriangularIndicesEquiv_symm_inl ι i

example (p : {p : ι × ι // p.1 < p.2}) :
    (Matrix.upperTriangularIndicesEquiv ι).symm (Sum.inr p) =
      ⟨p.1, p.2.le⟩ :=
  Matrix.upperTriangularIndicesEquiv_symm_inr ι p

example (p : {p : ι × ι // p.1 ≤ p.2}) :
    Sum.elim (fun i => (i, i)) Subtype.val (Matrix.upperTriangularIndicesEquiv ι p) =
      p.1 :=
  Matrix.upperTriangularIndicesEquiv_coordinates ι p

example (p : {p : ι × ι // ¬ p.2 < p.1}) :
    (Matrix.upperTriangularRetainedEquiv ι p).1 = p.1 :=
  Matrix.upperTriangularRetainedEquiv_val ι p

example (p : {p : ι × ι // p.1 ≤ p.2}) :
    ((Matrix.upperTriangularRetainedEquiv ι).symm p).1 = p.1 :=
  Matrix.upperTriangularRetainedEquiv_symm_val ι p

example (p : {p : ι × ι // ¬ p.2 < p.1}) : p.1.1 ≤ p.1.2 :=
  (Matrix.upperTriangularRetainedEquiv ι p).2

example (i : ι) :
    ((Matrix.upperTriangularRetainedIndicesEquiv ι).symm (Sum.inl i)).1 =
      (i, i) :=
  Matrix.upperTriangularRetainedIndicesEquiv_symm_inl_val ι i

example (p : {p : ι × ι // p.1 < p.2}) :
    ((Matrix.upperTriangularRetainedIndicesEquiv ι).symm (Sum.inr p)).1 =
      p.1 :=
  Matrix.upperTriangularRetainedIndicesEquiv_symm_inr_val ι p

example [IsEmpty ι] : IsEmpty {p : ι × ι // p.1 ≤ p.2} := inferInstance

example [Fintype ι] :
    Fintype.card {p : ι × ι // p.1 ≤ p.2} =
      Fintype.card ι + (Fintype.card ι).choose 2 :=
  Matrix.card_upperTriangularIndices ι

example [Fintype ι] :
    Fintype.card {p : ι × ι // ¬ p.2 < p.1} =
      Fintype.card ι + (Fintype.card ι).choose 2 :=
  Matrix.card_upperTriangularRetainedIndices ι

example : Fintype.card {p : Fin 0 × Fin 0 // p.1 ≤ p.2} = 0 := by
  simp

example : Fintype.card {p : Fin 1 × Fin 1 // p.1 ≤ p.2} = 1 := by
  simp

example : Fintype.card {p : Fin 3 × Fin 3 // ¬ p.2 < p.1} = 6 := by
  simpa using Matrix.card_upperTriangularRetainedIndices (Fin 3)

end AlgebraicGroupsTest.LinearAlgebra.Matrix.UpperTriangularIndices
