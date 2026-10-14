/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoefficientMatrixUnit
public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Algebra-generating coefficients in a noncommutative group algebra

The rational group algebra of the free group on two generators has a diagonal
four-by-four coefficient matrix. Its diagonal lists both generators and both
inverse group elements, each with coefficient `1`. The entries satisfy the
canonical coalgebra matrix laws and generate the whole algebra as an algebra.
Including the inverses matters: a subalgebra is not closed under inversion.

This algebra is of finite type but is neither commutative nor finite as a
rational module. The linear span of the sixteen matrix entries is finitely
generated and proper. Thus algebra generation by the entries does not assert
that their linear span is the entire ambient coalgebra.

The matrix also exercises the existing Hopf coefficient-matrix unit API, in
both multiplication orders and at an inverse diagonal entry. The canonical
coalgebra and Hopf instances are used throughout; the group-indexed basis is
used only to prove failure of module finiteness.

## References

These examples use Mathlib's free-group induction and reduced-word API,
monoid-algebra Hopf structure, standard monoid-algebra basis, and finite-type
instances for finitely generated groups. The matrix-unit observations use
`HopfAlgebra.coefficientMatrixUnit` and its public API.
-/

@[expose] public noncomputable section

open scoped BigOperators
open TensorProduct

namespace CoalgebraExamples.NoncommutativeFiniteAlgebraGenerators

/-- The rational group algebra of the free group on two generators. -/
abbrev GroupAlgebra := MonoidAlgebra ℚ (FreeGroup Bool)

/-- The first generator, its inverse, the second generator, and its inverse. -/
def groupCoordinates : Fin 4 → FreeGroup Bool :=
  ![FreeGroup.of false, (FreeGroup.of false)⁻¹,
    FreeGroup.of true, (FreeGroup.of true)⁻¹]

/-- The diagonal matrix of the four group-basis singles with coefficient `1`. -/
def coefficientMatrix : Matrix (Fin 4) (Fin 4) GroupAlgebra :=
  Matrix.diagonal fun i => MonoidAlgebra.single (groupCoordinates i) (1 : ℚ)

/-- Each diagonal entry is its designated single, and every off-diagonal entry is zero. -/
@[simp]
theorem coefficientMatrix_apply (i j : Fin 4) :
    coefficientMatrix i j =
      if i = j then MonoidAlgebra.single (groupCoordinates i) (1 : ℚ) else 0 :=
  Matrix.diagonal_apply _ i j

/-- The diagonal group-basis matrix satisfies the coefficient comultiplication law. -/
theorem coefficientMatrix_comul (i j : Fin 4) :
    Coalgebra.comul (R := ℚ) (coefficientMatrix i j) =
      ∑ k, coefficientMatrix i k ⊗ₜ[ℚ] coefficientMatrix k j := by
  by_cases hij : i = j
  · subst j
    calc
      Coalgebra.comul (R := ℚ) (coefficientMatrix i i) =
          coefficientMatrix i i ⊗ₜ[ℚ] coefficientMatrix i i := by
        simp [coefficientMatrix]
      _ = ∑ k, coefficientMatrix i k ⊗ₜ[ℚ] coefficientMatrix k i := by
        symm
        apply Finset.sum_eq_single i
        · intro k _ hki
          simp [hki.symm]
        · simp
  · rw [coefficientMatrix_apply, ite_eq_right hij, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [hij]
    · simp [hik]

/-- The counit of a matrix entry is its Kronecker delta. -/
theorem coefficientMatrix_counit (i j : Fin 4) :
    Coalgebra.counit (R := ℚ) (coefficientMatrix i j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [coefficientMatrix]
  · simp [hij]

private theorem diagonal_mem_adjoin (i : Fin 4) :
    MonoidAlgebra.single (groupCoordinates i) (1 : ℚ) ∈
      Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix)) := by
  apply Algebra.subset_adjoin
  exact ⟨(i, i), by simp [Function.uncurry]⟩

private theorem single_one_mem_adjoin (g : FreeGroup Bool) :
    MonoidAlgebra.single g (1 : ℚ) ∈
      Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix)) := by
  refine FreeGroup.induction_on g ?_ ?_ ?_ ?_
  · simpa only [MonoidAlgebra.one_def] using
      (Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix))).one_mem
  · intro b
    cases b
    · simpa [groupCoordinates] using diagonal_mem_adjoin 0
    · simpa [groupCoordinates] using diagonal_mem_adjoin 2
  · intro b _
    cases b
    · simpa [groupCoordinates] using diagonal_mem_adjoin 1
    · simpa [groupCoordinates] using diagonal_mem_adjoin 3
  · intro x y hx hy
    simpa only [MonoidAlgebra.single_mul_single, one_mul] using
      (Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix))).mul_mem hx hy

/-- The four diagonal entries generate the entire group algebra as a rational algebra. -/
theorem coefficientMatrix_adjoin_eq_top :
    Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix)) = ⊤ := by
  apply top_unique
  intro f _
  refine MonoidAlgebra.induction_on f ?_ ?_ ?_
  · intro g
    simpa only [MonoidAlgebra.of_apply] using single_one_mem_adjoin g
  · intro x y hx hy
    exact (Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix))).add_mem hx hy
  · intro r x hx
    exact (Algebra.adjoin ℚ (Set.range (Function.uncurry coefficientMatrix))).smul_mem hx r

/-- The canonical finite-type instance comes from finite generation of the free group. -/
theorem algebra_finiteType : Algebra.FiniteType ℚ GroupAlgebra := inferInstance

/-- The free-group algebra is generated by the entries of a finite matrix unit. -/
theorem exists_coefficientMatrixUnit_adjoin_eq_top :
    ∃ (n : ℕ) (U : (Matrix (Fin n) (Fin n) GroupAlgebra)ˣ),
      Algebra.adjoin ℚ
        (Set.range (Function.uncurry (↑U : Matrix (Fin n) (Fin n) GroupAlgebra))) = ⊤ := by
  obtain ⟨n, M, hΔ, hε, hgen⟩ :=
    Coalgebra.exists_coefficientMatrix_adjoin_eq_top (K := ℚ) (A := GroupAlgebra)
  let U := HopfAlgebra.coefficientMatrixUnit (R := ℚ) M hΔ hε
  refine ⟨n, U, ?_⟩
  have hU : (↑U : Matrix (Fin n) (Fin n) GroupAlgebra) = M :=
    HopfAlgebra.coe_coefficientMatrixUnit M hΔ hε
  rw [hU]
  exact hgen

private theorem generator_products_ne :
    FreeGroup.of false * FreeGroup.of true ≠ FreeGroup.of true * FreeGroup.of false := by
  intro h
  have hwords :
      FreeGroup.reduce ([(false, true)] ++ [(true, true)]) =
        FreeGroup.reduce ([(true, true)] ++ [(false, true)]) := by
    simpa only [FreeGroup.toWord_mul, FreeGroup.toWord_of] using
      congrArg FreeGroup.toWord h
  exact (by decide :
    FreeGroup.reduce ([(false, true)] ++ [(true, true)]) ≠
      FreeGroup.reduce ([(true, true)] ++ [(false, true)])) hwords

/-- The two positive generator singles are an explicit noncommutativity witness. -/
theorem generators_mul_ne :
    (MonoidAlgebra.single (FreeGroup.of false) (1 : ℚ) : GroupAlgebra) *
        MonoidAlgebra.single (FreeGroup.of true) (1 : ℚ) ≠
      MonoidAlgebra.single (FreeGroup.of true) (1 : ℚ) *
        MonoidAlgebra.single (FreeGroup.of false) (1 : ℚ) := by
  intro h
  apply generator_products_ne
  apply MonoidAlgebra.single_left_injective (R := ℚ) (r := 1) one_ne_zero
  simpa only [MonoidAlgebra.single_mul_single, one_mul] using h

private theorem generator_powers_injective :
    Function.Injective (fun n : ℕ => (FreeGroup.of false : FreeGroup Bool) ^ n) := by
  intro m n h
  have hlength := congrArg (fun g : FreeGroup Bool => g.toWord.length) h
  simpa only [FreeGroup.toWord_of_pow, List.length_replicate] using hlength

/-- Distinct positive powers index an infinite linearly independent basis subfamily. -/
theorem not_moduleFinite : ¬ Module.Finite ℚ GroupAlgebra := by
  intro h
  let : Module.Finite ℚ GroupAlgebra := h
  exact (Module.Finite.not_linearIndependent_of_infinite
    ((MonoidAlgebra.basis (FreeGroup Bool) ℚ) ∘
      fun n : ℕ => (FreeGroup.of false : FreeGroup Bool) ^ n))
    ((MonoidAlgebra.basis (FreeGroup Bool) ℚ).linearIndependent.comp _
      generator_powers_injective)

/-- The rational linear span of all entries of the four-by-four matrix. -/
def coefficientSpan : Submodule ℚ GroupAlgebra :=
  Submodule.span ℚ (Set.range (Function.uncurry coefficientMatrix))

/-- The coefficient span is finitely generated because the entry index type is finite. -/
theorem coefficientSpan_fg : coefficientSpan.FG :=
  Submodule.fg_span (Set.finite_range (Function.uncurry coefficientMatrix))

/-- The coefficient span is proper, although the same entries algebra-generate
the ambient algebra. -/
theorem coefficientSpan_ne_top : coefficientSpan ≠ ⊤ := by
  intro htop
  have hfg : (⊤ : Submodule ℚ GroupAlgebra).FG := htop ▸ coefficientSpan_fg
  exact not_moduleFinite (Module.Finite.of_fg_top hfg)

/-- The existing Hopf matrix API gives both inverse multiplication orders. -/
theorem coefficientMatrix_antipode_inverse_orders :
    coefficientMatrix * coefficientMatrix.map (HopfAlgebra.antipode ℚ) = 1 ∧
      coefficientMatrix.map (HopfAlgebra.antipode ℚ) * coefficientMatrix = 1 := by
  exact ⟨HopfAlgebra.coefficientMatrix_mul_antipode coefficientMatrix
      coefficientMatrix_comul coefficientMatrix_counit,
    HopfAlgebra.antipode_mul_coefficientMatrix coefficientMatrix
      coefficientMatrix_comul coefficientMatrix_counit⟩

/-- The existing matrix unit retains the input and inverts the first group index in its inverse. -/
theorem coefficientMatrixUnit_value_and_inverse_entry :
    let U := HopfAlgebra.coefficientMatrixUnit (R := ℚ) coefficientMatrix
      coefficientMatrix_comul coefficientMatrix_counit
    (↑U : Matrix (Fin 4) (Fin 4) GroupAlgebra) = coefficientMatrix ∧
      (↑(U⁻¹) : Matrix (Fin 4) (Fin 4) GroupAlgebra) 0 0 =
        MonoidAlgebra.single ((FreeGroup.of false)⁻¹) (1 : ℚ) := by
  dsimp only
  constructor
  · exact HopfAlgebra.coe_coefficientMatrixUnit coefficientMatrix
      coefficientMatrix_comul coefficientMatrix_counit
  · rw [HopfAlgebra.coefficientMatrixUnit_inv_apply]
    simp [groupCoordinates]

end CoalgebraExamples.NoncommutativeFiniteAlgebraGenerators
