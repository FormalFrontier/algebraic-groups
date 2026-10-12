/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Coefficients
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Finite coalgebra coefficients over the natural numbers

The coalgebra `AddMonoidAlgebra ℕ ℤ` has a diagonal comultiplication on its
integer-indexed basis. Its finite basis families have ambient coordinate maps
obtained from `Finsupp.lapply`. These maps supply biorthogonal coordinates without
a field assumption.

The examples construct coefficient spaces for the basis elements at `3` and `7`,
individually and together. The pair also tests closure on a non-generator linear
combination. An empty coordinate family gives the zero coefficient space in the
same nonzero ambient coalgebra.
-/

@[expose] public section

open scoped TensorProduct
open AddMonoidAlgebra (single)

namespace CoalgebraCoefficientExamples

private noncomputable def integerCoordinate (g : ℤ) : AddMonoidAlgebra ℕ ℤ →ₗ[ℕ] ℕ :=
  (Finsupp.lapply g).comp (AddMonoidAlgebra.coeffLinearEquiv ℕ).toLinearMap

private theorem integerCoordinate_single (g h : ℤ) :
    integerCoordinate g (single h (1 : ℕ)) = if g = h then 1 else 0 := by
  simp [integerCoordinate, eq_comm]

-- The two hypotheses needed by the coefficient lemmas are proved from
-- coordinate projection and the diagonal comultiplication, respectively.
private theorem diagonal_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) (hg : Function.Injective g) :
    (∀ j, Coalgebra.comul (R := ℕ) (single (g j) (1 : ℕ)) =
      ∑ i, single (g i) (1 : ℕ) ⊗ₜ[ℕ]
        (if i = j then single (g j) (1 : ℕ) else 0)) ∧
    (∀ i j, integerCoordinate (g i) (single (g j) (1 : ℕ)) =
      if i = j then 1 else 0) := by
  constructor
  · intro j
    simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]
    simp [TensorProduct.tmul_ite]
  · intro i j
    rw [integerCoordinate_single]
    simp only [hg.eq_iff]

/-- A finite injectively indexed family of integer basis elements over `ℕ` is contained in a
finitely generated submodule whose comultiplication lands in the image of its tensor square. -/
theorem coefficient_space_of_indices {ι : Type*} [Finite ι]
    (g : ι → ℤ) (hg : Function.Injective g) :
    ∃ D : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      (∀ j, single (g j) (1 : ℕ) ∈ D) ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  classical
  let := Fintype.ofFinite ι
  let u : ι → AddMonoidAlgebra ℕ ℤ := fun i => single (g i) 1
  let a : ι → ι → AddMonoidAlgebra ℕ ℤ := fun i j => if i = j then u j else 0
  let f : ι → (AddMonoidAlgebra ℕ ℤ →ₗ[ℕ] ℕ) := fun i => integerCoordinate (g i)
  obtain ⟨hΔ, hf⟩ := diagonal_coordinates g hg
  let D := Submodule.span ℕ (Set.range (Function.uncurry a))
  refine ⟨D, ?_, Coalgebra.fg_span_coefficients a, ?_⟩
  · intro j
    exact Coalgebra.span_le_span_coefficients (u := u) (a := a) hΔ
      (Submodule.subset_span ⟨j, rfl⟩)
  · intro x hx
    exact Coalgebra.comul_mem_range_mapIncl_span_coefficients
      (u := u) (a := a) (f := f) hΔ hf hx

private theorem singleton_three_client :
    ∃ D : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      single (3 : ℤ) (1 : ℕ) ∈ D ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  obtain ⟨D, hmem, hfg, hclosed⟩ := coefficient_space_of_indices
    (fun _ : Unit => (3 : ℤ)) (fun _ _ _ => Subsingleton.elim _ _)
  exact ⟨D, hmem (), hfg, hclosed⟩

private theorem singleton_seven_client :
    ∃ D : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      single (7 : ℤ) (1 : ℕ) ∈ D ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  obtain ⟨D, hmem, hfg, hclosed⟩ := coefficient_space_of_indices
    (fun _ : Unit => (7 : ℤ)) (fun _ _ _ => Subsingleton.elim _ _)
  exact ⟨D, hmem (), hfg, hclosed⟩

-- Extraction and the right-counit consequence are used separately from
-- containment, which uses the left counit.
private theorem singleton_three_extraction :
    single (3 : ℤ) (1 : ℕ) =
      ((TensorProduct.lid ℕ (AddMonoidAlgebra ℕ ℤ)).toLinearMap ∘ₗ
        (integerCoordinate 3).rTensor (AddMonoidAlgebra ℕ ℤ))
      (Coalgebra.comul (R := ℕ) (single (3 : ℤ) (1 : ℕ))) := by
  obtain ⟨hΔ, hf⟩ := diagonal_coordinates
    (fun _ : Unit => (3 : ℤ)) (fun _ _ _ => Subsingleton.elim _ _)
  simpa using Coalgebra.coefficient_eq_contraction
    (f := fun _ : Unit => integerCoordinate 3) hΔ hf () ()

private theorem singleton_three_counit :
    Coalgebra.counit (R := ℕ) (single (3 : ℤ) (1 : ℕ)) = 1 := by
  obtain ⟨hΔ, hf⟩ := diagonal_coordinates
    (fun _ : Unit => (3 : ℤ)) (fun _ _ _ => Subsingleton.elim _ _)
  simpa using Coalgebra.counit_coefficient
    (f := fun _ : Unit => integerCoordinate 3) hΔ hf () ()

/-- Two distinct group-like basis elements lie in a finitely generated closed
coefficient span, with tensor-square closure also on a non-generator sum. -/
private theorem pair_three_seven_client :
    ∃ D : Submodule ℕ (AddMonoidAlgebra ℕ ℤ),
      single (3 : ℤ) (1 : ℕ) ∈ D ∧ single (7 : ℤ) (1 : ℕ) ∈ D ∧ D.FG ∧
      (∀ x ∈ D, Coalgebra.comul (R := ℕ) x ∈
        LinearMap.range (TensorProduct.mapIncl D D)) ∧
      Coalgebra.comul (R := ℕ)
        ((2 : ℕ) • single (3 : ℤ) (1 : ℕ) + (5 : ℕ) • single (7 : ℤ) (1 : ℕ)) ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  let g : Bool → ℤ := fun i => if i then 7 else 3
  have hg : Function.Injective g := by
    intro i j h
    cases i <;> cases j <;> simp_all [g]
  obtain ⟨D, hmem, hfg, hclosed⟩ := coefficient_space_of_indices g hg
  have h3 : single (3 : ℤ) (1 : ℕ) ∈ D := hmem false
  have h7 : single (7 : ℤ) (1 : ℕ) ∈ D := hmem true
  exact ⟨D, h3, h7, hfg, hclosed,
    hclosed _ (D.add_mem (D.smul_mem 2 h3) (D.smul_mem 5 h7))⟩

-- Repeated first factors need not admit biorthogonal coordinates. The span
-- containment still follows from the comultiplication expression alone.
private theorem dependent_coordinates_containment :
    let u : Bool → AddMonoidAlgebra ℕ ℤ := fun _ => single (3 : ℤ) 1
    let a : Bool → Bool → AddMonoidAlgebra ℕ ℤ :=
      fun i _ => if i then 0 else single (3 : ℤ) 1
    Submodule.span ℕ (Set.range u) ≤
      Submodule.span ℕ (Set.range (Function.uncurry a)) := by
  dsimp only
  apply Coalgebra.span_le_span_coefficients
  intro j
  simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]
  simp

private theorem empty_coefficients_client :
    (⊥ : Submodule ℕ (AddMonoidAlgebra ℕ ℤ)).FG ∧
      ∀ x ∈ (⊥ : Submodule ℕ (AddMonoidAlgebra ℕ ℤ)),
        Coalgebra.comul (R := ℕ) x ∈ LinearMap.range
          (TensorProduct.mapIncl (⊥ : Submodule ℕ (AddMonoidAlgebra ℕ ℤ)) ⊥) := by
  let u : Empty → AddMonoidAlgebra ℕ ℤ := Empty.elim
  let a : Empty → Empty → AddMonoidAlgebra ℕ ℤ := fun i => Empty.elim i
  let f : Empty → (AddMonoidAlgebra ℕ ℤ →ₗ[ℕ] ℕ) := Empty.elim
  have hΔ : ∀ j, Coalgebra.comul (R := ℕ) (u j) =
      ∑ i, u i ⊗ₜ[ℕ] a i j := fun j => Empty.elim j
  have hf : ∀ i j, f i (u j) = if i = j then 1 else 0 := fun i => Empty.elim i
  have hspan : Submodule.span ℕ (Set.range (Function.uncurry a)) = ⊥ := by
    rw [Set.range_eq_empty, Submodule.span_empty]
  constructor
  · simpa only [hspan] using Coalgebra.fg_span_coefficients (R := ℕ) a
  · intro x hx
    rw [← hspan] at hx ⊢
    exact Coalgebra.comul_mem_range_mapIncl_span_coefficients
      (u := u) (a := a) (f := f) hΔ hf hx

end CoalgebraCoefficientExamples
