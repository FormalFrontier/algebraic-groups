/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Regular-comodule coefficients on the natural-number monoid algebra

The canonical coalgebra on `MonoidAlgebra ℕ ℕ` has group-like standard basis
vectors. Its existing regular comodule has a nonconstant full coaction on the
sum of the basis vectors indexed by zero and one. The coefficient morphism for
the zeroth coordinate is a nonzero, nonidentity projection. The regular-target
correspondence reads this same projection as the coordinate functional and
recovers the identity from the counit.

All coaction data and basis data here are the stock regular comodule,
`MonoidAlgebra.instCoalgebra`, and `MonoidAlgebra.basis`. The basis index is `ℕ`;
the coordinate column is formed by the stock tensor/Finsupp equivalence on
the original coaction, with no finite-index hypothesis or model constructor.
-/

@[expose] public section

open scoped TensorProduct

namespace RegularComoduleCoefficients

local notation "C" => MonoidAlgebra ℕ ℕ
local notation "X" => Coalgebra.RightComodule.regular ℕ C
local notation "b" => (MonoidAlgebra.basis ℕ ℕ : Module.Basis ℕ ℕ C)
local notation "e₀" => (MonoidAlgebra.single 0 1 : C)
local notation "e₁" => (MonoidAlgebra.single 1 1 : C)
local notation "π₀" => Coalgebra.RightComodule.coefficientHom X (Module.Basis.coord b 0)

private theorem column_tmul_single (n : ℕ) (c : C) :
    TensorProduct.equivFinsuppOfBasisLeft b ((MonoidAlgebra.single n 1 : C) ⊗ₜ[ℕ] c) =
      Finsupp.single n c := by
  have hb : (b) n = (MonoidAlgebra.single n 1 : C) :=
    MonoidAlgebra.basis_apply ℕ n
  rw [← hb, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul,
    Module.Basis.repr_self, Finsupp.mapRange_single, one_smul]

/-- Each standard basis vector is group-like for the existing full coaction. -/
theorem coaction_single (n : ℕ) :
    (X).coaction (MonoidAlgebra.single n 1 : C) =
      (MonoidAlgebra.single n 1 : C) ⊗ₜ[ℕ] (MonoidAlgebra.single n 1 : C) := by
  simp only [Coalgebra.RightComodule.regular_coaction, MonoidAlgebra.comul_single,
    CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

/-- The coaction of the sum has two distinct diagonal terms. -/
theorem coaction_pair :
    (X).coaction (e₀ + e₁) = e₀ ⊗ₜ[ℕ] e₀ + e₁ ⊗ₜ[ℕ] e₁ := by
  rw [map_add, coaction_single, coaction_single]

/-- The full coaction on this element is not tensoring by the zeroth basis vector. -/
theorem coaction_pair_ne_constant :
    (X).coaction (e₀ + e₁) ≠ (e₀ + e₁) ⊗ₜ[ℕ] e₀ := by
  intro h
  rw [coaction_pair] at h
  -- The coefficient at (1, 1) is one for the diagonal coaction and zero for
  -- tensoring by the zeroth basis vector.
  have h₁₁ := congrArg
    (fun t ↦ ((TensorProduct.equivFinsuppOfBasisLeft b t) 1).coeff 1) h
  simp only [TensorProduct.add_tmul, map_add, column_tmul_single] at h₁₁
  simp at h₁₁

/-- The original coaction's column uses the two corresponding basis coefficients. -/
theorem coordinate_column_pair :
    TensorProduct.equivFinsuppOfBasisLeft b ((X).coaction (e₀ + e₁)) =
      Finsupp.single 0 e₀ + Finsupp.single 1 e₁ := by
  rw [coaction_pair, map_add, column_tmul_single, column_tmul_single]

/-- This column has finite support although its basis index type is infinite. -/
theorem coordinate_column_pair_support :
    (TensorProduct.equivFinsuppOfBasisLeft b ((X).coaction (e₀ + e₁))).support =
      {0, 1} := by
  rw [coordinate_column_pair]
  ext n
  by_cases h₀ : n = 0
  · subst n
    simp
  by_cases h₁ : n = 1
  · subst n
    simp
  · simp [Finsupp.mem_support_iff, h₀, h₁]

/-- The zeroth-coordinate coefficient morphism fixes the zeroth basis vector. -/
theorem projection_zero : π₀ e₀ = e₀ := by
  rw [Coalgebra.RightComodule.coefficientHom_apply,
    ← (X).equivFinsuppOfBasisLeft_coaction_apply b e₀ 0,
    coaction_single, column_tmul_single]
  simp

/-- The same coefficient morphism kills the first basis vector. -/
theorem projection_one : π₀ e₁ = 0 := by
  rw [Coalgebra.RightComodule.coefficientHom_apply,
    ← (X).equivFinsuppOfBasisLeft_coaction_apply b e₁ 0,
    coaction_single, column_tmul_single]
  simp

/-- The projection's underlying linear map is nonzero. -/
theorem projection_toLinearMap_ne_zero : (π₀).toLinearMap ≠ 0 := by
  intro h
  have hz : e₀ = (0 : C) :=
    projection_zero.symm.trans (LinearMap.congr_fun h e₀)
  have h₀ := congrArg (fun f : C ↦ f.coeff 0) hz
  simp at h₀

/-- The projection is not the identity comodule morphism. -/
theorem projection_ne_id : π₀ ≠ Coalgebra.RightComoduleHom.id X := by
  intro h
  have hz : (0 : C) = e₁ :=
    projection_one.symm.trans (congrArg (fun f : Coalgebra.RightComoduleHom X X ↦ f e₁) h)
  have h₁ := congrArg (fun f : C ↦ f.coeff 1) hz
  simp at h₁

/-- The counit composite of this same projection is the zeroth coordinate. -/
theorem projection_counit :
    Coalgebra.counit (R := ℕ) ∘ₗ (π₀).toLinearMap = (b).coord 0 := by
  exact (X).counit_comp_coefficientHom ((b).coord 0)

/-- The regular-target correspondence reads the projection as its coordinate. -/
theorem homRegularEquiv_projection :
    (X).homRegularEquiv π₀ = (b).coord 0 := by
  exact (X).homRegularEquiv_coefficientHom ((b).coord 0)

/-- The inverse correspondence recovers this same bundled projection. -/
theorem homRegularEquiv_symm_coord :
    (X).homRegularEquiv.symm ((b).coord 0) = π₀ := by
  exact (X).homRegularEquiv_symm_apply ((b).coord 0)

/-- The counit functional gives the identity, rather than the coordinate projection. -/
theorem coefficientHom_counit :
    (X).coefficientHom (Coalgebra.counit (R := ℕ)) =
      Coalgebra.RightComoduleHom.id X := by
  exact Coalgebra.RightComodule.coefficientHom_regular_counit

/-- The identity morphism is read back as the counit. -/
theorem homRegularEquiv_id :
    (X).homRegularEquiv (Coalgebra.RightComoduleHom.id X) =
      Coalgebra.counit (R := ℕ) := by
  exact Coalgebra.RightComodule.homRegularEquiv_regular_id

/-- The inverse correspondence sends the counit to the identity. -/
theorem homRegularEquiv_symm_counit :
    (X).homRegularEquiv.symm (Coalgebra.counit (R := ℕ)) =
      Coalgebra.RightComoduleHom.id X := by
  rw [Coalgebra.RightComodule.homRegularEquiv_symm_apply, coefficientHom_counit]

end RegularComoduleCoefficients

-- The supplied infinite basis spans the all-dual coefficient span of the regular coaction.
example :
    let X := Coalgebra.RightComodule.regular ℕ (MonoidAlgebra ℕ ℕ)
    let b := (MonoidAlgebra.basis ℕ ℕ : Module.Basis ℕ ℕ (MonoidAlgebra ℕ ℕ))
    X.coefficientSpan = Submodule.span ℕ
      (Set.range (Function.uncurry (fun i j : ℕ ↦ X.coefficient (b.coord i) (b j)))) :=
  Coalgebra.RightComodule.coefficientSpan_eq_span_basis _ (MonoidAlgebra.basis ℕ ℕ)
