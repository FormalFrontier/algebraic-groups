/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor coordinates along a split free presentation

A section `σ : C →ₗ[R] (ι →₀ R)` of `π : (ι →₀ R) →ₗ[R] C` gives finitely
supported coordinates for tensors in `M ⊗[R] C`. The construction is the existing
`TensorProduct.equivFinsuppOfBasisRight Finsupp.basisSingleOne` applied after
`σ.lTensor M`. Its values are right-factor contractions by the coordinate
functionals of `σ`, and descending through `π` reconstructs the tensor.

The basis is on the free presentation, not on `C`; no freeness or finite-generation
assumption on `C` is needed. The index type and both modules may have independent
universes. For a projective module, `Module.Projective.out` supplies a section of
`Finsupp.linearCombination R id`, with index type `C`.

## References

* Mathlib's tensor-product basis and Finsupp formalizations, especially
  `TensorProduct.equivFinsuppOfBasisRight` and its evaluation and inverse formulas.
* Mathlib's projective-module formalization, for sections of free presentations.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the
  coefficient-coalgebra method motivating tensor coordinates.
-/

@[expose] public section

universe u v w z

namespace TensorProduct

open scoped TensorProduct

variable {R : Type u} {C : Type v} {M : Type w} {ι : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid M] [Module R M]

open Classical in
/-- Every coordinate of the tensor lifted through `σ` is the contraction by
`c ↦ σ c i`. This holds at all indices, including those outside its finite support,
and does not require a retraction of `σ`. -/
theorem equivFinsuppOfBasisRight_lTensor_apply
    (σ : C →ₗ[R] (ι →₀ R)) (t : M ⊗[R] C) (i : ι) :
    equivFinsuppOfBasisRight (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R))
        (σ.lTensor M t) i =
      TensorProduct.rid R M (((Finsupp.lapply i).comp σ).lTensor M t) := by
  rw [equivFinsuppOfBasisRight_apply]
  change TensorProduct.rid R M ((Finsupp.lapply i).lTensor M (σ.lTensor M t)) = _
  rw [LinearMap.lTensor_comp_apply]

open Classical in
/-- Descending the canonical finite coordinates of a lifted tensor through a
split free presentation reconstructs the tensor. The coordinate construction is
Mathlib's public `equivFinsuppOfBasisRight`, on the basis of `ι →₀ R`. -/
theorem sum_tmul_eq_of_split
    (π : (ι →₀ R) →ₗ[R] C) (σ : C →ₗ[R] (ι →₀ R))
    (hσ : π.comp σ = LinearMap.id) (t : M ⊗[R] C) :
    let a := equivFinsuppOfBasisRight
      (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)) (σ.lTensor M t)
    (∑ i ∈ a.support, a i ⊗ₜ[R] π (Finsupp.single i 1)) = t := by
  let bF : Module.Basis ι R (ι →₀ R) := Finsupp.basisSingleOne
  let a : ι →₀ M := equivFinsuppOfBasisRight bF (σ.lTensor M t)
  have hsplit : π.lTensor M (σ.lTensor M t) = t := by
    rw [← LinearMap.lTensor_comp_apply, hσ]
    simp only [LinearMap.lTensor_id, LinearMap.id_apply]
  have hπb (i : ι) : π (bF i) = π (Finsupp.single i 1) := by
    simp [bF]
  have hrepr : (∑ i ∈ a.support, a i ⊗ₜ[R] bF i) = σ.lTensor M t := by
    simpa only [equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
      using (equivFinsuppOfBasisRight bF).symm_apply_apply (σ.lTensor M t)
  calc
    (∑ i ∈ a.support, a i ⊗ₜ[R] π (Finsupp.single i 1)) =
        π.lTensor M (∑ i ∈ a.support, a i ⊗ₜ[R] bF i) := by
      simp only [map_sum, LinearMap.lTensor_tmul, hπb]
    _ = π.lTensor M (σ.lTensor M t) := congrArg (π.lTensor M) hrepr
    _ = t := hsplit

open Classical in
/-- A split free presentation gives a finite tensor expansion whose coefficients
are contractions by its section's coordinate functionals. Neither a basis of `C`
nor a finite index type is required. The witness is the canonical construction
used in `sum_tmul_eq_of_split`. -/
theorem exists_tensor_coefficients_of_split
    (π : (ι →₀ R) →ₗ[R] C) (σ : C →ₗ[R] (ι →₀ R))
    (hσ : π.comp σ = LinearMap.id) (t : M ⊗[R] C) :
    ∃ a : ι →₀ M,
      (∑ i ∈ a.support, a i ⊗ₜ[R] π (Finsupp.single i 1)) = t ∧
      ∀ i, a i = TensorProduct.rid R M (((Finsupp.lapply i).comp σ).lTensor M t) := by
  refine ⟨equivFinsuppOfBasisRight Finsupp.basisSingleOne (σ.lTensor M t),
    sum_tmul_eq_of_split π σ hσ t, ?_⟩
  exact fun i ↦ equivFinsuppOfBasisRight_lTensor_apply σ t i

end TensorProduct
