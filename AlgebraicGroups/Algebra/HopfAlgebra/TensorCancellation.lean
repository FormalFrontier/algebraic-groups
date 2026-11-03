/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Ordered three-factor Hopf cancellation

For a Hopf algebra over a commutative semiring, this module proves the ordered tensor identity
`∑ S(h₃) ⊗ h₁ * S(h₂) = S(h) ⊗ 1`. The iterated comultiplication is expressed using the
canonical tensor associator; the multiplication order is unchanged throughout the proof.

The proof first tensors the usual right-antipode cancellation with the identity, applies the
left counit law, and then swaps the two output factors and applies the antipode to the first.
No inverse or involutivity of the antipode, commutativity of the Hopf algebra, or module
flatness is required. The tensor and Hopf algebra constructions and cancellation laws are
reused from Mathlib.

## References

* *Decomposition of a right Hopf module over a commutative semiring*, §3.1, equations (3.3)
  and (3.4).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace HopfAlgebra

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

local notation "Δ" => Coalgebra.comul (R := R) (A := H)
local notation "ε" => Coalgebra.counit (R := R) (A := H)
local notation "S" => antipode R (A := H)
local notation "μ" => LinearMap.mul' R H

/-- Right-antipode cancellation on the first two factors of the left-associated iterated
comultiplication, leaving the third factor unchanged. -/
private theorem mul_antipode_comul_rTensor_apply (h : H) :
    ((μ ∘ₗ (S).lTensor H).rTensor H) ((Δ).rTensor H (Δ h)) = (1 : H) ⊗ₜ[R] h := by
  have hc : (μ ∘ₗ (S).lTensor H) ∘ₗ Δ = Algebra.linearMap R H ∘ₗ ε := by
    simpa only [LinearMap.comp_assoc] using
      (mul_antipode_lTensor_comul (R := R) (A := H))
  rw [← LinearMap.rTensor_comp_apply, hc, LinearMap.rTensor_comp_apply,
    Coalgebra.rTensor_counit_comul]
  simp only [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]

/-- The ordered Hopf identity `∑ S(h₃) ⊗ h₁ * S(h₂) = S(h) ⊗ 1`, with the three input
factors supplied by the right-associated iterated comultiplication.

This is equation (3.4) of *Decomposition of a right Hopf module over a commutative semiring*,
§3.1. The swap exchanges tensor factors, not factors of a product in `H`. -/
theorem antipode_tensor_mul_antipode_comul_apply (h : H) :
    (S).rTensor H
      (TensorProduct.comm R H H
        (((μ ∘ₗ (S).lTensor H).rTensor H)
          ((TensorProduct.assoc R H H H).symm ((Δ).lTensor H (Δ h))))) =
      S h ⊗ₜ[R] (1 : H) := by
  rw [Coalgebra.coassoc_symm_apply, mul_antipode_comul_rTensor_apply]
  simp only [TensorProduct.comm_tmul, LinearMap.rTensor_tmul]

/-- Linear-map form of the ordered Hopf identity
`∑ S(h₃) ⊗ h₁ * S(h₂) = S(h) ⊗ 1`.

Starting with `H ⊗ (H ⊗ H)`, the associator inverse groups the first two factors, whose
image under `μ ∘ₗ S.lTensor H` is `a * S(b)`. The final symmetry and `S.rTensor H` send
`(a * S(b)) ⊗ c` to `S(c) ⊗ (a * S(b))`. -/
theorem antipode_tensor_mul_antipode_comul :
    (S).rTensor H ∘ₗ (TensorProduct.comm R H H).toLinearMap ∘ₗ
      (μ ∘ₗ (S).lTensor H).rTensor H ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap ∘ₗ (Δ).lTensor H ∘ₗ Δ =
      (TensorProduct.mk R H H).flip (1 : H) ∘ₗ S := by
  apply LinearMap.ext
  intro h
  exact antipode_tensor_mul_antipode_comul_apply h

end HopfAlgebra
