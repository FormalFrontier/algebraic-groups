/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplicativity of additive maps out of tensor products

The pure-tensor criterion `LinearMap.map_mul_of_map_mul_tmul` needs only
additivity of the map, not linearity over a common scalar semiring. We give that
generalization for additive homomorphisms, so it applies to semilinear maps
without choosing an additional scalar action on their target.

The ordinary ring-homomorphism constructor using this criterion agrees with the
ring-homomorphism parent of Mathlib's
`Algebra.TensorProduct.algHomOfLinearMapTensorProduct`.
-/

@[expose] public section

universe uR uS uA uB uC

open scoped TensorProduct

namespace AddMonoidHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An additive map out of a tensor product preserves multiplication if it does so
on pairs of pure tensors. This generalizes `LinearMap.map_mul_of_map_mul_tmul`. -/
theorem map_mul_of_map_mul_tmul [NonUnitalNonAssocSemiring C]
    (f : A ⊗[R] B →+ C)
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
      f ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) = f (a₁ ⊗ₜ[R] b₁) * f (a₂ ⊗ₜ[R] b₂))
    (x y : A ⊗[R] B) : f (x * y) = f x * f y := by
  induction x with
  | tmul a b =>
    induction y with
    | tmul c d => simpa only [Algebra.TensorProduct.tmul_mul_tmul] using hf a c b d
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]

end AddMonoidHom

namespace Algebra.TensorProduct

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} {C : Type uC}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B] [Semiring C] [Algebra S C]

/-- The ordinary ring-homomorphism constructor using the additive criterion agrees
with the ring-homomorphism parent of Mathlib's linear pure-tensor construction. -/
theorem algHomOfLinearMapTensorProduct_toRingHom (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
      f ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) = f (a₁ ⊗ₜ[R] b₁) * f (a₂ ⊗ₜ[R] b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) :
    (algHomOfLinearMapTensorProduct f h_mul h_one).toRingHom =
      { f.toAddMonoidHom with
        map_one' := h_one
        map_mul' := f.toAddMonoidHom.map_mul_of_map_mul_tmul h_mul } := rfl

end Algebra.TensorProduct
