/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Balanced right module actions

The given action of an opposite algebra on a module induces an action map from
its tensor product with the algebra. The scalar tower uses the original scalar
module; no new scalar action or balancing datum is chosen.

The construction is the tensor lift of `Algebra.lsmul`, composed with the
opposite linear equivalence and flipped. Its pure-tensor formula and uniqueness
characterize it, and the regular specialization is multiplication.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace TensorProduct

variable (R : Type u) (A : Type v) (M : Type w)
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M]
variable [IsScalarTower R Aᵐᵒᵖ M]

/-- The balanced map of a given right algebra action on the original scalar module. -/
def rightAction : M ⊗[R] A →ₗ[R] M :=
  TensorProduct.lift
    (((Algebra.lsmul R R M : Aᵐᵒᵖ →ₐ[R] Module.End R M).toLinearMap ∘ₗ
      (MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).toLinearMap).flip)

/-- On pure tensors, the balanced action is the given opposite-algebra action. -/
@[simp] theorem rightAction_tmul (m : M) (a : A) :
    rightAction R A M (m ⊗ₜ[R] a) = MulOpposite.op a • m := by
  simp [rightAction, Algebra.lsmul_apply]

/-- A linear map is the balanced action exactly when it has the given pure-tensor values. -/
theorem eq_rightAction_iff (f : M ⊗[R] A →ₗ[R] M) :
    f = rightAction R A M ↔ ∀ m a, f (m ⊗ₜ[R] a) = MulOpposite.op a • m := by
  constructor
  · rintro rfl
    exact rightAction_tmul R A M
  · intro h
    apply TensorProduct.ext'
    intro m a
    simpa only [rightAction_tmul] using h m a

/-- Successive right actions multiply their algebra arguments in the original order. -/
theorem rightAction_rightAction_tmul (m : M) (a b : A) :
    rightAction R A M (rightAction R A M (m ⊗ₜ[R] a) ⊗ₜ[R] b) =
      rightAction R A M (m ⊗ₜ[R] (a * b)) := by
  simpa only [rightAction_tmul] using op_smul_op_smul m a b

/-- On the right regular module, the balanced action is ordinary multiplication. -/
@[simp] theorem rightAction_eq_mul' : rightAction R A A = LinearMap.mul' R A := by
  apply TensorProduct.ext'
  intro a b
  simp only [rightAction_tmul, op_smul_eq_mul, LinearMap.mul'_apply]

end TensorProduct
