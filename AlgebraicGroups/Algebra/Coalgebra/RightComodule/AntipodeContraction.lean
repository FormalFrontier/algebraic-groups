/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Module.TensorProductAction
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Antipode contraction on a right comodule

The antipode contraction applies the antipode to the coalgebra factor of a right
coaction and then applies the given right action. Its characteristic finite-sum
formula uses any specified tensor presentation of the coaction.

## Main declarations

* `Coalgebra.RightComodule.antipodeContraction` is the resulting linear endomorphism.
* `Coalgebra.RightComodule.antipodeContraction_eq_sum` evaluates it from a finite
  tensor presentation of the coaction.
* `Coalgebra.RightComodule.regular_antipodeContraction` computes it on the regular
  comodule as the counit times the unit.

## Implementation notes

The construction needs only `HopfAlgebraStruct`, with no compatibility condition
between the given action and coaction. The regular-comodule calculation uses the
full Hopf algebra axioms and the canonical opposite-module action on the algebra.

## References

The construction uses `TensorProduct.rightAction`; the regular-comodule formula
uses the antipode identity in Mathlib's `HopfAlgebra.Basic`.
-/

@[expose] public section

universe u v w z

open scoped BigOperators TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type u} {H : Type v} {M : Type w}

section Data

variable [CommSemiring R] [Semiring H] [HopfAlgebraStruct R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M]
variable [IsScalarTower R Hᵐᵒᵖ M]

/-- Contract the right coaction using the antipode and the given right action. -/
def antipodeContraction (X : RightComodule R H M) : M →ₗ[R] M :=
  _root_.TensorProduct.rightAction R H M ∘ₗ
    (HopfAlgebra.antipode R).lTensor M ∘ₗ X.coaction

/-- The antipode contraction applies the antipode to the right tensor factor
before applying the given action. -/
@[simp] theorem antipodeContraction_apply (X : RightComodule R H M) (m : M) :
    X.antipodeContraction m =
      _root_.TensorProduct.rightAction R H M
        ((HopfAlgebra.antipode R).lTensor M (X.coaction m)) := rfl

/-- Evaluate the antipode contraction from a finite tensor presentation of the
specified coaction. -/
theorem antipodeContraction_eq_sum {ι : Type z} (X : RightComodule R H M) (m : M)
    (s : Finset ι) (a : ι → M) (h : ι → H)
    (hρ : X.coaction m = ∑ i ∈ s, a i ⊗ₜ[R] h i) :
    X.antipodeContraction m =
      ∑ i ∈ s, MulOpposite.op (HopfAlgebra.antipode R (h i)) • a i := by
  rw [antipodeContraction_apply, hρ]
  simp only [map_sum, LinearMap.lTensor_tmul, _root_.TensorProduct.rightAction_tmul]

end Data

section Regular

variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- On the regular comodule, antipode contraction is the counit times the unit. -/
theorem regular_antipodeContraction (h : H) :
    (regular R H).antipodeContraction h =
      Coalgebra.counit (R := R) h • (1 : H) := by
  simpa only [antipodeContraction_apply, regular_coaction,
    _root_.TensorProduct.rightAction_eq_mul', Algebra.algebraMap_eq_smul_one] using
    (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) h)

end Regular

end Coalgebra.RightComodule
