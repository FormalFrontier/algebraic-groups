/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Frobenius
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Purity of injective algebra maps from finite-dimensional Hopf algebras

An injective algebra map from a finite-dimensional commutative Hopf algebra has
injective tensor units. The target is any algebra over the Hopf algebra; no commutativity,
Hopf structure or specified base-field algebra structure on the target is assumed.
For example, the target can be a matrix algebra when the source is the base field.

Self-injectivity of the Hopf algebra extends its identity along the given linear
inclusion. Tensoring this retraction and composing with the left unitor splits each
tensor unit. The proof uses `HopfAlgebra.injective_self` and Mathlib's
`Module.Injective.extension_property`, `TensorProduct.map` and `TensorProduct.lid`.

## References

* J. S. Milne, *Algebraic Groups*, Theorem 3.31, for the nil-augmentation setting
  in which this purity result can be applied. The proof here is different: it uses
  self-injectivity of finite-dimensional Hopf algebras and module splitting.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace HopfAlgebra

/-- An injective algebra map from a finite-dimensional commutative Hopf algebra is
pure: its tensor units are injective for every module. The target algebra is arbitrary.
Self-injectivity of the Hopf source splits the original algebra map as a linear map. -/
theorem tensorProduct_mk_one_injective (K : Type u) (D : Type v) (E : Type w)
    [Field K] [CommRing D] [HopfAlgebra K D] [Module.Finite K D]
    [Ring E] [Algebra D E] (hinj : Function.Injective (algebraMap D E))
    (N : Type z) [AddCommMonoid N] [Module D N] :
    Function.Injective (TensorProduct.mk D E N 1) := by
  have : Module.Injective D D := HopfAlgebra.injective_self K D
  obtain ⟨r, hr⟩ := Module.Injective.extension_property D D D E
    (Algebra.linearMap D E) hinj (LinearMap.id : D →ₗ[D] D)
  have hr_one : r (1 : E) = 1 := by
    simpa using LinearMap.congr_fun hr (1 : D)
  have hsplit : Function.LeftInverse
      ((TensorProduct.lid D N).toLinearMap ∘ₗ
        TensorProduct.map r (LinearMap.id : N →ₗ[D] N))
      (TensorProduct.mk D E N 1) := by
    intro n
    simp [hr_one]
  exact hsplit.injective

end HopfAlgebra
