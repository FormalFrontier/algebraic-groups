/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar-extension images of submodules

Commuting tensor factors identifies the right-order tensor-inclusion image with
`Submodule.baseChange`. An arbitrary linear map on the coefficient factor carries
one scalar-extension image into another. Neither assertion requires injectivity
of the tensor inclusion or flatness, and the coefficient algebras may be
noncommutative semirings.

## References

* Mathlib's tensor-map, commutativity and scalar-extension formalizations.
* C. Kassel, *Quantum Groups*, §II.4, for tensor-product conventions.
-/

@[expose] public section

universe uR uA uB uM

open scoped TensorProduct

namespace TensorProduct

variable {R : Type uR} {A : Type uA} {M : Type uM}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]

/-- Commutation identifies the right-order tensor-inclusion image with the
scalar-extension image of a submodule. -/
theorem comm_mem_baseChange_iff (U : Submodule R M) (y : M ⊗[R] A) :
    TensorProduct.comm R M A y ∈ U.baseChange A ↔
      y ∈ LinearMap.range (U.subtype.rTensor A) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨TensorProduct.comm R A U t, ?_⟩
    apply (TensorProduct.comm R M A).injective
    exact (LinearMap.congr_fun
      (LinearMap.comm_comp_rTensor_comp_comm_eq (Q := A) U.subtype) t).trans ht
  · rintro ⟨t, ht⟩
    refine ⟨TensorProduct.comm R U A t, ?_⟩
    calc
      U.subtype.baseChange A (TensorProduct.comm R U A t) =
          TensorProduct.comm R M A (U.subtype.rTensor A t) :=
        TensorProduct.map_comm (LinearMap.id : A →ₗ[R] A) U.subtype t
      _ = TensorProduct.comm R M A y :=
        congrArg (TensorProduct.comm R M A) ht

end TensorProduct

namespace Submodule

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]

/-- A linear map on the coefficient factor transports scalar-extension images.
The tensor transport is `R`-linear; it need not be linear over either coefficient
algebra. -/
theorem map_mem_baseChange (U : Submodule R M) (f : A →ₗ[R] B)
    {z : A ⊗[R] M} (hz : z ∈ U.baseChange A) :
    TensorProduct.map f (LinearMap.id : M →ₗ[R] M) z ∈ U.baseChange B := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨TensorProduct.map f (LinearMap.id : U →ₗ[R] U) w, ?_⟩
  change TensorProduct.map (LinearMap.id : B →ₗ[R] B) U.subtype
      (TensorProduct.map f (LinearMap.id : U →ₗ[R] U) w) =
    TensorProduct.map f (LinearMap.id : M →ₗ[R] M)
      (TensorProduct.map (LinearMap.id : A →ₗ[R] A) U.subtype w)
  simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

end Submodule
