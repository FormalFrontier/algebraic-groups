/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Composition of scalar extensions

The map `TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton A _ F)`
extends an `R`-linear map `F : M →ₗ[R] N` to an `A`-linear map `A ⊗[R] M →ₗ[A] N`.
Here `A` can be a noncommutative algebra, and `N` is any compatible `R`- and `A`-module.

Postcomposition with an `A`-linear map commutes with this extension. This generalizes
`LinearMap.liftBaseChange_comp` from Mathlib to noncommutative scalar algebras. For
commutative scalar algebras, the extension agrees with `LinearMap.liftBaseChange`.
-/

@[expose] public section

namespace TensorProduct.AlgebraTensorModule

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section Semiring

variable [Semiring A] [Algebra R A] [Module A N] [IsScalarTower R A N]
variable [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- Postcomposing the scalar extension of an `R`-linear map with an `A`-linear map
extends the postcomposite. The scalar algebra `A` need not be commutative. -/
theorem comp_lift_toSpanSingleton (F : M →ₗ[R] N) (H : N →ₗ[A] P) :
    H.comp (lift (LinearMap.toSpanSingleton A _ F)) =
      lift (LinearMap.toSpanSingleton A _ ((H.restrictScalars R).comp F)) := by
  apply ext
  intro a m
  simp only [LinearMap.comp_apply, lift_tmul, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, LinearMap.coe_restrictScalars]
  exact H.map_smul a (F m)

end Semiring

section CommSemiring

variable [CommSemiring A] [Algebra R A] [Module A N] [IsScalarTower R A N]

/-- For a commutative scalar algebra, extension by `lift` and `toSpanSingleton`
agrees with `LinearMap.liftBaseChange`. -/
theorem lift_toSpanSingleton_eq_liftBaseChange (F : M →ₗ[R] N) :
    lift (LinearMap.toSpanSingleton A _ F) = F.liftBaseChange A := by
  apply ext
  intro a m
  simp only [lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    LinearMap.liftBaseChange_tmul]

end CommSemiring

end TensorProduct.AlgebraTensorModule
