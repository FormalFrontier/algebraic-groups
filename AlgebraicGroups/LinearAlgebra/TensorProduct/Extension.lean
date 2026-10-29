/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extensions of linear maps

The map `TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton A _ F)`
extends an `R`-linear map `F : M →ₗ[R] N` to an `A`-linear map `A ⊗[R] M →ₗ[A] N`.
Here `A` can be a noncommutative algebra, and `N` is any compatible `R`- and `A`-module.

When `A = R`, conjugating the extension of a map `M →ₗ[R] R ⊗[R] N`
by the left unitors gives its left-unitor contraction.

Postcomposition with an `A`-linear map commutes with this extension. This generalizes
`LinearMap.liftBaseChange_comp` from Mathlib to noncommutative scalar algebras. For
commutative scalar algebras, the extension agrees with `LinearMap.liftBaseChange`.
The extension to `A ⊗[R] M` is the identity precisely for the map `m ↦ 1 ⊗ₜ[R] m`.

For an arbitrary algebra map `φ : A →ₐ[R] B`, changing coefficients by
`TensorProduct.map φ.toLinearMap LinearMap.id` commutes with the extension of
`F : M →ₗ[R] A ⊗[R] N`. The coefficient algebras need not be commutative, and neither
needs to act on `M` or `N`. Algebra-equivalence transport is a specialization using
`TensorProduct.congr`; for commutative coefficients, the agreement with
`LinearMap.liftBaseChange` gives the same naturality square for that extension.

## References

These calculations use Mathlib's tensor-product universal property and its algebra,
scalar-extension and linear-map APIs.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Conjugating the scalar extension of an arbitrary map `M →ₗ[R] R ⊗[R] N`
by the left unitors gives its left-unitor contraction. No algebra or coalgebra
structure on either module is needed. -/
theorem lid_comp_lift_toSpanSingleton (F : M →ₗ[R] R ⊗[R] N) :
    (TensorProduct.lid R N).toLinearMap.comp
      ((lift (LinearMap.toSpanSingleton R (M →ₗ[R] R ⊗[R] N) F)).comp
        (TensorProduct.lid R M).symm.toLinearMap) =
      (TensorProduct.lid R N).toLinearMap.comp F := by
  ext m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
  rw [lift_tmul, LinearMap.toSpanSingleton_apply, one_smul]

section Semiring

variable [Semiring A] [Algebra R A] [Module A N] [IsScalarTower R A N]
variable [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- The scalar extension of `F` is the identity exactly when `F` sends `m` to `1 ⊗ₜ[R] m`. -/
theorem lift_toSpanSingleton_eq_id_iff (F : M →ₗ[R] A ⊗[R] M) :
    lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M) F) =
      (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M) ↔
    F = TensorProduct.mk R A M (1 : A) := by
  constructor
  · intro h
    apply LinearMap.ext
    intro m
    simpa only [lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
      one_smul, LinearMap.id_apply, TensorProduct.mk_apply] using
      LinearMap.congr_fun h ((1 : A) ⊗ₜ[R] m)
  · rintro rfl
    apply ext
    intro a m
    simpa only [lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
      TensorProduct.mk_apply, LinearMap.id_apply] using
      (TensorProduct.tmul_eq_smul_one_tmul (R := R) a m).symm

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

section ScalarTransport

variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Changing coefficients along an algebra homomorphism commutes with tensor scalar
extension. Both sides are `R`-linear maps; no action of either coefficient algebra
on `M` or `N` is required. The coefficient algebras need not be commutative. -/
theorem map_comp_lift_toSpanSingleton
    (φ : A →ₐ[R] B) (F : M →ₗ[R] A ⊗[R] N) :
    (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[R] N)).comp
      ((lift (LinearMap.toSpanSingleton A
        (M →ₗ[R] A ⊗[R] N) F)).restrictScalars R) =
      ((lift (LinearMap.toSpanSingleton B
        (M →ₗ[R] B ⊗[R] N)
        ((TensorProduct.map φ.toLinearMap
          (LinearMap.id : N →ₗ[R] N)).comp F))).restrictScalars R).comp
        (TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[R] M)) := by
  have hφ (a : A) (y : A ⊗[R] N) :
      TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[R] N) (a • y) =
        φ a • TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[R] N) y := by
    induction y using TensorProduct.inductionOn with
    | tmul b n =>
        simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul,
          AlgHom.toLinearMap_apply, LinearMap.id_apply, smul_eq_mul, map_mul]
    | add y y' hy hy' =>
        simp only [smul_add, map_add, hy, hy']
  apply TensorProduct.ext'
  intro a m
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
    lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply] using hφ a (F m)

/-- Elementwise coefficient naturality of tensor scalar extension along an arbitrary
algebra homomorphism. This is the application form of `map_comp_lift_toSpanSingleton`. -/
theorem map_lift_toSpanSingleton_apply
    (φ : A →ₐ[R] B) (F : M →ₗ[R] A ⊗[R] N)
    (z : A ⊗[R] M) :
    TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[R] N)
      (lift (LinearMap.toSpanSingleton A
        (M →ₗ[R] A ⊗[R] N) F) z) =
      lift (LinearMap.toSpanSingleton B
        (M →ₗ[R] B ⊗[R] N)
        ((TensorProduct.map φ.toLinearMap
          (LinearMap.id : N →ₗ[R] N)).comp F))
        (TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[R] M) z) := by
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] using
    LinearMap.congr_fun (map_comp_lift_toSpanSingleton φ F) z

/-- Transport by an algebra equivalence is the specialization of coefficient
naturality in which the coefficient maps are tensor linear equivalences. -/
theorem congr_comp_lift_toSpanSingleton
    (e : A ≃ₐ[R] B) (F : M →ₗ[R] A ⊗[R] N) :
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R N)).toLinearMap.comp
      ((lift (LinearMap.toSpanSingleton A
        (M →ₗ[R] A ⊗[R] N) F)).restrictScalars R) =
      ((lift (LinearMap.toSpanSingleton B
        (M →ₗ[R] B ⊗[R] N)
        ((TensorProduct.congr e.toLinearEquiv
          (LinearEquiv.refl R N)).toLinearMap.comp F))).restrictScalars R).comp
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)).toLinearMap := by
  simpa only [TensorProduct.toLinearMap_congr, LinearEquiv.refl_toLinearMap,
    AlgEquiv.toAlgHom_toLinearMap] using
    map_comp_lift_toSpanSingleton e.toAlgHom F

end ScalarTransport

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
