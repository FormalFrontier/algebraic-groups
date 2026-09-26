/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Points of a symmetric Hopf algebra

Algebra maps out of a symmetric algebra, with convolution, form the additive
group of linear maps into the target algebra. No finiteness assumption is needed.
-/

public section

noncomputable section

namespace SymmetricAlgebra

universe u v w

variable (K : Type u) [CommRing K] (M : Type v) [AddCommMonoid M] [Module K M]
  (R : Type w) [CommRing R] [Algebra K R]

/-- Convolution of algebra maps out of the symmetric algebra is addition of
linear maps on its primitive generators. -/
@[expose] def linearMapMulEquivAlgHom :
    Multiplicative (M →ₗ[K] R) ≃* WithConv (SymmetricAlgebra K M →ₐ[K] R) where
  toEquiv := (Multiplicative.toAdd : Multiplicative (M →ₗ[K] R) ≃ (M →ₗ[K] R)).trans
    (lift.trans (WithConv.equiv _).symm)
  map_mul' f g := by
    apply WithConv.ofConv_injective
    apply algHom_ext
    ext m
    change lift (f.toAdd + g.toAdd) (ι K M m) =
      ((WithConv.toConv (lift f.toAdd)) *
        (WithConv.toConv (lift g.toAdd))).ofConv (ι K M m)
    rw [AlgHom.convMul_apply, comul_ι]
    simp

@[simp]
theorem linearMapMulEquivAlgHom_ι (f : M →ₗ[K] R) (m : M) :
    (linearMapMulEquivAlgHom K M R (.ofAdd f)).ofConv (ι K M m) = f m := by
  simp [linearMapMulEquivAlgHom]

theorem linearMapMulEquivAlgHom_zero :
    linearMapMulEquivAlgHom K M R (.ofAdd (0 : M →ₗ[K] R)) = 1 :=
  (linearMapMulEquivAlgHom K M R).map_one

/-- Negating the linear map produces a two-sided convolution inverse. -/
theorem linearMapMulEquivAlgHom_neg_mul (f : M →ₗ[K] R) :
    linearMapMulEquivAlgHom K M R (.ofAdd (-f)) *
      linearMapMulEquivAlgHom K M R (.ofAdd f) = 1 := by
  rw [← (linearMapMulEquivAlgHom K M R).map_mul]
  simp

theorem linearMapMulEquivAlgHom_mul_neg (f : M →ₗ[K] R) :
    linearMapMulEquivAlgHom K M R (.ofAdd f) *
      linearMapMulEquivAlgHom K M R (.ofAdd (-f)) = 1 := by
  rw [← (linearMapMulEquivAlgHom K M R).map_mul]
  simp

/-- The equivalence commutes with every algebra map on the test algebra. -/
theorem linearMapMulEquivAlgHom_naturality
    {S : Type*} [CommRing S] [Algebra K S]
    (h : R →ₐ[K] S) (f : M →ₗ[K] R) :
    (linearMapMulEquivAlgHom K M S (.ofAdd (h.toLinearMap.comp f))).ofConv =
      h.comp (linearMapMulEquivAlgHom K M R (.ofAdd f)).ofConv := by
  apply algHom_ext
  ext m
  simp

end SymmetricAlgebra
