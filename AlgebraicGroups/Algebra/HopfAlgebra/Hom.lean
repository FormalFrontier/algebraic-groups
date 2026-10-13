/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Bialgebra homomorphisms between Hopf algebras

A bialgebra homomorphism between Hopf algebras commutes with their antipodes.
The base is a commutative semiring; the two Hopf algebras need not be commutative
or have additive inverses. The proof compares a left and a right inverse in
Mathlib's convolution monoid of linear maps, using its compatibility lemmas for
composition with the convolution product and unit. The quotient construction
`HopfAlgebra.ofSurjective` assumes antipode compatibility rather than proving it.

## References

* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `Mathlib.RingTheory.Coalgebra.Convolution` and
  `Mathlib.RingTheory.HopfAlgebra.Convolution`: convolution of linear maps,
  compatibility with algebra and coalgebra maps, and the antipode identities.
* Robert Hawkins, Mathlib, `Mathlib.RingTheory.HopfAlgebra.Quotient`:
  `LinearMap.convOne_comp_coalgHom` and `LinearMap.algHom_comp_convOne`,
  compatibility of the convolution unit with coalgebra and algebra maps.
-/

@[expose] public section

universe u v w

open WithConv

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- A bialgebra homomorphism between Hopf algebras commutes with the antipodes.
This follows from uniqueness of convolution inverses, using Mathlib's linear-map
convolution identities. -/
@[simp]
theorem map_antipode (f : A →ₐc[R] B) (x : A) :
    f (HopfAlgebra.antipode R x) = HopfAlgebra.antipode R (f x) := by
  have hleft : toConv ((HopfAlgebra.antipode R).comp f.toLinearMap) *
      toConv f.toLinearMap = (1 : WithConv (A →ₗ[R] B)) := by
    apply ofConv_injective
    calc
      (toConv ((HopfAlgebra.antipode R).comp f.toLinearMap) *
          toConv f.toLinearMap : WithConv (A →ₗ[R] B)).ofConv =
          (toConv (HopfAlgebra.antipode R) *
            toConv LinearMap.id : WithConv (B →ₗ[R] B)).ofConv.comp
              f.toCoalgHom.toLinearMap := by
        rw [LinearMap.convMul_comp_coalgHom_distrib]
        rfl
      _ = (1 : WithConv (B →ₗ[R] B)).ofConv.comp f.toLinearMap := by
        rw [LinearMap.antipode_mul_id]
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv := by
        exact LinearMap.convOne_comp_coalgHom f.toCoalgHom
  have hright : toConv f.toLinearMap *
      toConv (f.toLinearMap.comp (HopfAlgebra.antipode R)) =
        (1 : WithConv (A →ₗ[R] B)) := by
    apply ofConv_injective
    calc
      (toConv f.toLinearMap *
          toConv (f.toLinearMap.comp (HopfAlgebra.antipode R)) :
            WithConv (A →ₗ[R] B)).ofConv =
          (f : A →ₐ[R] B).toLinearMap.comp
            (toConv LinearMap.id * toConv (HopfAlgebra.antipode R) :
              WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.algHom_comp_convMul_distrib]
        rfl
      _ = f.toLinearMap.comp (1 : WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.id_mul_antipode]
        rfl
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv := by
        exact LinearMap.algHom_comp_convOne (f : A →ₐ[R] B)
  have heq := toConv_injective (left_inv_eq_right_inv hleft hright)
  exact (LinearMap.congr_fun heq x).symm

end BialgHom
