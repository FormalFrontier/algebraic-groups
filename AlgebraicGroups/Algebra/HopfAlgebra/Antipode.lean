/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Involutivity of antipodes in commutative or cocommutative Hopf algebras

The antipode of a Hopf algebra over a commutative semiring is involutive if
its multiplication is commutative or its comultiplication is cocommutative.
These are different sufficient conditions: the cocommutative result allows
noncommutative multiplication, while the commutative result needs no
cocommutativity.

For commutative multiplication, the proof applies involutivity of inversion
to the convolution group of algebra endomorphisms: inversion is composition
with the antipode. For cocommutative comultiplication, antimultiplicativity
of the antipode transforms a convolution inverse identity into one for its
square; uniqueness of left and right convolution inverses then identifies
the square with the identity. The pointwise identities are simp lemmas.

Involutivity is not asserted for arbitrary Hopf algebras. Neither result
requires additive inverses, finiteness or nontriviality.

## References

* Mathlib, `RingTheory/HopfAlgebra/Convolution`, by Yaël Dillies,
  Michał Mrugała and Yunzhou Xie: antimultiplicativity of the antipode,
  its linear convolution inverse identities, the antipode algebra homomorphism
  and the convolution group of algebra homomorphisms.
* Mathlib, `RingTheory/Coalgebra/Convolution`, by Yaël Dillies,
  Michał Mrugała and Yunzhou Xie: convolution multiplication and its unit
  on linear maps.
* Mathlib, `RingTheory/Coalgebra/Basic`, by Ali Ramsey and Eric Wieser,
  and `LinearAlgebra/TensorProduct/Map`, by Kenny Lau and Mario Carneiro:
  cocommutativity and naturality of tensor symmetry.
* Mathlib, `Algebra/WithConv`, by Monica Omar, and `Algebra/Group/DivInvMonoid`,
  `Algebra/Group/Defs` and `Algebra/Group/Monoid`, by Jeremy Avigad,
  Leonardo de Moura, Simon Hudon and Mario Carneiro: the convolution type synonym,
  involutivity of inversion and uniqueness of left and right inverses.
* Mathlib, `CategoryTheory/Monoidal/Hopf_`, by Kim Morrison: the corresponding
  antipode identity for commutative Hopf objects in a braided monoidal category.
-/

@[expose] public section

universe u v

namespace HopfAlgebra

section CommSemiring

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

/-- The antipode of a commutative Hopf algebra is involutive, by involutivity of
inversion in Mathlib's convolution group of algebra endomorphisms. -/
theorem antipode_involutive : Function.Involutive (antipode R (A := A)) := by
  intro a
  exact congrArg (fun f : WithConv (A →ₐ[R] A) => f.ofConv a)
    (inv_inv (WithConv.toConv (AlgHom.id R A)))

/-- Applying the antipode twice in a commutative Hopf algebra returns the input. -/
@[simp]
theorem antipode_antipode (a : A) : antipode R (antipode R a) = a :=
  antipode_involutive a

/-- The square of the antipode as a linear map is the identity in a commutative Hopf algebra. -/
@[simp]
theorem antipode_comp_antipode :
    (antipode R (A := A)).comp (antipode R) = LinearMap.id := by
  ext a
  exact antipode_antipode a

end CommSemiring

section IsCocomm

open WithConv

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A]

local notation "𝑺" => antipode R (A := A)

/-- The antipode of a cocommutative Hopf algebra is involutive, by
antimultiplicativity and uniqueness of left and right convolution inverses. -/
theorem antipode_involutive_of_isCocomm : Function.Involutive (antipode R (A := A)) := by
  -- Postcomposing `S ⋆ id = 1` by `S` gives `S ⋆ S² = 1`.
  -- Cocommutativity removes the tensor symmetry introduced by antimultiplicativity.
  have hright : toConv 𝑺 * toConv (𝑺 ∘ₗ 𝑺) = 1 := by
    apply WithConv.ext
    calc
      (toConv 𝑺 * toConv (𝑺 ∘ₗ 𝑺)).ofConv =
          𝑺 ∘ₗ (toConv 𝑺 * toConv (LinearMap.id : A →ₗ[R] A)).ofConv := by
        simp only [LinearMap.convMul_def, ofConv_toConv]
        symm
        calc
          𝑺 ∘ₗ LinearMap.mul' R A ∘ₗ
              TensorProduct.map 𝑺 LinearMap.id ∘ₗ Coalgebra.comul =
              𝑺 ∘ₗ LinearMap.mul' R A ∘ₗ
                (TensorProduct.map 𝑺 LinearMap.id ∘ₗ
                  (TensorProduct.comm R A A).toLinearMap) ∘ₗ Coalgebra.comul := by
            rw [LinearMap.comp_assoc, Coalgebra.IsCocomm.comm_comp_comul]
          _ = (𝑺 ∘ₗ LinearMap.mul' R A ∘ₗ
                (TensorProduct.comm R A A).toLinearMap) ∘ₗ
              TensorProduct.map LinearMap.id 𝑺 ∘ₗ Coalgebra.comul := by
            rw [TensorProduct.map_comp_comm_eq]
            simp only [LinearMap.comp_assoc]
          _ = LinearMap.mul' R A ∘ₗ TensorProduct.map 𝑺 𝑺 ∘ₗ
              TensorProduct.map LinearMap.id 𝑺 ∘ₗ Coalgebra.comul := by
            rw [antipode_comp_mul_comp_comm]
            simp only [LinearMap.comp_assoc]
          _ = LinearMap.mul' R A ∘ₗ
              TensorProduct.map 𝑺 (𝑺 ∘ₗ 𝑺) ∘ₗ Coalgebra.comul := by
            rw [← LinearMap.comp_assoc Coalgebra.comul
                (TensorProduct.map LinearMap.id 𝑺) (TensorProduct.map 𝑺 𝑺),
              ← TensorProduct.map_comp, LinearMap.comp_id]
      _ = 𝑺 ∘ₗ (1 : WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.antipode_mul_id]
      _ = (1 : WithConv (A →ₗ[R] A)).ofConv := by
        ext a
        simp [LinearMap.convOne_def, Algebra.algebraMap_eq_smul_one]
  -- The identity is a left inverse of `S`, and its square is a right inverse.
  have hsquare : 𝑺 ∘ₗ 𝑺 = (LinearMap.id : A →ₗ[R] A) :=
    toConv_injective
      (left_inv_eq_right_inv (LinearMap.id_mul_antipode (R := R) (C := A)) hright).symm
  intro a
  exact LinearMap.congr_fun hsquare a

/-- Applying the antipode twice in a cocommutative Hopf algebra returns the input. -/
@[simp]
theorem antipode_antipode_of_isCocomm (a : A) : antipode R (antipode R a) = a :=
  antipode_involutive_of_isCocomm a

/-- The square of the antipode as a linear map is the identity in a cocommutative Hopf algebra. -/
@[simp]
theorem antipode_comp_antipode_of_isCocomm :
    (antipode R (A := A)).comp (antipode R) = LinearMap.id := by
  ext a
  exact antipode_antipode_of_isCocomm a

end IsCocomm

end HopfAlgebra
