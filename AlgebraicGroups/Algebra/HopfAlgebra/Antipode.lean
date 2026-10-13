/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Involutivity of the antipode of a commutative Hopf algebra

The antipode of a commutative Hopf algebra over a commutative semiring is
involutive. The proof applies involutivity of inversion to the convolution
group of algebra endomorphisms: inversion is composition with the antipode.
The pointwise identity is a simp lemma.

Commutativity of the algebra is essential; the statement is not asserted for
an arbitrary noncommutative Hopf algebra. Neither cocommutativity nor any
finiteness or nontriviality hypothesis is needed.

## References

* Mathlib, `RingTheory/HopfAlgebra/Convolution`, by Yaël Dillies,
  Michał Mrugała and Yunzhou Xie: the antipode algebra homomorphism and
  the convolution group of algebra homomorphisms.
* Mathlib, `Algebra/WithConv`, by Monica Omar, and `Algebra/Group/DivInvMonoid`
  and `Algebra/Group/Defs`, by Jeremy Avigad, Leonardo de Moura, Simon Hudon
  and Mario Carneiro: the convolution type synonym and involutivity of inversion.
* Mathlib, `CategoryTheory/Monoidal/Hopf_`, by Kim Morrison: the corresponding
  antipode identity for commutative Hopf objects in a braided monoidal category.
-/

@[expose] public section

universe u v

namespace HopfAlgebra

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

end HopfAlgebra
