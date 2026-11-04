/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Construction
public import AlgebraicGroups.Algebra.HopfAlgebra.Pure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Purity of finite-dimensional Hopf subalgebras

A given finite-dimensional Hopf subalgebra has injective tensor units for every module
on the subalgebra. Its self-injectivity extends the identity along the original
subalgebra-linear inclusion, and tensoring this retraction splits each tensor unit.
The proof uses `HopfAlgebra.injective_self` and Mathlib's
`Module.Injective.extension_property`, `TensorProduct.map` and `TensorProduct.lid`.

For a finite-type Hopf subalgebra with nil augmentation kernel, subtracting the counit
scalar makes each element nilpotent. Mathlib's integrality APIs then give integrality,
hence finite-dimensionality, of that same subalgebra.

## Limitations

These are purity results for a supplied finite-dimensional Hopf subalgebra and for the
nil-augmentation finite-type case. They do not prove faithful flatness for arbitrary
Hopf subalgebras, nor require the ambient Hopf algebra to be finite-dimensional or
of finite type.

## References

* J. S. Milne, *Algebraic Groups*, Theorem 3.31, for the nil-augmentation setting.
  The purity proof here instead uses self-injectivity of finite-dimensional Hopf
  algebras and module splitting.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Subalgebra

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [HopfAlgebra K A]

/-- The inclusion of a finite-dimensional Hopf subalgebra is pure: every tensor unit
is injective. The proof splits the inclusion using self-injectivity of the subalgebra. -/
theorem tensorProduct_mk_one_injective (B : Subalgebra K A) (hB : B.IsHopfSubalgebra)
    [Module.Finite K B] (N : Type w) [AddCommMonoid N] [Module B N] :
    Function.Injective (TensorProduct.mk B A N 1) := by
  let : HopfAlgebra K B := B.hopfAlgebra hB
  apply HopfAlgebra.tensorProduct_mk_one_injective K B A _ N
  intro b c h
  exact Subtype.ext h

/-- A finite-type Hopf subalgebra whose augmentation kernel consists of nilpotent
elements has injective tensor units. This is the nil-augmentation setting of Milne,
*Algebraic Groups*, Theorem 3.31; the proof here derives finiteness of the given
subalgebra and then uses a different, self-injectivity-based splitting argument. -/
theorem tensorProduct_mk_one_injective_of_isNilpotent_counit
    (B : Subalgebra K A) (hB : B.IsHopfSubalgebra) [Algebra.FiniteType K B]
    (hε : ∀ b : B, Coalgebra.counit (R := K) (b : A) = 0 → IsNilpotent b)
    (N : Type w) [AddCommMonoid N] [Module B N] :
    Function.Injective (TensorProduct.mk B A N 1) := by
  let : HopfAlgebra K B := B.hopfAlgebra hB
  have hnil : ∀ b : B, Bialgebra.counitAlgHom K B b = 0 → IsNilpotent b := by
    intro b hb
    apply hε b
    rw [← B.coalgebraOfComulMem_counit hB.comul_mem b]
    exact hb
  have : Algebra.IsIntegral K B := ⟨fun b => by
    let c : K := Bialgebra.counitAlgHom K B b
    obtain ⟨n, hn⟩ := hnil (b - algebraMap K B c) (by simp [c])
    have hi : IsIntegral K (b - algebraMap K B c) := by
      apply IsIntegral.of_pow (Nat.succ_pos n)
      rw [pow_succ, hn, zero_mul]
      exact isIntegral_zero
    simpa only [sub_add_cancel] using hi.add (isIntegral_algebraMap (x := c))⟩
  have : Module.Finite K B := Algebra.IsIntegral.finite
  exact B.tensorProduct_mk_one_injective hB N

end Subalgebra
