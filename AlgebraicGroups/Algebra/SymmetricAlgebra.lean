/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on a symmetric algebra

The symmetric algebra of a module over a commutative ring is a Hopf algebra whose
generators are primitive. Its antipode sends every generator to its additive inverse.

Mathlib supplies the primitive bialgebra structure and the Hopf-algebra constructor;
this file supplies the antipode for an arbitrary module. The rank-one primitive
coordinate specializes to the additive-group coproduct in Milne's item 2.1.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.1 (rank-one additive coordinate).
- Mathlib, `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra` (primitive generators)
  and `Mathlib.RingTheory.HopfAlgebra.Basic` (`HopfAlgebra.ofAlgHom`).
-/

public section

noncomputable section

namespace SymmetricAlgebra

variable (K : Type*) [CommRing K] (M : Type*) [AddCommMonoid M] [Module K M]

/-- The algebra endomorphism of a symmetric algebra that negates every generator. -/
@[expose] def antipodeAlgHom : SymmetricAlgebra K M →ₐ[K] SymmetricAlgebra K M :=
  lift (-ι K M)

@[simp]
theorem antipodeAlgHom_ι (x : M) :
    antipodeAlgHom K M (ι K M x) = -ι K M x := by
  simp [antipodeAlgHom]

/-- The Hopf algebra structure on a symmetric algebra, extending Mathlib's
`SymmetricAlgebra.instBialgebra` by the antipode negating each generator. -/
instance instHopfAlgebra : HopfAlgebra K (SymmetricAlgebra K M) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom K M)
    (by
      apply algHom_ext
      ext x
      simp [antipodeAlgHom, algebraMapInv_ι])
    (by
      apply algHom_ext
      ext x
      simp [antipodeAlgHom, algebraMapInv_ι])

@[simp]
theorem antipode_ι (x : M) :
    HopfAlgebra.antipode K (ι K M x) = -ι K M x := by
  change antipodeAlgHom K M (ι K M x) = -ι K M x
  simp

end SymmetricAlgebra
