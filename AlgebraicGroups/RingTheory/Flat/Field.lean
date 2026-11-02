/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat modules over a field

A module over a field is flat even when its additive structure is given only
as an additive commutative monoid. The canonical additive group structure is
needed only to apply the vector-space freeness theorem; the flatness conclusion
uses the original additive monoid and module structures.

## References

Mathlib's `Module.addCommMonoidToAddCommGroup`, `Module.Free.of_divisionRing`
and `Module.Flat.of_free` supply the additive group, freeness and flatness proofs.
-/

@[expose] public section

universe u v

namespace Module.Flat

/-- Every module over a field is flat, with no additive-group structure required
as input. -/
theorem of_field (K : Type u) (M : Type v)
    [Field K] [AddCommMonoid M] [Module K M] : Module.Flat K M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K M := Module.Free.of_divisionRing K M
  exact Module.Flat.of_free

/-- For an additive commutative group, `of_field` agrees with the flatness proof
obtained from Mathlib's division-ring freeness instance. -/
theorem of_field_eq_of_free (K : Type u) (M : Type v)
    [Field K] [AddCommGroup M] [Module K M] :
    of_field K M =
      @Module.Flat.of_free K M (inferInstance : CommSemiring K)
        (inferInstance : AddCommMonoid M) (inferInstance : Module K M)
        (Module.Free.of_divisionRing K M) :=
  Subsingleton.elim _ _

end Module.Flat
