/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CounitRange
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Zero underlying maps of coalgebra homomorphisms

A coalgebra homomorphism has zero underlying linear map exactly when its source is
subsingleton. Counit preservation reduces this to the corresponding criterion for the
source counit. The scalar semiring, source and target may lie in independent universes.
Only the source needs the coalgebra laws; the target needs a coalgebra structure.

## References

Counit preservation and the bundled homomorphism API are supplied by
`Mathlib.RingTheory.Coalgebra.Hom`. The source criterion is
`Coalgebra.counit_eq_zero_iff` from `AlgebraicGroups.Algebra.Coalgebra.CounitRange`.
The reverse implication uses Mathlib's uniqueness of linear maps from a subsingleton
module in `Mathlib.Algebra.Module.LinearMap.Defs`.
-/

@[expose] public section

universe u v w

namespace CoalgHom

variable {R : Type u} {C : Type v} {C' : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid C'] [Module R C'] [CoalgebraStruct R C']

/-- The underlying linear map of a coalgebra homomorphism is zero exactly when its
source is subsingleton. Only a coalgebra structure is required on the target. -/
theorem toLinearMap_eq_zero_iff (f : C →ₗc[R] C') :
    f.toLinearMap = 0 ↔ Subsingleton C := by
  constructor
  · intro hf
    apply (Coalgebra.counit_eq_zero_iff R C).mp
    simpa only [hf, LinearMap.comp_zero] using f.counit_comp.symm
  · intro h
    have : Subsingleton C := h
    exact Subsingleton.elim _ _

end CoalgHom
