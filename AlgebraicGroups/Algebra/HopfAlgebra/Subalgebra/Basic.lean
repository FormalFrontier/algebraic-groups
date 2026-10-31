/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf-stable subalgebras

`Subalgebra.IsHopfSubalgebra` expresses stability under comultiplication and the antipode.
It is a predicate on a subalgebra, so membership, coercions and extensionality are those
of `Subalgebra`. No condition on the counit is needed.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Subalgebra

variable {K : Type u} {B : Type v}
variable [CommSemiring K] [Semiring B] [HopfAlgebraStruct K B]

/-- A subalgebra is Hopf-stable if its comultiplication takes values in its tensor square
and its antipode takes values in the subalgebra. -/
structure IsHopfSubalgebra (S : Subalgebra K B) : Prop where
  /-- Comultiplication takes values in the image of the tensor square of the inclusion. -/
  comul_mem : ∀ s : S, Coalgebra.comul (R := K) (s : B) ∈
    LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)
  /-- The antipode preserves the subalgebra. -/
  antipode_mem : ∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S

/-- Hopf stability consists precisely of comultiplication stability and antipode stability. -/
theorem isHopfSubalgebra_iff (S : Subalgebra K B) :
    S.IsHopfSubalgebra ↔
      (∀ s : S, Coalgebra.comul (R := K) (s : B) ∈
        LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)) ∧
      (∀ s : S, HopfAlgebra.antipode K (s : B) ∈ S) :=
  ⟨fun h => ⟨h.comul_mem, h.antipode_mem⟩, fun h => ⟨h.1, h.2⟩⟩

end Subalgebra
