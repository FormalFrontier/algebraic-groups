/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
import Mathlib.Algebra.Field.Rat

/-!
# Greatest subcoalgebras and the scalar coalgebra

Inclusion into the greatest subcoalgebra factors the underlying submodule inclusion.
For the rational scalar coalgebra, the greatest subcoalgebra contains a nonzero lift
of the ambient element `1`, with its counit and comultiplication inherited through
inclusion. No multiplicative structure on the subcoalgebra subtype is needed.

A rational subcoalgebra containing `1` is the greatest subcoalgebra: scalar closure
puts every rational number in its carrier. The identity coalgebra homomorphism also
factors through the greatest subcoalgebra by codomain restriction.

## References

The scalar coalgebra and its structure maps are Mathlib's `CommSemiring.toCoalgebra`,
`CommSemiring.counit_apply` and `CommSemiring.comul_apply`, with the field structure
from `Mathlib.Algebra.Field.Rat`. Linear inclusion uses Mathlib's `Submodule.inclusion`
and `Submodule.subtype_comp_inclusion`. Coalgebra inclusion and codomain restriction
use `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom`.
-/

noncomputable section

universe u v

open scoped TensorProduct

namespace CoalgebraTest

/-- The canonical order gives the usual factorization of a submodule inclusion. -/
private theorem subtype_comp_inclusion_top
    {K : Type u} {C : Type v} [Field K] [AddCommGroup C] [Module K C]
    [Coalgebra K C] (D : Subcoalgebra K C) :
    let hD : D.toSubmodule ≤ (⊤ : Subcoalgebra K C).toSubmodule :=
      Subcoalgebra.toSubmodule_le_toSubmodule.mpr le_top
    (⊤ : Subcoalgebra K C).toSubmodule.subtype.comp (Submodule.inclusion hD) =
      D.toSubmodule.subtype := by
  exact Submodule.subtype_comp_inclusion _ _ _

local notation "T" => (⊤ : Subcoalgebra ℚ ℚ)

/-- The greatest rational subcoalgebra contains a nonzero lift of ambient `1` and
its restricted structure maps agree with the scalar coalgebra at that lift. -/
private theorem scalar_top_nonzero :
    (T).toSubmodule ≠ (⊥ : Submodule ℚ ℚ) ∧
      ∃ u : T, (u : ℚ) = 1 ∧ u ≠ 0 ∧
        Coalgebra.counit (R := ℚ) (A := T) u = 1 ∧
        TensorProduct.mapIncl (T).toSubmodule (T).toSubmodule
            (Coalgebra.comul (R := ℚ) (A := T) u) =
          (1 : ℚ) ⊗ₜ[ℚ] (1 : ℚ) := by
  have h1 : (1 : ℚ) ∈ T := Subcoalgebra.mem_top
  let u : T := ⟨1, h1⟩
  refine ⟨?_, u, rfl, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : (1 : ℚ) ∈ (T).toSubmodule := h1
    rw [hbot, Submodule.mem_bot] at hmem
    exact (one_ne_zero : (1 : ℚ) ≠ 0) hmem
  · intro hzero
    exact (one_ne_zero : (1 : ℚ) ≠ 0)
      (congrArg (fun x : T => (x : ℚ)) hzero)
  · simpa only [CommSemiring.counit_apply] using Subcoalgebra.coalgebra_counit_apply T u
  · simpa only [CommSemiring.comul_apply] using Subcoalgebra.mapIncl_coalgebra_comul T u

/-- Containing ambient `1` forces a rational subcoalgebra to be the greatest one. -/
private theorem scalar_eq_top_of_one_mem :
    ∀ D : Subcoalgebra ℚ ℚ, (1 : ℚ) ∈ D → D = T := by
  intro D h1
  apply Subcoalgebra.eq_top_iff.mpr
  intro q
  simpa only [smul_eq_mul, mul_one] using D.smul_mem q h1

/-- Restricting the identity to the greatest subcoalgebra preserves the identity
factorization and recovers ambient `1` under inclusion. -/
private theorem scalar_top_identity_factorization :
    let j := (CoalgHom.id ℚ ℚ).codRestrict T (fun _ => Subcoalgebra.mem_top)
    (T).subtype.comp j = CoalgHom.id ℚ ℚ ∧ (T).subtype (j 1) = 1 := by
  constructor
  · exact CoalgHom.subtype_comp_codRestrict _ _ _
  · rw [Subcoalgebra.subtype_apply, CoalgHom.coe_codRestrict]
    rfl

end CoalgebraTest
