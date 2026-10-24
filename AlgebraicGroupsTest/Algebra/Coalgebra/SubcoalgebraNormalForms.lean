/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv

universe u v w w₁

section

example {K : Type u} [Field K] :
    (1 : K) ∉ (CoalgEquiv.refl K K).subcoalgebraCongr
      (⊥ : Subcoalgebra K K) := by
  simp

end
