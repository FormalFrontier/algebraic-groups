/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Unitors

/-!
# A nonidentity naturality use of both external tensor unitors

For the canonical regular comodule over `ℕ`, naturality moves the morphism
`3 • id` through either unitor. Inputs with scalar factor `2` give `6`, not `1`.
This uses the morphisms after the required forward change of coefficients.
-/

open scoped TensorProduct
open Coalgebra (RightComoduleHom)
open Coalgebra.RightComodule

noncomputable section

namespace CoalgebraExternalTensorUnitorExamples

example :
    ((externalTensorLeftUnitor (regular ℕ ℕ)).comp
      (((RightComoduleHom.id (regular ℕ ℕ)).externalTensor
        ((3 : ℕ) • RightComoduleHom.id (regular ℕ ℕ))).mapCoalgebra
          (Coalgebra.TensorProduct.lid ℕ ℕ).toCoalgHom))
            ((2 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 6 ∧
    ((externalTensorRightUnitor (regular ℕ ℕ)).comp
      ((((3 : ℕ) • RightComoduleHom.id (regular ℕ ℕ)).externalTensor
        (RightComoduleHom.id (regular ℕ ℕ))).mapCoalgebra
          (Coalgebra.TensorProduct.rid ℕ ℕ ℕ).toCoalgHom))
            ((1 : ℕ) ⊗ₜ[ℕ] (2 : ℕ)) = 6 ∧
    (6 : ℕ) ≠ 1 := by
  constructor
  · rw [externalTensorLeftUnitor_naturality]
    rfl
  · constructor
    · rw [externalTensorRightUnitor_naturality]
      rfl
    · decide

end CoalgebraExternalTensorUnitorExamples
