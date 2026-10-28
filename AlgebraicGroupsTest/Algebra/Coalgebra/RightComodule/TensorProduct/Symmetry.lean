/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Symmetry
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Distinct-coefficient clients for external tensor symmetry

The regular coalgebras on `Bool` and `Fin 3` distinguish coefficient reindexing
from carrier transport. The naturality client uses twice and three times the
identity, so the swapped output retains both nonidentity morphisms.
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra (RightComoduleHom)
open Coalgebra.RightComodule

noncomputable section

namespace CoalgebraExternalTensorSymmetryExamples

local notation "C" => MonoidAlgebra ℕ Bool
local notation "D" => MonoidAlgebra ℕ (Fin 3)
local notation "c" => (MonoidAlgebra.single false 1 : C)
local notation "d" => (MonoidAlgebra.single (0 : Fin 3) 1 : D)
local notation "X" =>
  @regular ℕ C _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ Bool)
local notation "Y" =>
  @regular ℕ D _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ (Fin 3))

-- Coefficient symmetry exchanges the two different monoid-algebra coalgebras.
example : Coalgebra.TensorProduct.comm ℕ C D (c ⊗ₜ[ℕ] d) = d ⊗ₜ[ℕ] c :=
  Coalgebra.TensorProduct.comm_tmul ℕ C D c d

-- Forward carrier symmetry is a morphism over D ⊗ C, after coefficient change.
example : externalTensorCommHom X Y (c ⊗ₜ[ℕ] d) = d ⊗ₜ[ℕ] c :=
  externalTensorCommHom_tmul X Y c d

-- Its inverse has the same coefficient coalgebra, not the unreindexed C ⊗ D.
example : externalTensorCommInvHom X Y (d ⊗ₜ[ℕ] c) = c ⊗ₜ[ℕ] d :=
  externalTensorCommInvHom_tmul X Y c d

-- Naturality swaps the nonidentity output, rather than replacing either map by id.
example :
    ((externalTensorCommHom X Y).comp
      ((((2 : ℕ) • RightComoduleHom.id X).externalTensor
        ((3 : ℕ) • RightComoduleHom.id Y)).mapCoalgebra
          (Coalgebra.TensorProduct.comm ℕ C D).toCoalgHom)) (c ⊗ₜ[ℕ] d) =
      ((3 : ℕ) • d) ⊗ₜ[ℕ] ((2 : ℕ) • c) := by
  rw [externalTensorCommHom_naturality, RightComoduleHom.comp_apply,
    externalTensorCommHom_tmul, RightComoduleHom.externalTensor_tmul]
  rfl

end CoalgebraExternalTensorSymmetryExamples
