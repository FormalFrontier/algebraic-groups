/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.Algebra.SymmetricAlgebra
public import Mathlib.Data.ZMod.Basic

/-!
# Symmetric Hopf algebra regression checks

The clients retain structure compatibility and the primitive-generator laws,
including integer coefficients and the zero ring. The generator antipode equation
over `ZMod 2` is also available to importers.
-/

set_option warningAsError true

noncomputable section

open scoped TensorProduct

namespace SymmetricAlgebra

universe u v

variable (K : Type u) [CommRing K] (M : Type v) [AddCommMonoid M] [Module K M]

@[instance_reducible] private noncomputable def persistentTestSymmetricAlgebra001 :
    Bialgebra K (SymmetricAlgebra K M) := inferInstance

@[instance_reducible] private noncomputable def persistentTestSymmetricAlgebra002 :
    HopfAlgebra K (SymmetricAlgebra K M) := inferInstance

private theorem persistentTestSymmetricAlgebra003 :
    (instHopfAlgebra K M).toHopfAlgebraStruct.toBialgebra = instBialgebra K M := rfl

private theorem persistentTestSymmetricAlgebra004 (x : M) :
    antipodeAlgHom K M (ι K M x) = -ι K M x := by simp

private theorem persistentTestSymmetricAlgebra005 (x : M) :
    HopfAlgebra.antipode K (ι K M x) = -ι K M x := by simp

private theorem persistentTestSymmetricAlgebra006 (x : M) :
    Coalgebra.comul (R := K) (ι K M x) =
      ι K M x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] ι K M x := by simp

private theorem persistentTestSymmetricAlgebra007 (x : M) :
    Coalgebra.counit (R := K) (ι K M x) = 0 := by simp

@[instance_reducible] private noncomputable def persistentTestSymmetricAlgebra008 :
    HopfAlgebra Int (SymmetricAlgebra Int Int) := inferInstance

@[instance_reducible] private noncomputable def persistentTestSymmetricAlgebra009 :
    HopfAlgebra (ZMod 2) (SymmetricAlgebra (ZMod 2) (ZMod 2)) := inferInstance

@[instance_reducible] private noncomputable def persistentTestSymmetricAlgebra010 :
    HopfAlgebra (ZMod 1) (SymmetricAlgebra (ZMod 1) (ZMod 1)) := inferInstance

/-- On each generator of the symmetric algebra of `ZMod 2`, the antipode acts by negation. -/
public theorem antipode_ι_zmod_two (x : ZMod 2) :
    HopfAlgebra.antipode (ZMod 2) (ι (ZMod 2) (ZMod 2) x) =
      -ι (ZMod 2) (ZMod 2) x := by simp

private theorem persistentTestSymmetricAlgebra012 (x : ZMod 1) :
    HopfAlgebra.antipode (ZMod 1) (ι (ZMod 1) (ZMod 1) x) =
      -ι (ZMod 1) (ZMod 1) x := by simp

end SymmetricAlgebra
