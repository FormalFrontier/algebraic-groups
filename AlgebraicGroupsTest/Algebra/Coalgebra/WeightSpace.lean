/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Unit and generator weights in a regular monoid algebra

The regular coaction on `R[Multiplicative ℤ]` has the unit and integer-generator
weights. Over `ℕ` these occur distinctly and nontrivially; over `ℚ` their weight
submodules are disjoint. The group-like laws come from Mathlib's standard
monoid-algebra coalgebra, without any additional cyclic-group construction.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Coalgebra Coalgebra.RightComodule

namespace Coalgebra.RightComodule.WeightSpaceExamples

/-- The unit weight of the regular monoid algebra of the infinite cyclic group. -/
def unitWeight (R : Type*) [CommSemiring R] :
    GroupLike R (MonoidAlgebra R (Multiplicative ℤ)) :=
  ⟨MonoidAlgebra.single 1 1, MonoidAlgebra.isGroupLikeElem_single_one 1⟩

/-- The integer-generator weight in the same regular monoid algebra. -/
def generatorWeight (R : Type*) [CommSemiring R] :
    GroupLike R (MonoidAlgebra R (Multiplicative ℤ)) :=
  ⟨MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1,
    MonoidAlgebra.isGroupLikeElem_single_one (Multiplicative.ofAdd (1 : ℤ))⟩

theorem unitWeight_ne_generatorWeight (R : Type*) [CommSemiring R] [Nontrivial R] :
    unitWeight R ≠ generatorWeight R := by
  intro h
  have hm : (1 : Multiplicative ℤ) = Multiplicative.ofAdd (1 : ℤ) :=
    MonoidAlgebra.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
      (congrArg GroupLike.val h)
  exact (by simp : Multiplicative.ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ)) hm.symm

local notation "Aℕ" => MonoidAlgebra ℕ (Multiplicative ℤ)
local notation "Aℚ" => MonoidAlgebra ℚ (Multiplicative ℤ)

example :
    (unitWeight ℕ).val ∈ (regular ℕ Aℕ).weightSpace (unitWeight ℕ).val ∧
    (generatorWeight ℕ).val ∈ (regular ℕ Aℕ).weightSpace (generatorWeight ℕ).val ∧
    (unitWeight ℕ).val ≠ 0 ∧ (generatorWeight ℕ).val ≠ 0 ∧
    unitWeight ℕ ≠ generatorWeight ℕ := by
  refine ⟨?_, ?_, ?_, ?_, unitWeight_ne_generatorWeight ℕ⟩
  · exact (mem_weightSpace _ _).mpr (unitWeight ℕ).isGroupLikeElem_val.comul_eq_tmul_self
  · exact (mem_weightSpace _ _).mpr (generatorWeight ℕ).isGroupLikeElem_val.comul_eq_tmul_self
  · exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero
  · exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero

example (v : (regular ℕ Aℕ).weightSpace (generatorWeight ℕ).val) :
    (v : Aℕ) = MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ))
      (counit (R := ℕ) (v : Aℕ)) := by
  calc
    (v : Aℕ) = (counit (R := ℕ) (v : Aℕ)) • (generatorWeight ℕ).val :=
      ((regular_weightSpace_inverse (generatorWeight ℕ)).2 v).symm
    _ = _ := by simp only [generatorWeight, MonoidAlgebra.smul_single', mul_one]

example : Disjoint
    ((regular ℚ Aℚ).weightSpace (unitWeight ℚ).val)
    ((regular ℚ Aℚ).weightSpace (generatorWeight ℚ).val) :=
  (iSupIndep_weightSpace (regular ℚ Aℚ)).pairwiseDisjoint
    (unitWeight_ne_generatorWeight ℚ)

example :
    (generatorWeight ℚ).val ∈ (regular ℚ Aℚ).weightSpace (generatorWeight ℚ).val ∧
    (generatorWeight ℚ).val ≠ 0 := by
  exact ⟨(mem_weightSpace _ _).mpr (generatorWeight ℚ).isGroupLikeElem_val.comul_eq_tmul_self,
    MonoidAlgebra.single_ne_zero.mpr one_ne_zero⟩

example : (scalar ℕ (Fin 0 → ℕ)).weightSpace (1 : ℕ) = ⊥ :=
  Subsingleton.elim _ _

example (v : PUnit) : v ∈ (regular PUnit PUnit).weightSpace (0 : PUnit) :=
  (mem_weightSpace _ _).mpr (Subsingleton.elim _ _)

end Coalgebra.RightComodule.WeightSpaceExamples
