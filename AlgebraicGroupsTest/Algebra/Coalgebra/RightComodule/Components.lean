/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Components
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightDecomposition
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoefficients
public import AlgebraicGroupsTest.Algebra.Coalgebra.RightComodule

/-!
# Components in a regular monoid-algebra comodule

The coefficient semiring is `ℕ × ℕ` and the basis index is the infinite type `ℕ`.
The two-support vector `single 1 (1, 0) + single 0 (0, 1)` is used directly in the
regular comodule, with Mathlib's standard basis and its group-like singleton-one
vectors. Its components are vectors, not scalar coefficients.

The same vector is also recovered through the canonical weight-decomposition
equivalence, whose coordinates are its singleton summands.

The zero-ambient boundary uses `RightComoduleExamples.zeroAmbientComodule` and the
singleton basis of the scalar coalgebra. No basis of the ambient module is needed.

## References

The inputs use Mathlib's monoid-algebra basis and singleton-one group-like family,
and the regular and scalar coactions of `Coalgebra.RightComodule`. The component
formulas use Mathlib's tensor-product basis coordinate API.
-/

@[expose] public section

open scoped TensorProduct

namespace RightComoduleComponentsExamples

local notation "R" => ℕ × ℕ
local notation "C" => MonoidAlgebra R ℕ
local notation "X" => Coalgebra.RightComodule.regular R C
local notation "b" => MonoidAlgebra.basis ℕ R
local notation "f" => (MonoidAlgebra.single 1 (1, 0) + MonoidAlgebra.single 0 (0, 1) : C)

/-- The components of the two-support vector are exactly its singleton summands;
in particular all components at other indices vanish. -/
example (i : ℕ) :
    (X).components b f i = MonoidAlgebra.single i ((f).coeff i) := by
  by_cases h1 : i = 1 <;> by_cases h0 : i = 0 <;>
    simp_all [Coalgebra.RightComodule.components_apply, Module.Basis.coord_apply,
      MonoidAlgebra.basis_repr, CommSemiring.comul_apply]

/-- Each component in the regular comodule has the corresponding basis weight. -/
example (i : ℕ) :
    (X).coaction ((X).components b f i) = ((X).components b f i) ⊗ₜ[R] b i := by
  have hb (j : ℕ) : IsGroupLikeElem R (b j) := by
    simpa only [MonoidAlgebra.basis_apply] using
      (MonoidAlgebra.isGroupLikeElem_single_one («R» := R) (A := R) j)
  exact (X).coaction_components b hb f i

/-- Finite summation recovers the two-support vector. -/
example : ((X).components b f).sum (fun _ w => w) = f := by
  have hb (j : ℕ) : IsGroupLikeElem R (b j) := by
    simpa only [MonoidAlgebra.basis_apply] using
      (MonoidAlgebra.isGroupLikeElem_single_one («R» := R) (A := R) j)
  exact (X).sum_components b hb f

/-- The component linear map sends zero to zero in the zero ambient module. -/
example :
    RightComoduleExamples.zeroAmbientComodule.components
      (Module.Basis.singleton PUnit ℕ) 0 = 0 :=
  map_zero _

/-- The component identity also applies when the ambient module is zero. -/
example (i : PUnit) :
    RightComoduleExamples.zeroAmbientComodule.coaction
        (RightComoduleExamples.zeroAmbientComodule.components
          (Module.Basis.singleton PUnit ℕ) 0 i) =
      (RightComoduleExamples.zeroAmbientComodule.components
        (Module.Basis.singleton PUnit ℕ) 0 i) ⊗ₜ[ℕ]
          (Module.Basis.singleton PUnit ℕ) i := by
  have hb (j : PUnit) : IsGroupLikeElem ℕ ((Module.Basis.singleton PUnit ℕ) j) := by
    simpa only [Module.Basis.singleton_apply] using
      (IsGroupLikeElem.one («R» := ℕ) (A := ℕ))
  exact RightComoduleExamples.zeroAmbientComodule.coaction_components
    (Module.Basis.singleton PUnit ℕ) hb 0 i

/-- Finite component recovery includes the zero-ambient boundary. -/
example :
    (RightComoduleExamples.zeroAmbientComodule.components
      (Module.Basis.singleton PUnit ℕ) 0).sum (fun _ w => w) = 0 := by
  have hb (j : PUnit) : IsGroupLikeElem ℕ ((Module.Basis.singleton PUnit ℕ) j) := by
    simpa only [Module.Basis.singleton_apply] using
      (IsGroupLikeElem.one («R» := ℕ) (A := ℕ))
  exact RightComoduleExamples.zeroAmbientComodule.sum_components
    (Module.Basis.singleton PUnit ℕ) hb 0

private theorem basis_isGroupLike (i : ℕ) : IsGroupLikeElem R (b i) := by
  simpa only [MonoidAlgebra.basis_apply] using
    (MonoidAlgebra.isGroupLikeElem_single_one («R» := R) (A := R) i)

/-- The canonical decomposition extracts the singleton summands of the same
infinite-index vector, and its inverse recovers that vector. -/
example (i : ℕ) :
    (((X).weightDecomposition b basis_isGroupLike f) i : C) =
        MonoidAlgebra.single i ((f).coeff i) ∧
      ((X).weightDecomposition b basis_isGroupLike).symm
        ((X).weightDecomposition b basis_isGroupLike f) = f := by
  constructor
  · rw [(X).weightDecomposition_apply]
    by_cases h1 : i = 1 <;> by_cases h0 : i = 0 <;>
      simp_all [Coalgebra.RightComodule.components_apply, Module.Basis.coord_apply,
        MonoidAlgebra.basis_repr, CommSemiring.comul_apply]
  · exact ((X).weightDecomposition b basis_isGroupLike).symm_apply_apply f

end RightComoduleComponentsExamples
