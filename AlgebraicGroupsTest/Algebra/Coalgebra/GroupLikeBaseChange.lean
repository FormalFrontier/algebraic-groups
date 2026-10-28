/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeBaseChange
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Group-like scalar extension on diagonal coalgebras

The integral diagonal coalgebra `MonoidAlgebra ℤ ℕ` has a normalized coordinate
point at label `37`. Extension from `ℤ` to `Polynomial ℤ` preserves this point
and its two group-like equations. Both the source point and its image are
nonzero. Replacing its coefficient `1` by `2` gives a point that is not
group-like, before or after extension.

Extension of the same coalgebra to the zero algebra `PUnit` sends zero to a
group-like element although the source counit is not one. This boundary
concerns arbitrary scalar extension; it does not characterize all extensions
that reflect group-like elements.

## References

Mathlib supplies the diagonal monoid-algebra coalgebra and its coordinate
points in `Mathlib.RingTheory.Coalgebra.MonoidAlgebra` and
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`. Its polynomial module is free by
`Mathlib.LinearAlgebra.Finsupp.VectorSpace`; free nontrivial modules are
faithfully flat by `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra

namespace CoalgebraTest

/-- The integral coordinate point and its polynomial scalar extension satisfy
both the fieldwise equations and the full group-like predicate. Their nonzero
values and the coefficient-two failures distinguish normalization from a
vacuous condition. -/
theorem integral_polynomial_baseChange_single_one :
    Module.FaithfullyFlat ℤ (Polynomial ℤ) ∧
      (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) ≠ 0 ∧
      ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
        (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ≠ 0 ∧
      (counit (R := ℤ) (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) = 1 ∧
        comul (R := ℤ) (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) =
          (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) ⊗ₜ[ℤ]
            (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ∧
      (counit (R := Polynomial ℤ)
          ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
            (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) = 1 ∧
        comul (R := Polynomial ℤ)
          ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
            (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) =
          ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
            (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ⊗ₜ[Polynomial ℤ]
              ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
                (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ))) ∧
      IsGroupLikeElem ℤ (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) ∧
      IsGroupLikeElem (Polynomial ℤ)
        ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
          (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ∧
      (IsGroupLikeElem (Polynomial ℤ)
          ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
            (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ↔
        IsGroupLikeElem ℤ (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)) ∧
      ¬ IsGroupLikeElem ℤ (MonoidAlgebra.single 37 (2 : ℤ) : MonoidAlgebra ℤ ℕ) ∧
      ¬ IsGroupLikeElem (Polynomial ℤ)
        ((1 : Polynomial ℤ) ⊗ₜ[ℤ]
          (MonoidAlgebra.single 37 (2 : ℤ) : MonoidAlgebra ℤ ℕ)) := by
  have hsource : IsGroupLikeElem ℤ
      (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) :=
    MonoidAlgebra.isGroupLikeElem_single_one (R := ℤ) (A := ℤ) 37
  have htarget := Coalgebra.baseChange_counit_eq_one_and_comul_eq_tmul_self
    ℤ (Polynomial ℤ) (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)
    hsource.counit_eq_one hsource.comul_eq_tmul_self
  have hsource_ne : (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ) ≠ 0 := by
    intro h
    have hc := congrArg (fun x : MonoidAlgebra ℤ ℕ => x.coeff 37) h
    simp at hc
  have htwo : ¬ IsGroupLikeElem ℤ
      (MonoidAlgebra.single 37 (2 : ℤ) : MonoidAlgebra ℤ ℕ) := by
    intro h
    simpa using h.counit_eq_one
  refine ⟨inferInstance, hsource_ne, ?_,
    (Coalgebra.baseChange_counit_eq_one_and_comul_eq_tmul_self_iff
      ℤ (Polynomial ℤ) (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ)).mp htarget,
    htarget, hsource, IsGroupLikeElem.baseChange (Polynomial ℤ) hsource,
    TauCeti.isGroupLikeElem_one_tmul_iff (R := ℤ) (K := Polynomial ℤ)
      (MonoidAlgebra.single 37 (1 : ℤ) : MonoidAlgebra ℤ ℕ), htwo, ?_⟩
  · intro h
    apply hsource_ne
    apply Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := ℤ) (B := Polynomial ℤ) (MonoidAlgebra ℤ ℕ)
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using h
  · intro h
    exact htwo ((TauCeti.isGroupLikeElem_one_tmul_iff (R := ℤ) (K := Polynomial ℤ)
      (MonoidAlgebra.single 37 (2 : ℤ) : MonoidAlgebra ℤ ℕ)).mp h)

/-- The zero element of the same integral coalgebra is not normalized, but
its image over the zero algebra satisfies both group-like equations and the
full group-like predicate. This scalar extension is not faithfully flat. -/
theorem integral_punit_baseChange_zero :
    counit (R := ℤ) (0 : MonoidAlgebra ℤ ℕ) = 0 ∧
      counit (R := ℤ) (0 : MonoidAlgebra ℤ ℕ) ≠ 1 ∧
      ¬ IsGroupLikeElem ℤ (0 : MonoidAlgebra ℤ ℕ) ∧
      (counit (R := PUnit) ((1 : PUnit) ⊗ₜ[ℤ] (0 : MonoidAlgebra ℤ ℕ)) = 1 ∧
        comul (R := PUnit) ((1 : PUnit) ⊗ₜ[ℤ] (0 : MonoidAlgebra ℤ ℕ)) =
          ((1 : PUnit) ⊗ₜ[ℤ] (0 : MonoidAlgebra ℤ ℕ)) ⊗ₜ[PUnit]
            ((1 : PUnit) ⊗ₜ[ℤ] (0 : MonoidAlgebra ℤ ℕ))) ∧
      IsGroupLikeElem PUnit ((1 : PUnit) ⊗ₜ[ℤ] (0 : MonoidAlgebra ℤ ℕ)) ∧
      ¬ Module.FaithfullyFlat ℤ PUnit := by
  have hzero : counit (R := ℤ) (0 : MonoidAlgebra ℤ ℕ) ≠ 1 := by simp
  refine ⟨by simp, hzero, ?_, ⟨Subsingleton.elim _ _, by simp⟩,
    ⟨Subsingleton.elim _ _, by simp⟩, ?_⟩
  · intro h
    exact hzero h.counit_eq_one
  · intro h
    let := h
    have h01 : (0 : ℤ) = 1 :=
      FaithfulSMul.algebraMap_injective ℤ PUnit (Subsingleton.elim _ _)
    exact zero_ne_one h01

end CoalgebraTest
