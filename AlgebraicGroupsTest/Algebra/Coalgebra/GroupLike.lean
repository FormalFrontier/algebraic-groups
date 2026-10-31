/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.GroupLike
import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Hom
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Unit-counit normalization in a group algebra

Over an arbitrary field `k`, the group algebra on `Multiplicative ℤ` has Mathlib's full
Hopf algebra and inherited coalgebra structures. The basis element at integer weight `1`
is a unit with tensor-square comultiplication and unit counit, distinct from zero and the
algebra unit at weight `0`. Its normalization uses the coalgebra criterion with those same
counit-unit and comultiplication inputs.

The scalar
subalgebra is proper and stable under comultiplication and the antipode. Its induced
Hopf algebra retains the inherited algebra and module structures and the induced
coalgebra; the scalar unit homomorphism factors through its inclusion.

Zero satisfies the tensor-square equation in the same coalgebra, but its counit is not a
unit and it is not group-like.

## References

Mathlib's `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, by Amelia Livingston, supplies
its full group-algebra Hopf structure. The group-like basis elements and their units use
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra` and `Mathlib.RingTheory.HopfAlgebra.GroupLike`,
by Amelia Livingston, Yaël Dillies and Michał Mrugała.
-/

@[expose] public section

universe u

open scoped TensorProduct

private abbrev GroupAlgebra (k : Type u) [Field k] :=
  MonoidAlgebra k (Multiplicative ℤ)

private noncomputable abbrev generator (k : Type u) [Field k] : GroupAlgebra k :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k)

private theorem generator_inputs (k : Type u) [Field k] :
    IsUnit (Coalgebra.counit (R := k) (generator k)) ∧
      Coalgebra.comul (R := k) (generator k) = generator k ⊗ₜ[k] generator k ∧
      IsUnit (generator k) ∧ generator k ≠ 0 ∧ generator k ≠ 1 := by
  have ht : IsGroupLikeElem k (generator k) :=
    MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k)
      (Multiplicative.ofAdd (1 : ℤ))
  refine ⟨?_, ht.comul_eq_tmul_self, ht.isUnit, ?_, ?_⟩
  · rw [ht.counit_eq_one]
    exact isUnit_one
  · intro h
    have hc := congrArg
      (fun x : GroupAlgebra k => x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
    exact (one_ne_zero : (1 : k) ≠ 0) (by
      simpa only [generator, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc)
  · intro h
    have hi : Multiplicative.ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ) :=
      fun h => (one_ne_zero : (1 : ℤ) ≠ 0) (ofAdd_eq_one.mp h)
    have hc := congrArg
      (fun x : GroupAlgebra k => x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
    exact (one_ne_zero : (1 : k) ≠ 0) (by
      simpa only [generator, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hi] using hc)

private theorem generator_isGroupLikeElem (k : Type u) [Field k] :
    IsGroupLikeElem k (generator k) := by
  exact IsGroupLikeElem.of_isUnit_counit
    (generator_inputs k).1 (generator_inputs k).2.1

private theorem generator_counit (k : Type u) [Field k] :
    Coalgebra.counit (R := k) (generator k) = 1 :=
  (generator_isGroupLikeElem k).counit_eq_one

private theorem generator_not_mem_scalar_bottom (k : Type u) [Field k] :
    generator k ∉ (⊥ : Subalgebra k (GroupAlgebra k)) := by
  intro ht
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp ht
  have hc1 : c = 1 := by
    have h := congrArg
      (fun x : GroupAlgebra k => Coalgebra.counit (R := k) x) hc
    simpa only [Bialgebra.counit_algebraMap, generator_counit] using h
  apply (generator_inputs k).2.2.2.2
  calc
    generator k = algebraMap k (GroupAlgebra k) c := hc.symm
    _ = 1 := by rw [hc1, map_one]

private theorem scalar_bottom_inputs (k : Type u) [Field k] :
    let S := (⊥ : Subalgebra k (GroupAlgebra k))
    (∀ s : S, Coalgebra.comul (R := k) (s : GroupAlgebra k) ∈
      LinearMap.range (TensorProduct.map S.val.toLinearMap S.val.toLinearMap)) ∧
    (∀ s : S, HopfAlgebra.antipode k (s : GroupAlgebra k) ∈ S) := by
  dsimp only
  constructor
  · intro s
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp s.property
    refine ⟨c • ((1 : (⊥ : Subalgebra k (GroupAlgebra k))) ⊗ₜ[k] 1), ?_⟩
    rw [map_smul, TensorProduct.map_tmul]
    change c • ((1 : GroupAlgebra k) ⊗ₜ[k] 1) =
      Coalgebra.comul (R := k) (s : GroupAlgebra k)
    rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul,
      Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  · intro s
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp s.property
    rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (⊥ : Subalgebra k (GroupAlgebra k)).algebraMap_mem c

private theorem scalar_bottom_factorization (k : Type u) [Field k] :
    let S := (⊥ : Subalgebra k (GroupAlgebra k))
    ∃ h : S.IsHopfSubalgebra,
      generator k ∉ S ∧
      (S.hopfAlgebra h).toBialgebra.toAlgebra = (inferInstance : Algebra k S) ∧
      @Algebra.toModule k S _ _ (S.hopfAlgebra h).toBialgebra.toAlgebra =
        (inferInstance : Module k S) ∧
      (S.hopfAlgebra h).toBialgebra.toCoalgebra =
        S.coalgebraOfComulMem h.comul_mem ∧
      (∃ g : @BialgHom k k S
          (inferInstance : CommSemiring k)
          (inferInstance : Semiring k) (inferInstance : Algebra k k)
          (inferInstance : Semiring S) (inferInstance : Algebra k S)
          (inferInstance : CoalgebraStruct k k)
          (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct,
        @BialgHom.comp k k S (GroupAlgebra k)
          (inferInstance : CommSemiring k)
          (inferInstance : Semiring k) (inferInstance : Semiring S)
          (inferInstance : Semiring (GroupAlgebra k))
          (inferInstance : Algebra k k) (inferInstance : Algebra k S)
          (inferInstance : Algebra k (GroupAlgebra k))
          (inferInstance : CoalgebraStruct k k)
          (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
          (inferInstance : CoalgebraStruct k (GroupAlgebra k))
          (S.inclusionBialgHom h) g =
          Bialgebra.unitBialgHom k (GroupAlgebra k)) := by
  let S : Subalgebra k (GroupAlgebra k) := ⊥
  have h : S.IsHopfSubalgebra :=
    ⟨(scalar_bottom_inputs k).1, (scalar_bottom_inputs k).2⟩
  refine ⟨h, generator_not_mem_scalar_bottom k, S.hopfAlgebra_toAlgebra h,
    S.hopfAlgebra_toModule h, S.hopfAlgebra_toCoalgebra h, ?_⟩
  let f : k →ₐc[k] GroupAlgebra k := Bialgebra.unitBialgHom k (GroupAlgebra k)
  have hf : f.toAlgHom.range ≤ S := by
    rintro _ ⟨c, rfl⟩
    change algebraMap k (GroupAlgebra k) c ∈ S
    exact S.algebraMap_mem c
  exact ⟨S.corestrict h f hf, S.inclusionBialgHom_comp_corestrict h f hf⟩

private theorem zero_boundary (k : Type u) [Field k] :
    Coalgebra.comul (R := k) (0 : GroupAlgebra k) =
        (0 : GroupAlgebra k) ⊗ₜ[k] (0 : GroupAlgebra k) ∧
      ¬ IsUnit (Coalgebra.counit (R := k) (0 : GroupAlgebra k)) ∧
      ¬ IsGroupLikeElem k (0 : GroupAlgebra k) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_zero, TensorProduct.zero_tmul]
  · simpa only [map_zero] using (not_isUnit_zero : ¬ IsUnit (0 : k))
  · intro h
    exact h.ne_zero rfl
