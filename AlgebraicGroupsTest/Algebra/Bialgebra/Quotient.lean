/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Bialgebra.Quotient
import AlgebraicGroups.Algebra.Coalgebra.Quotient
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Augmentation ideals and the zero-ideal boundary

For a field `k`, consider the monoid bialgebra on `Multiplicative ℕ`. Write
`t = MonoidAlgebra.single (Multiplicative.ofAdd 1) 1`; its counit is `1` and
its comultiplication is `t ⊗ t`. The ordinary ring kernel of the counit is the
augmentation ideal. Nonvacuity requires this ideal to be nonzero and proper,
its scalar restriction to be a coideal, and the class of `1` to survive in
the ordinary ideal quotient. The difference `t - 1` records the nonzero
kernel element and the identification of `t` with `1` in that quotient.

The zero-ideal boundary compares the ordinary algebra lift of the identity
with `AlgEquiv.quotientBot`, rather than identifying the two carriers.

## Implementation notes

All ring, algebra and bialgebra structures are Mathlib's. The augmentation
ideal is only an ordinary ring kernel. Coideality occurs as a proposition,
not as an instance used to construct quotient bialgebra data.

## References

Mathlib's `Mathlib.RingTheory.Bialgebra.MonoidAlgebra` supplies the monoid
bialgebra, and `Mathlib.RingTheory.Bialgebra.Hom` supplies its counit as a
bialgebra morphism. `CoalgHomClass.ker_isCoideal` from
`AlgebraicGroups.Algebra.Coalgebra.Quotient` applies to linear kernels over a
field; relating that linear kernel to the scalar-restricted ring kernel is
part of the coideality assertion below. The ordinary quotient, algebra lift
and zero-ideal equivalence are from Mathlib's ideal quotient API.
-/

@[expose] public section

noncomputable section

universe u

namespace MonoidAlgebra.AugmentationQuotient

/-- The monoid algebra on the multiplicative tag of the additive monoid `ℕ`. -/
private abbrev WeightAlgebra (k : Type u) [Semiring k] := MonoidAlgebra k (Multiplicative ℕ)

/-- The ordinary ring kernel of the counit of the monoid bialgebra. -/
private abbrev augmentationIdeal (k : Type u) [Field k] : Ideal (WeightAlgebra k) :=
  RingHom.ker
    ((Bialgebra.counitBialgHom k (WeightAlgebra k) : WeightAlgebra k →ₐ[k] k).toRingHom)

/-- The augmentation ideal is nonzero, proper and scalar-restricted coideal;
the ordinary quotient has a surviving unit and kills the nonzero element `t - 1`. -/
private theorem augmentationIdeal_properties (k : Type u) [Field k] :
    augmentationIdeal k ≠ ⊥ ∧
      augmentationIdeal k ≠ ⊤ ∧
      ((augmentationIdeal k).restrictScalars k).IsCoideal ∧
      Ideal.Quotient.mk (augmentationIdeal k) (1 : WeightAlgebra k) ≠ 0 ∧
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 - (1 : WeightAlgebra k)) ≠ 0 ∧
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 - (1 : WeightAlgebra k)) ∈
        augmentationIdeal k ∧
      Ideal.Quotient.mk (augmentationIdeal k)
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
        Ideal.Quotient.mk (augmentationIdeal k) (1 : WeightAlgebra k) := by
  classical
  have hindex : (Multiplicative.ofAdd 1 : Multiplicative ℕ) ≠ 1 := by simp
  have hnonzero :
      MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 - (1 : WeightAlgebra k) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun a : WeightAlgebra k => a.coeff (Multiplicative.ofAdd 1)) h
    simpa [MonoidAlgebra.one_def, Finsupp.single_apply, Ne.symm hindex] using hcoeff
  have hmem :
      MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 - (1 : WeightAlgebra k) ∈
        augmentationIdeal k := by
    apply RingHom.mem_ker.mpr
    change Bialgebra.counitBialgHom k (WeightAlgebra k)
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 - 1) = 0
    rw [map_sub, map_one (Bialgebra.counitBialgHom k (WeightAlgebra k)),
      Bialgebra.counitBialgHom_apply, MonoidAlgebra.counit_single,
      CommSemiring.counit_apply, sub_self]
  have hone : (1 : WeightAlgebra k) ∉ augmentationIdeal k :=
    RingHom.one_notMem_ker
      ((Bialgebra.counitBialgHom k (WeightAlgebra k) : WeightAlgebra k →ₐ[k] k).toRingHom)
  have hker : (augmentationIdeal k).restrictScalars k =
      LinearMap.ker
        (Bialgebra.counitBialgHom k (WeightAlgebra k)).toCoalgHom.toLinearMap := by
    ext a
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact RingHom.mem_ker
  have hcoideal : ((augmentationIdeal k).restrictScalars k).IsCoideal := by
    rw [hker]
    simpa only [CoalgHom.toLinearMap_eq_coe] using
      CoalgHomClass.ker_isCoideal (Bialgebra.counitBialgHom k (WeightAlgebra k)).toCoalgHom
  refine ⟨?_, (Ideal.ne_top_iff_one _).mpr hone, hcoideal, ?_, hnonzero, hmem, ?_⟩
  · intro hbot
    exact hnonzero (Ideal.mem_bot.mp (hbot ▸ hmem))
  · intro hzero
    exact hone (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem

/-- At the zero ideal, the algebra lift of the identity agrees with the
canonical algebra equivalence from the quotient by zero. -/
private theorem lift_id_bot_eq_quotientBot (k : Type u) [Field k] :
    Ideal.Quotient.liftₐ (⊥ : Ideal (WeightAlgebra k)) (AlgHom.id k (WeightAlgebra k))
        (fun _ ha => by
          simpa only [AlgHom.id_apply] using (Ideal.mem_bot.mp ha)) =
      (AlgEquiv.quotientBot k (WeightAlgebra k)).toAlgHom := by
  apply Ideal.Quotient.algHom_ext k
  rw [Ideal.Quotient.liftₐ_comp]
  apply AlgHom.ext
  intro a
  simp only [AlgHom.id_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.quotientBot_mk]

end MonoidAlgebra.AugmentationQuotient
