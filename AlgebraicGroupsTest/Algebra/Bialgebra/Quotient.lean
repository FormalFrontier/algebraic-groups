/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Bialgebra.Quotient
import AlgebraicGroups.Algebra.Coalgebra.Quotient
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Augmentation quotient factorization and the zero-ideal boundary

For a field `k`, consider the monoid bialgebra on `Multiplicative ℕ`. Write
`t = MonoidAlgebra.single (Multiplicative.ofAdd 1) 1`; its counit is `1` and
its comultiplication is `t ⊗ t`. The ordinary ring kernel of the counit is the
augmentation ideal. Nonvacuity requires this ideal to be nonzero and proper,
its scalar restriction to be a coideal, and the class of `1` to survive in
the ordinary ideal quotient. The difference `t - 1` records the nonzero
kernel element and the identification of `t` with `1` in that quotient.

The quotient bialgebra uses this coideal certificate locally. Its counit is
an independent factor of the original counit through the quotient projection.
The factorization client compares the induced bialgebra morphism with that
counit, including evaluation on `t - 1`, the surviving unit and the generator.
The zero-ideal boundary compares the induced morphism's underlying algebra
map with `AlgEquiv.quotientBot`, rather than identifying the two carriers.

## Implementation notes

All ring, algebra and bialgebra structures are Mathlib's. The augmentation
ideal is an ordinary ring kernel. Its proved coideal certificate is installed
only locally; the quotient, projection and quotient counit then use the
canonical ideal-quotient bialgebra structure. No bialgebra structure is
transported from an equivalence with the field.

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
    simp [MonoidAlgebra.one_def] at hcoeff
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
    simpa only [CoalgHom.toLinearMap_eq_ofClass] using
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


namespace MonoidAlgebra.AugmentationQuotient

/-- The coideal certificate for the augmentation ideal. -/
private theorem augmentationIdeal_isCoideal (k : Type u) [Field k] :
    ((augmentationIdeal k).restrictScalars k).IsCoideal :=
  (MonoidAlgebra.AugmentationQuotient.augmentationIdeal_properties k).2.2.1

attribute [local instance] augmentationIdeal_isCoideal

/-- The canonical projection to the augmentation quotient bialgebra. -/
private abbrev augmentationProjection (k : Type u) [Field k] :
    WeightAlgebra k →ₐc[k] (WeightAlgebra k ⧸ augmentationIdeal k) :=
  Bialgebra.Quotient.mkBialgHom (R := k) (augmentationIdeal k)

/-- The counit of the augmentation quotient, independently of quotient lifting. -/
private abbrev augmentationCounitFactor (k : Type u) [Field k] :
    (WeightAlgebra k ⧸ augmentationIdeal k) →ₐc[k] k :=
  Bialgebra.counitBialgHom k (WeightAlgebra k ⧸ augmentationIdeal k)

/-- The quotient counit factors the original counit by preservation of counits
under the quotient projection. -/
private theorem augmentationCounitFactor_comp (k : Type u) [Field k] :
    (augmentationCounitFactor k).comp (augmentationProjection k) =
      Bialgebra.counitBialgHom k (WeightAlgebra k) := by
  apply BialgHom.coe_toAlgHom_injective
  change (Bialgebra.counitAlgHom k (WeightAlgebra k ⧸ augmentationIdeal k)).comp
      (augmentationProjection k).toAlgHom = Bialgebra.counitAlgHom k (WeightAlgebra k)
  exact BialgHom.counitAlgHom_comp (augmentationProjection k)

/-- The ordinary algebra lift of the counit through its ring kernel. -/
private abbrev augmentationAlgLift (k : Type u) [Field k] :
    (WeightAlgebra k ⧸ augmentationIdeal k) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (augmentationIdeal k)
    (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom
    (fun _a ha => RingHom.mem_ker.mp ((le_refl (augmentationIdeal k)) ha))

/-- Counit preservation of the ordinary algebra lift in the augmentation quotient. -/
private theorem augmentationAlgLift_counit (k : Type u) [Field k] :
    (Bialgebra.counitAlgHom k k).comp (augmentationAlgLift k) =
      Bialgebra.counitAlgHom k (WeightAlgebra k ⧸ augmentationIdeal k) := by
  exact Bialgebra.Quotient.counitAlgHom_comp_liftₐ (augmentationIdeal k)
    (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))

/-- Comultiplication preservation of the same ordinary algebra lift. -/
private theorem augmentationAlgLift_comul (k : Type u) [Field k] :
    (Algebra.TensorProduct.map (augmentationAlgLift k) (augmentationAlgLift k)).comp
        (Bialgebra.comulAlgHom k (WeightAlgebra k ⧸ augmentationIdeal k)) =
      (Bialgebra.comulAlgHom k k).comp (augmentationAlgLift k) := by
  exact Bialgebra.Quotient.map_liftₐ_comp_comulAlgHom (augmentationIdeal k)
    (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))

/-- The induced bialgebra lift of the original counit. -/
private abbrev augmentationBialgLift (k : Type u) [Field k] :
    (WeightAlgebra k ⧸ augmentationIdeal k) →ₐc[k] k :=
  Bialgebra.Quotient.liftBialgHom (augmentationIdeal k)
    (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))

/-- Factorization through the proper nonzero augmentation quotient, including
its algebra lift, representatives and comparison with the quotient counit. -/
private theorem augmentation_lift_client (k : Type u) [Field k] :
    let t : WeightAlgebra k := MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
    let z := t - 1
    augmentationIdeal k ≠ ⊥ ∧
      augmentationIdeal k ≠ ⊤ ∧
      z ≠ 0 ∧ z ∈ augmentationIdeal k ∧
      Ideal.Quotient.mk (augmentationIdeal k) (1 : WeightAlgebra k) ≠ 0 ∧
      Ideal.Quotient.mk (augmentationIdeal k) t =
        Ideal.Quotient.mk (augmentationIdeal k) (1 : WeightAlgebra k) ∧
      (Bialgebra.counitAlgHom k k).comp (augmentationAlgLift k) =
        Bialgebra.counitAlgHom k (WeightAlgebra k ⧸ augmentationIdeal k) ∧
      (Algebra.TensorProduct.map (augmentationAlgLift k) (augmentationAlgLift k)).comp
          (Bialgebra.comulAlgHom k (WeightAlgebra k ⧸ augmentationIdeal k)) =
        (Bialgebra.comulAlgHom k k).comp (augmentationAlgLift k) ∧
      (augmentationBialgLift k).toAlgHom = augmentationAlgLift k ∧
      augmentationBialgLift k (Ideal.Quotient.mk (augmentationIdeal k) z) = 0 ∧
      augmentationBialgLift k
          (Ideal.Quotient.mk (augmentationIdeal k) (1 : WeightAlgebra k)) = 1 ∧
      augmentationBialgLift k (Ideal.Quotient.mk (augmentationIdeal k) t) = 1 ∧
      (augmentationBialgLift k).comp (augmentationProjection k) =
        Bialgebra.counitBialgHom k (WeightAlgebra k) ∧
      (∀ g h : (WeightAlgebra k ⧸ augmentationIdeal k) →ₐc[k] k,
        g.comp (augmentationProjection k) = h.comp (augmentationProjection k) → g = h) ∧
      (∀ g : (WeightAlgebra k ⧸ augmentationIdeal k) →ₐc[k] k,
        g.comp (augmentationProjection k) = Bialgebra.counitBialgHom k (WeightAlgebra k) →
          g = augmentationBialgLift k) ∧
      (∃! g : (WeightAlgebra k ⧸ augmentationIdeal k) →ₐc[k] k,
        g.comp (augmentationProjection k) = Bialgebra.counitBialgHom k (WeightAlgebra k)) ∧
      augmentationBialgLift k = augmentationCounitFactor k := by
  dsimp only
  obtain ⟨hbot, htop, _, hone, hz, hzmem, ht⟩ :=
    MonoidAlgebra.AugmentationQuotient.augmentationIdeal_properties k
  refine ⟨hbot, htop, hz, hzmem, hone, ht,
    augmentationAlgLift_counit k, augmentationAlgLift_comul k,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Bialgebra.Quotient.liftBialgHom_toAlgHom (augmentationIdeal k)
      (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))
  · rw [Bialgebra.Quotient.liftBialgHom_mk]
    exact RingHom.mem_ker.mp hzmem
  · rw [Bialgebra.Quotient.liftBialgHom_mk, map_one]
  · rw [Bialgebra.Quotient.liftBialgHom_mk, Bialgebra.counitBialgHom_apply,
      MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · exact Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom (augmentationIdeal k)
      (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))
  · intro g h hcomp
    exact Bialgebra.Quotient.hom_ext (augmentationIdeal k) g h hcomp
  · intro g hg
    exact Bialgebra.Quotient.liftBialgHom_unique (augmentationIdeal k)
      (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k)) g hg
  · exact Bialgebra.Quotient.existsUnique_liftBialgHom (augmentationIdeal k)
      (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))
  · exact (Bialgebra.Quotient.liftBialgHom_unique (augmentationIdeal k)
      (Bialgebra.counitBialgHom k (WeightAlgebra k)) (le_refl (augmentationIdeal k))
      (augmentationCounitFactor k) (augmentationCounitFactor_comp k)).symm

/-- The zero ideal has a scalar-restricted coideal certificate. -/
private theorem botIdeal_isCoideal (k : Type u) [Field k] :
    ((⊥ : Ideal (WeightAlgebra k)).restrictScalars k).IsCoideal := by
  constructor
  · intro x hx
    have hxzero : x = 0 := Ideal.mem_bot.mp hx
    simp only [hxzero, map_zero]
  · intro x hx
    have hxzero : x = 0 := Ideal.mem_bot.mp hx
    simp only [hxzero, map_zero]

attribute [local instance] botIdeal_isCoideal

/-- The identity factor at the zero ideal has the underlying algebra map of
the canonical quotient-by-zero equivalence. -/
private theorem liftBialgHom_bot_client (k : Type u) [Field k] :
    (Bialgebra.Quotient.liftBialgHom (⊥ : Ideal (WeightAlgebra k))
        (BialgHom.id k (WeightAlgebra k)) bot_le).toAlgHom =
      (AlgEquiv.quotientBot k (WeightAlgebra k)).toAlgHom := by
  rw [Bialgebra.Quotient.liftBialgHom_toAlgHom]
  simpa only [BialgHom.id_toAlgHom] using
    MonoidAlgebra.AugmentationQuotient.lift_id_bot_eq_quotientBot k

end MonoidAlgebra.AugmentationQuotient
