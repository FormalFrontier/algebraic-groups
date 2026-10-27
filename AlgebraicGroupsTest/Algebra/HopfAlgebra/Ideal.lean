/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.HopfAlgebra.Ideal
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The augmentation ideal of the infinite cyclic group algebra

Over every field `k`, the group algebra `MonoidAlgebra k (Multiplicative ℤ)`
and the scalar target carry Mathlib's full Hopf structures. The map is the
bundled counit `Bialgebra.counitBialgHom`, with no change of algebra or coalgebra
structure. Its ordinary ring kernel is a proper nonzero ideal: the difference
between the weight-one basis vector and the unit is a nonzero member, whereas
the unit is not a member. The weight-one coefficient distinguishes these
vectors in every characteristic.

The four Hopf-ideal propositions concern this same augmentation map, using
the kernel and the inverse image of the scalar bottom ideal. Coideality and
the Hopf-ideal property of the bottom ideal are separate propositions, not
additional algebraic structures or installed instances.
-/

noncomputable section

namespace HopfIdealExamples

universe u

private abbrev WeightAlgebra (k : Type u) [Field k] :=
  MonoidAlgebra k (Multiplicative ℤ)

private abbrev augmentationIdeal (k : Type u) [Field k] : Ideal (WeightAlgebra k) :=
  RingHom.ker (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom

variable {k : Type u} [Field k]

/-- The weight-one basis vector differs from the unit in every characteristic. -/
private theorem augmentation_generator_sub_one_ne_zero :
    (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k) : WeightAlgebra k) - 1 ≠
      0 := by
  intro h
  have hcoeff := congrArg
    (fun x : WeightAlgebra k => x.coeff (Multiplicative.ofAdd (1 : ℤ))) h
  apply one_ne_zero (α := k)
  simp [MonoidAlgebra.one_def] at hcoeff

/-- The difference between the weight-one basis vector and the unit lies in the
ordinary augmentation kernel. -/
private theorem augmentation_generator_sub_one_mem :
    (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k) : WeightAlgebra k) - 1 ∈
      augmentationIdeal k := by
  apply RingHom.mem_ker.mpr
  change (Bialgebra.counitBialgHom k (WeightAlgebra k))
    ((MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k) : WeightAlgebra k) - 1) = 0
  simp only [map_sub, map_one, Bialgebra.counitBialgHom_apply,
    MonoidAlgebra.counit_single, Bialgebra.counit_one, sub_self]

/-- The unit does not lie in the ordinary augmentation kernel. -/
private theorem augmentation_one_not_mem :
    (1 : WeightAlgebra k) ∉ augmentationIdeal k := by
  exact RingHom.one_notMem_ker
    (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom

/-- The ordinary augmentation ideal is nonzero. -/
private theorem augmentationIdeal_ne_bot : augmentationIdeal k ≠ ⊥ := by
  intro hbot
  apply augmentation_generator_sub_one_ne_zero (k := k)
  have hmem := augmentation_generator_sub_one_mem (k := k)
  rw [hbot] at hmem
  simpa only [Submodule.mem_bot] using hmem

/-- The ordinary augmentation ideal is proper. -/
private theorem augmentationIdeal_ne_top : augmentationIdeal k ≠ ⊤ := by
  intro htop
  apply augmentation_one_not_mem (k := k)
  simp only [htop, Submodule.mem_top]

/-- The bottom ideal of the scalar Hopf algebra has the Hopf-ideal property. -/
private theorem scalar_bot_isHopfIdeal :
    Ideal.IsHopfIdeal k (⊥ : Ideal k) := by
  refine { toIsCoideal := ?_, antipode_mem := ?_ }
  · constructor
    · intro x hx
      have hx0 : x = 0 := by
        simpa only [Submodule.restrictScalars_mem, Submodule.mem_bot] using hx
      simp only [hx0, map_zero]
    · intro x hx
      have hx0 : x = 0 := by
        simpa only [Submodule.restrictScalars_mem, Submodule.mem_bot] using hx
      simp only [hx0, map_zero]
  · intro x hx
    have hx0 : x = 0 := by
      simpa only [Submodule.mem_bot] using hx
    simp only [hx0, map_zero, Submodule.mem_bot]

/-- The scalar restriction of the ordinary augmentation kernel is a coideal. -/
private theorem augmentationIdeal_isCoideal :
    ((augmentationIdeal k).restrictScalars k).IsCoideal := by
  have hker :
      LinearMap.ker
          (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toLinearMap =
        (augmentationIdeal k).restrictScalars k := by
    apply Submodule.ext
    intro x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, augmentationIdeal,
      RingHom.mem_ker]
    rfl
  rw [← hker]
  exact CoalgHomClass.ker_isCoideal
    (Bialgebra.counitBialgHom k (WeightAlgebra k)).toCoalgHom

/-- The preimage of the scalar bottom ideal is the ordinary augmentation ideal. -/
private theorem augmentation_comap_eq_augmentationIdeal :
    (⊥ : Ideal k).comap
        (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom =
      augmentationIdeal k := by
  exact (RingHom.ker_eq_comap_bot
    (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom).symm

/-- The conditional kernel theorem certifies the augmentation ideal using its
coideality. -/
private theorem augmentation_conditional_kernel :
    Ideal.IsHopfIdeal k (augmentationIdeal k) := by
  exact BialgHom.ker_isHopfIdeal_of_isCoideal
    (Bialgebra.counitBialgHom k (WeightAlgebra k))
    (augmentationIdeal_isCoideal (k := k))

/-- The field kernel theorem certifies the augmentation ideal without a
coideality hypothesis. -/
private theorem augmentation_field_kernel :
    Ideal.IsHopfIdeal k (augmentationIdeal k) := by
  exact BialgHom.ker_isHopfIdeal (Bialgebra.counitBialgHom k (WeightAlgebra k))

/-- The conditional inverse-image theorem certifies the preimage of the scalar
bottom ideal under augmentation, using the coideality of this preimage. -/
private theorem augmentation_conditional_comap :
    Ideal.IsHopfIdeal k ((⊥ : Ideal k).comap
      (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom) := by
  apply Ideal.IsHopfIdeal.comap_of_isCoideal
    (scalar_bot_isHopfIdeal (k := k))
    (Bialgebra.counitBialgHom k (WeightAlgebra k))
  rw [augmentation_comap_eq_augmentationIdeal]
  exact augmentationIdeal_isCoideal (k := k)

/-- The field inverse-image theorem certifies the preimage of the scalar bottom
ideal under augmentation without a coideality hypothesis. -/
private theorem augmentation_field_comap :
    Ideal.IsHopfIdeal k ((⊥ : Ideal k).comap
      (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom) := by
  exact Ideal.IsHopfIdeal.comap (scalar_bot_isHopfIdeal (k := k))
    (Bialgebra.counitBialgHom k (WeightAlgebra k))

end HopfIdealExamples
