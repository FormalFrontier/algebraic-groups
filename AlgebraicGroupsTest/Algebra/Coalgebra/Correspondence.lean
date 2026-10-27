/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.CoidealCorrespondence
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Data.ZMod.Basic

/-!
# Integer group-algebra parity and coideal correspondence

The stock bialgebra map induced by reduction of integers modulo two has a
nonzero kernel strictly below the source augmentation coideal. The coideal
correspondence sends these two points to zero and the nonzero proper target
augmentation coideal, respectively. Its inverse recovers both points.

All carriers, coalgebras and the bialgebra homomorphism are Mathlib's canonical
ones. Coefficients are accessed through the group-algebra wrapper, not through
a definitional identification with finitely supported functions.

## References

Mathlib's monoid-algebra coalgebra and bialgebra formalizations supply the
structures and the induced map. Its finitely supported function and modular
integer APIs supply surjectivity of the coefficient-domain map.
-/

@[expose] public section

noncomputable section

namespace AddMonoidAlgebra

private abbrev C := AddMonoidAlgebra ℤ ℤ
private abbrev D := AddMonoidAlgebra ℤ (ZMod 2)

private def parityMap : C →ₐc[ℤ] D :=
  AddMonoidAlgebra.mapDomainBialgHom ℤ (Int.castAddHom (ZMod 2))

private theorem parityMap_surjective : Function.Surjective parityMap := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := ℤ)
    (ZMod.intCast_surjective (n := 2)) y.coeff
  refine ⟨AddMonoidAlgebra.ofCoeff x, ?_⟩
  apply (AddMonoidAlgebra.coeffLinearEquiv ℤ).injective
  exact hx

private def parityKernel : Submodule ℤ C := (parityMap : C →ₗ[ℤ] D).ker
private def sourceAugmentation : Submodule ℤ C :=
  (Coalgebra.counit : C →ₗ[ℤ] ℤ).ker
private def targetAugmentation : Submodule ℤ D :=
  (Coalgebra.counit : D →ₗ[ℤ] ℤ).ker

private theorem parityKernel_isCoideal : parityKernel.IsCoideal := by
  exact CoalgHomClass.ker_isCoideal_of_surjective parityMap parityMap_surjective

private theorem sourceAugmentation_isCoideal : sourceAugmentation.IsCoideal := by
  apply CoalgHomClass.ker_isCoideal_of_surjective (Coalgebra.counitCoalgHom ℤ C)
  intro r
  refine ⟨single (0 : ℤ) r, ?_⟩
  change Coalgebra.counit (R := ℤ) (single (0 : ℤ) r : C) = r
  rw [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]

private theorem targetAugmentation_isCoideal : targetAugmentation.IsCoideal := by
  apply CoalgHomClass.ker_isCoideal_of_surjective (Coalgebra.counitCoalgHom ℤ D)
  intro r
  refine ⟨single (0 : ZMod 2) r, ?_⟩
  simp

private theorem parityKernel_le_sourceAugmentation :
    parityKernel ≤ sourceAugmentation := by
  intro x hx
  change Coalgebra.counit (R := ℤ) x = 0
  have hx' : parityMap x = 0 := hx
  rw [← CoalgHomClass.counit_comp_apply parityMap x, hx', map_zero]

private theorem targetZero_isCoideal : (⊥ : Submodule ℤ D).IsCoideal where
  counit_eq_zero := by
    intro x hx
    have hx' : x = 0 := by simpa only [Submodule.mem_bot] using hx
    subst x
    simp
  map_mkQ_comul_eq_zero := by
    intro x hx
    have hx' : x = 0 := by simpa only [Submodule.mem_bot] using hx
    subst x
    simp

private def kernelPoint :
    {I : Submodule ℤ C // I.IsCoideal ∧ (parityMap : C →ₗ[ℤ] D).ker ≤ I} :=
  ⟨parityKernel, parityKernel_isCoideal, le_rfl⟩

private def augmentationPoint :
    {I : Submodule ℤ C // I.IsCoideal ∧ (parityMap : C →ₗ[ℤ] D).ker ≤ I} :=
  ⟨sourceAugmentation, sourceAugmentation_isCoideal, parityKernel_le_sourceAugmentation⟩

private def zeroPoint : {J : Submodule ℤ D // J.IsCoideal} :=
  ⟨⊥, targetZero_isCoideal⟩

private def targetAugmentationPoint : {J : Submodule ℤ D // J.IsCoideal} :=
  ⟨targetAugmentation, targetAugmentation_isCoideal⟩

private def correspondence :=
  Submodule.coidealOrderIsoOfSurjective parityMap parityMap_surjective

private theorem correspondence_apply_val
    (I : {I : Submodule ℤ C // I.IsCoideal ∧ (parityMap : C →ₗ[ℤ] D).ker ≤ I}) :
    (correspondence I).val = I.val.map (parityMap : C →ₗ[ℤ] D) := by
  simpa only [correspondence] using
    (Submodule.coidealOrderIsoOfSurjective_apply_val parityMap parityMap_surjective I)

private theorem correspondence_symm_apply_val
    (J : {J : Submodule ℤ D // J.IsCoideal}) :
    (correspondence.symm J).val = J.val.comap (parityMap : C →ₗ[ℤ] D) := by
  simpa only [correspondence] using
    (Submodule.coidealOrderIsoOfSurjective_symm_apply_val parityMap parityMap_surjective J)

private theorem even_difference :
    (single (2 : ℤ) 1 - single (0 : ℤ) 1 : C) ≠ 0 ∧
      (single (2 : ℤ) 1 - single (0 : ℤ) 1 : C) ∈ parityKernel := by
  constructor
  · intro h
    have hne : (0 : ℤ) ≠ 2 := by decide
    have hc := congrArg (fun x : C => x.coeff (2 : ℤ)) h
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero] at hc
    have hz : (1 : ℤ) = 0 := by
      simpa only [Finsupp.sub_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne' hne, Finsupp.zero_apply, sub_zero] using hc
    exact one_ne_zero hz
  · change AddMonoidAlgebra.mapDomainBialgHom ℤ (Int.castAddHom (ZMod 2))
      (single (2 : ℤ) 1 - single (0 : ℤ) 1) = 0
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [map_sub, AddMonoidAlgebra.mapDomainBialgHom_single,
      AddMonoidAlgebra.mapDomainBialgHom_single]
    simp only [Int.coe_castAddHom, Int.cast_ofNat, Int.cast_zero, htwo, sub_self]

private theorem odd_difference :
    (single (1 : ℤ) 1 - single (0 : ℤ) 1 : C) ∈ sourceAugmentation ∧
      (single (1 : ℤ) 1 - single (0 : ℤ) 1 : C) ∉ parityKernel := by
  constructor
  · change Coalgebra.counit (R := ℤ) (single (1 : ℤ) 1 - single (0 : ℤ) 1 : C) = 0
    simp
  · intro hx
    have hx' : parityMap (single (1 : ℤ) 1 - single (0 : ℤ) 1) = 0 := hx
    change AddMonoidAlgebra.mapDomainBialgHom ℤ (Int.castAddHom (ZMod 2))
      (single (1 : ℤ) 1 - single (0 : ℤ) 1) = 0 at hx'
    rw [map_sub, AddMonoidAlgebra.mapDomainBialgHom_single,
      AddMonoidAlgebra.mapDomainBialgHom_single] at hx'
    simp only [Int.coe_castAddHom, Int.cast_one, Int.cast_zero] at hx'
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    have hc := congrArg (fun y : D => y.coeff (1 : ZMod 2)) hx'
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero] at hc
    have hz : (1 : ℤ) = 0 := by
      simpa only [Finsupp.sub_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne' hne, Finsupp.zero_apply, sub_zero] using hc
    exact one_ne_zero hz

private theorem target_difference :
    (single (1 : ZMod 2) 1 - single (0 : ZMod 2) 1 : D) ≠ 0 ∧
      (single (1 : ZMod 2) 1 - single (0 : ZMod 2) 1 : D) ∈ targetAugmentation := by
  constructor
  · intro h
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    simpa [hne] using congrArg (fun y : D => y.coeff (1 : ZMod 2)) h
  · change Coalgebra.counit (R := ℤ)
      (single (1 : ZMod 2) 1 - single (0 : ZMod 2) 1 : D) = 0
    simp

private theorem augmentation_proper_witnesses :
    (single (0 : ℤ) 1 : C) ∉ sourceAugmentation ∧
      (single (0 : ZMod 2) 1 : D) ∉ targetAugmentation := by
  constructor
  · change ¬ Coalgebra.counit (R := ℤ) (single (0 : ℤ) 1 : C) = 0
    simp
  · change ¬ Coalgebra.counit (R := ℤ) (single (0 : ZMod 2) 1 : D) = 0
    simp

private theorem strict_chains :
    (⊥ : Submodule ℤ C) < parityKernel ∧
      parityKernel < sourceAugmentation ∧ sourceAugmentation < ⊤ ∧
      (⊥ : Submodule ℤ D) < targetAugmentation ∧ targetAugmentation < ⊤ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_not_ge bot_le ?_
    intro h
    exact even_difference.1 ((Submodule.mem_bot ℤ).mp (h even_difference.2))
  · refine lt_of_le_not_ge parityKernel_le_sourceAugmentation ?_
    intro h
    exact odd_difference.2 (h odd_difference.1)
  · refine lt_of_le_not_ge le_top ?_
    intro h
    exact augmentation_proper_witnesses.1 (h Submodule.mem_top)
  · refine lt_of_le_not_ge bot_le ?_
    intro h
    exact target_difference.1 ((Submodule.mem_bot ℤ).mp (h target_difference.2))
  · refine lt_of_le_not_ge le_top ?_
    intro h
    exact augmentation_proper_witnesses.2 (h Submodule.mem_top)

private theorem correspondence_kernel : correspondence kernelPoint = zeroPoint := by
  apply Subtype.ext
  rw [correspondence_apply_val]
  change parityKernel.map (parityMap : C →ₗ[ℤ] D) = ⊥
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (Submodule.mem_bot ℤ).mpr hx
  · exact bot_le

private theorem correspondence_augmentation :
    correspondence augmentationPoint = targetAugmentationPoint := by
  apply Subtype.ext
  rw [correspondence_apply_val]
  change sourceAugmentation.map (parityMap : C →ₗ[ℤ] D) = targetAugmentation
  have hcomap : targetAugmentation.comap (parityMap : C →ₗ[ℤ] D) =
      sourceAugmentation := by
    apply Submodule.ext
    intro x
    change Coalgebra.counit (R := ℤ) (parityMap x) = 0 ↔
      Coalgebra.counit (R := ℤ) x = 0
    rw [CoalgHomClass.counit_comp_apply parityMap x]
  rw [← hcomap]
  exact Submodule.map_comap_eq_of_surjective parityMap_surjective targetAugmentation

private theorem correspondence_symm_zero : correspondence.symm zeroPoint = kernelPoint := by
  rw [← correspondence_kernel]
  exact correspondence.symm_apply_apply kernelPoint

private theorem correspondence_symm_targetAugmentation :
    correspondence.symm targetAugmentationPoint = augmentationPoint := by
  rw [← correspondence_augmentation]
  exact correspondence.symm_apply_apply augmentationPoint

private theorem zeroPoint_lt_targetAugmentationPoint : zeroPoint < targetAugmentationPoint := by
  rw [← correspondence_kernel, ← correspondence_augmentation]
  exact correspondence.strictMono
    (show kernelPoint < augmentationPoint from strict_chains.2.1)

private theorem mem_correspondence_augmentation_iff (y : D) :
    y ∈ (correspondence augmentationPoint).val ↔
    ∃ x, x ∈ sourceAugmentation ∧ parityMap x = y := by
  rw [correspondence_apply_val]
  exact Submodule.mem_map

private theorem mem_correspondence_symm_targetAugmentation_iff (x : C) :
    x ∈ (correspondence.symm targetAugmentationPoint).val ↔
    parityMap x ∈ targetAugmentation := by
  rw [correspondence_symm_apply_val]
  rfl

end AddMonoidAlgebra
