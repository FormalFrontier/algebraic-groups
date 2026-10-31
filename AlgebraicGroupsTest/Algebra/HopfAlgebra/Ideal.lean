/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.HopfAlgebra.Ideal
import AlgebraicGroups.Algebra.HopfAlgebra.Range
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

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

attribute [local instance] augmentation_field_kernel
attribute [local instance 50] augmentationIdeal_isCoideal

section

local instance augmentationRangeHopfAlgebra :
    HopfAlgebra k (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.range :=
  (Bialgebra.counitBialgHom k (WeightAlgebra k)).rangeHopfAlgebra

/-- On this same group-algebra counit, the first-isomorphism equivalence kills
`t - 1` and identifies `t` with the unit, while the quotient unit survives.
Both factor triangles hold, and the inclusion after equivalence is also the
independently given counit of this very quotient, by quotient-factor uniqueness. -/
example :
    let f := Bialgebra.counitBialgHom k (WeightAlgebra k)
    let t : WeightAlgebra k := MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1
    let q := Bialgebra.Quotient.mkBialgHom (R := k) (augmentationIdeal k)
    let E : (WeightAlgebra k ⧸ augmentationIdeal k) ≃ₐc[k] f.toAlgHom.range :=
      f.quotientKerEquivRange
    let p := f.rangeRestrict
    let i := f.rangeInclusion
    t - 1 ≠ 0 ∧ q 1 ≠ 0 ∧ E (q (t - 1)) = 0 ∧ E (q t) = p 1 ∧
      E.toBialgHom.comp q = p ∧
      i.comp E.toBialgHom =
        Bialgebra.Quotient.liftBialgHom (augmentationIdeal k) f le_rfl ∧
      i.comp E.toBialgHom =
        Bialgebra.counitBialgHom k (WeightAlgebra k ⧸ augmentationIdeal k) := by
  let f := Bialgebra.counitBialgHom k (WeightAlgebra k)
  dsimp only
  refine ⟨augmentation_generator_sub_one_ne_zero, ?_, ?_, ?_,
    f.quotientKerEquivRange_comp_mkBialgHom,
    f.rangeInclusion_comp_quotientKerEquivRange, ?_⟩
  · intro h
    exact augmentation_one_not_mem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · refine (f.quotientKerEquivRange_mk
      ((MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k) : WeightAlgebra k) -
        1)).trans ?_
    apply Subtype.ext
    exact (RingHom.mem_ker
      (f := (Bialgebra.counitBialgHom k (WeightAlgebra k)).toAlgHom.toRingHom)).mp
        (augmentation_generator_sub_one_mem (k := k))
  · refine (f.quotientKerEquivRange_mk
      (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : k))).trans ?_
    apply Subtype.ext
    simp [f]
  · have hfactor :
        (Bialgebra.counitBialgHom k (WeightAlgebra k ⧸ augmentationIdeal k)).comp
          (Bialgebra.Quotient.mkBialgHom (R := k) (augmentationIdeal k)) = f := by
      apply BialgHom.ext
      intro a
      exact Bialgebra.Quotient.counit_mk (augmentationIdeal k) a
    exact f.rangeInclusion_comp_quotientKerEquivRange.trans
      (Bialgebra.Quotient.liftBialgHom_unique (augmentationIdeal k) f le_rfl
        (Bialgebra.counitBialgHom k (WeightAlgebra k ⧸ augmentationIdeal k)) hfactor).symm

end

end HopfIdealExamples

/-! The projection of additive group algebras over `ZMod 4` gives two distinct
points of the kernel interval, with distinct images and nonzero scalar torsion.
All Hopf structures below are the canonical group-algebra structures. -/

namespace HopfIdealProjectionExamples

private abbrev Coeff := ZMod 4
private abbrev Source := AddMonoidAlgebra Coeff (ℤ × ℤ)
private abbrev Target := AddMonoidAlgebra Coeff ℤ

private noncomputable def projection : Source →ₐc[Coeff] Target :=
  AddMonoidAlgebra.mapDomainBialgHom Coeff (AddMonoidHom.fst ℤ ℤ)

private theorem projection_surjective : Function.Surjective projection := by
  let s : ℤ →+ ℤ × ℤ := (AddMonoidHom.id ℤ).prod (0 : ℤ →+ ℤ)
  have hs : (AddMonoidHom.fst ℤ ℤ).comp s = AddMonoidHom.id ℤ := by
    ext
    rfl
  intro y
  refine ⟨AddMonoidAlgebra.mapDomainBialgHom Coeff s y, ?_⟩
  change AddMonoidAlgebra.mapDomainBialgHom Coeff (AddMonoidHom.fst ℤ ℤ)
    (AddMonoidAlgebra.mapDomainBialgHom Coeff s y) = y
  rw [AddMonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, hs,
    AddMonoidAlgebra.mapDomainBialgHom_id]
  rfl

private abbrev kernel : Ideal Source := RingHom.ker (projection.toAlgHom : Source →+* Target)

private noncomputable def augmentation (C : Type*) [Ring C] [HopfAlgebra Coeff C] : Ideal C :=
  RingHom.ker (Bialgebra.counitBialgHom Coeff C).toAlgHom.toRingHom

private def k : Source :=
  AddMonoidAlgebra.single (0, 1) 1 - AddMonoidAlgebra.single (0, 0) 1

private def v : Source :=
  AddMonoidAlgebra.single (1, 0) 1 - AddMonoidAlgebra.single (0, 0) 1

private def w : Target := AddMonoidAlgebra.single 1 1 - AddMonoidAlgebra.single 0 1

/-- A nonzero kernel strictly below the augmentation ideal has zero image,
whereas the augmentation ideal has proper nonzero image. The same canonical
algebras have a nonzero element `2 δ₀` killed by the nonzero scalar `2`. -/
example :
    ∃ I₀ I₁ : {I : Ideal Source // Ideal.IsHopfIdeal Coeff I ∧ kernel ≤ I},
      I₀.val = kernel ∧ I₁.val = augmentation Source ∧
      ⊥ < I₀.val ∧ I₀.val < I₁.val ∧
      ((Ideal.hopfIdealOrderIsoOfSurjective projection projection_surjective).symm I₀).val = ⊥ ∧
      ((Ideal.hopfIdealOrderIsoOfSurjective projection projection_surjective).symm I₁).val =
        augmentation Target ∧
      ⊥ < augmentation Target ∧ augmentation Target < ⊤ ∧
      (2 : Coeff) ≠ 0 ∧ (2 : Coeff) * 2 = 0 ∧
      (2 : Coeff) • (AddMonoidAlgebra.single 0 1 : Target) ≠ 0 ∧
      (2 : Coeff) • ((2 : Coeff) • (AddMonoidAlgebra.single 0 1 : Target)) = 0 := by
  have hK : Ideal.IsHopfIdeal Coeff kernel := by
    apply projection.ker_isHopfIdeal_of_isCoideal
    change (LinearMap.ker projection.toLinearMap).IsCoideal
    exact CoalgHomClass.ker_isCoideal_of_surjective projection.toCoalgHom projection_surjective
  have hA : Ideal.IsHopfIdeal Coeff (augmentation Source) := by
    apply (Bialgebra.counitBialgHom Coeff Source).ker_isHopfIdeal_of_isCoideal
    change (LinearMap.ker (Bialgebra.counitBialgHom Coeff Source).toLinearMap).IsCoideal
    exact CoalgHomClass.ker_isCoideal_of_surjective
      (Bialgebra.counitBialgHom Coeff Source).toCoalgHom
      (Bialgebra.counit_surjective (R := Coeff) (A := Source))
  have hB : Ideal.IsHopfIdeal Coeff (augmentation Target) := by
    apply (Bialgebra.counitBialgHom Coeff Target).ker_isHopfIdeal_of_isCoideal
    change (LinearMap.ker (Bialgebra.counitBialgHom Coeff Target).toLinearMap).IsCoideal
    exact CoalgHomClass.ker_isCoideal_of_surjective
      (Bialgebra.counitBialgHom Coeff Target).toCoalgHom
      (Bialgebra.counit_surjective (R := Coeff) (A := Target))
  have hcomap : (augmentation Target).comap (projection.toAlgHom : Source →+* Target) =
      augmentation Source := by
    ext x
    change Coalgebra.counit (R := Coeff) (projection x) = 0 ↔
      Coalgebra.counit (R := Coeff) x = 0
    rw [CoalgHomClass.counit_comp_apply projection x]
  have hle : kernel ≤ augmentation Source := by
    rw [← hcomap]
    exact Ideal.comap_mono bot_le
  have hk : k ∈ kernel := by
    apply RingHom.mem_ker.mpr
    change projection k = 0
    simp [projection, k]
  have hkne : k ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Source => x.coeff (0, 1)) h
    simp only [k, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
      Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' (by decide : ((0, 0) : ℤ × ℤ) ≠ (0, 1)),
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, sub_zero] at hc
    exact (by decide : (1 : ZMod 4) ≠ 0) hc
  have hKbot : kernel ≠ ⊥ := by
    intro h
    apply hkne
    simpa only [h, Submodule.mem_bot] using hk
  have hv : v ∈ augmentation Source := by
    apply RingHom.mem_ker.mpr
    change Coalgebra.counit (R := Coeff) v = 0
    simp only [v, map_sub, AddMonoidAlgebra.counit_single, Bialgebra.counit_one, sub_self]
  have hfv : projection v = w := by
    simp [projection, v, w]
  have hwne : w ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Target => x.coeff 1) h
    simp only [w, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
      Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' (by decide : (0 : ℤ) ≠ 1),
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, sub_zero] at hc
    exact (by decide : (1 : ZMod 4) ≠ 0) hc
  have hlt : kernel < augmentation Source := by
    refine lt_of_le_not_ge hle ?_
    intro h
    exact hwne (hfv.symm.trans (RingHom.mem_ker.mp (h hv)))
  have hw : w ∈ augmentation Target := by
    apply RingHom.mem_ker.mpr
    change Coalgebra.counit (R := Coeff) w = 0
    simp only [w, map_sub, AddMonoidAlgebra.counit_single, Bialgebra.counit_one, sub_self]
  have hBbot : augmentation Target ≠ ⊥ := by
    intro h
    apply hwne
    simpa only [h, Submodule.mem_bot] using hw
  have hBtop : augmentation Target ≠ ⊤ := by
    intro h
    have hone : (1 : Target) ∈ augmentation Target := by
      rw [h]
      exact Submodule.mem_top
    change (Bialgebra.counitBialgHom Coeff Target) (1 : Target) = 0 at hone
    have hc : (1 : Coeff) = 0 := by simpa only [map_one] using hone
    exact (by decide : (1 : ZMod 4) ≠ 0) hc
  have hforward :
      (Ideal.hopfIdealOrderIsoOfSurjective projection projection_surjective
        ⟨augmentation Target, hB⟩).val = augmentation Source := by
    simpa only [Ideal.hopfIdealOrderIsoOfSurjective_apply_val] using hcomap
  have hmapK : kernel.map (projection.toAlgHom : Source →+* Target) = ⊥ :=
    Ideal.map_comap_of_surjective (projection.toAlgHom : Source →+* Target) projection_surjective ⊥
  have hmapA : (augmentation Source).map (projection.toAlgHom : Source →+* Target) =
      augmentation Target := by
    rw [← hforward, Ideal.hopfIdealOrderIsoOfSurjective_apply_val]
    exact Ideal.map_comap_of_surjective
      (projection.toAlgHom : Source →+* Target) projection_surjective _
  have htwo : (2 : Coeff) ≠ 0 := by
    change (2 : ZMod 4) ≠ 0
    decide
  have htwo_sq : (2 : Coeff) * 2 = 0 := by
    change (2 : ZMod 4) * 2 = 0
    decide
  have ht : (2 : Coeff) • (AddMonoidAlgebra.single 0 1 : Target) ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Target => x.coeff 0) h
    norm_num at hc
    exact htwo hc
  refine ⟨⟨kernel, hK, le_rfl⟩, ⟨augmentation Source, hA, hle⟩, rfl, rfl,
    bot_lt_iff_ne_bot.mpr hKbot, hlt, ?_, ?_, bot_lt_iff_ne_bot.mpr hBbot,
    lt_top_iff_ne_top.mpr hBtop, htwo, htwo_sq, ht, ?_⟩
  · simpa only [Ideal.hopfIdealOrderIsoOfSurjective_symm_apply_val] using hmapK
  · simpa only [Ideal.hopfIdealOrderIsoOfSurjective_symm_apply_val] using hmapA
  · rw [smul_smul, htwo_sq, zero_smul]

end HopfIdealProjectionExamples
