/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.TensorProductQuotient
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Independent nonvacuity for tensor products of coalgebra quotients

The stock full coalgebra `Prod.instCoalgebra` on `ℤ × ℤ` has the nonzero proper
coideal spanned by `(1, 0) - (0, 1)`. Ordinary scalar linear readbacks detect surviving
classes in its quotient, the tensor of two such quotients, and the quotient by the exact
range-sup appearing in Mathlib's tensor/quotient equivalence. The independent
nonvacuity proof uses neither a coalgebra structure on the range-sup quotient nor
a coalgebra equivalence.
-/

noncomputable section

open Coalgebra
open scoped TensorProduct

namespace AlgebraicGroupsTest.TensorProductQuotient

local notation "A" => ℤ × ℤ
local notation "a" => ((1, 0) : A)
local notation "b" => ((0, 1) : A)
local notation "d" => (a - b)
local notation "p" => Submodule.span ℤ ({d} : Set A)
local notation "σ" =>
  (LinearMap.range (TensorProduct.map (Submodule.subtype p) (LinearMap.id : A →ₗ[ℤ] A)) ⊔
    LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℤ] A) (Submodule.subtype p)))

/-- Both factors use `p`; every quotient here is the ordinary stock module quotient. -/
private theorem integerProduct_nonvacuity :
    (p).IsCoideal ∧ p ≠ ⊥ ∧ p ≠ ⊤ ∧
      (p).mkQ a = (p).mkQ b ∧ (p).mkQ a ≠ 0 ∧
      (p).mkQ a ⊗ₜ[ℤ] (p).mkQ a ≠ 0 ∧
      σ ≠ ⊥ ∧ σ ≠ ⊤ ∧ d ⊗ₜ[ℤ] a ≠ 0 ∧
      d ⊗ₜ[ℤ] a ∈ σ ∧ (σ).mkQ (d ⊗ₜ[ℤ] a) = 0 ∧
      (σ).mkQ (a ⊗ₜ[ℤ] a) ≠ 0 := by
  have hd : d ∈ p := Submodule.subset_span (by simp)
  have hab : (p).mkQ a = (p).mkQ b := (Submodule.Quotient.eq p).2 hd
  have hΔa : comul (R := ℤ) a = a ⊗ₜ[ℤ] a := by simp
  have hΔb : comul (R := ℤ) b = b ⊗ₜ[ℤ] b := by simp
  have hΔd : comul (R := ℤ) d = d ⊗ₜ[ℤ] a + b ⊗ₜ[ℤ] d := by
    rw [map_sub, hΔa, hΔb, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
      sub_add_sub_cancel]
  have hcoideal : (p).IsCoideal := by
    constructor
    · have hc : p ≤ LinearMap.ker (counit (R := ℤ) : A →ₗ[ℤ] ℤ) := by
        rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
        simp
      exact fun _ hx => hc hx
    · have hc : p ≤ LinearMap.ker
          ((TensorProduct.map (p).mkQ (p).mkQ).comp (comul (R := ℤ))) := by
        rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
        change TensorProduct.map (p).mkQ (p).mkQ (comul (R := ℤ) d) = 0
        have hdQ : (p).mkQ d = 0 := by rw [map_sub, hab, sub_self]
        rw [hΔd]
        simp only [map_add, TensorProduct.map_tmul, hdQ, TensorProduct.zero_tmul,
          TensorProduct.tmul_zero, add_zero]
      exact fun _ hx => hc hx
  let s : A →ₗ[ℤ] ℤ := LinearMap.fst ℤ ℤ ℤ + LinearMap.snd ℤ ℤ ℤ
  have hp : p ≤ LinearMap.ker s := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    simp [s]
  let sbar : (A ⧸ p) →ₗ[ℤ] ℤ := (p).liftQ s hp
  have ha : (p).mkQ a ≠ 0 := by
    intro h
    simpa [sbar, s] using congrArg sbar h
  have hpbot : p ≠ ⊥ := by
    intro h
    have hd0 : d = 0 := by simpa only [h, Submodule.mem_bot] using hd
    simpa using congrArg (LinearMap.fst ℤ ℤ ℤ) hd0
  have hptop : p ≠ ⊤ := by
    intro h
    apply ha
    exact (Submodule.Quotient.mk_eq_zero p).2 (by rw [h]; exact Submodule.mem_top)
  let tq : ((A ⧸ p) ⊗[ℤ] (A ⧸ p)) →ₗ[ℤ] ℤ :=
    (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map sbar sbar)
  have hqa : (p).mkQ a ⊗ₜ[ℤ] (p).mkQ a ≠ 0 := by
    intro h
    have h' := congrArg tq h
    change (TensorProduct.lid ℤ ℤ) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = tq 0 at h'
    rw [TensorProduct.lid_tmul, one_smul, map_zero] at h'
    exact one_ne_zero h'
  let t : (A ⊗[ℤ] A) →ₗ[ℤ] ℤ :=
    (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map s s)
  have hσ : σ ≤ LinearMap.ker t := by
    apply sup_le
    · intro z hz
      rcases hz with ⟨u, rfl⟩
      change t (TensorProduct.map (Submodule.subtype p)
        (LinearMap.id : A →ₗ[ℤ] A) u) = 0
      induction u with
      | tmul x y =>
          have hx : s (x : A) = 0 := hp x.property
          change (TensorProduct.lid ℤ ℤ) (s (x : A) ⊗ₜ[ℤ] s y) = 0
          rw [hx, TensorProduct.zero_tmul, map_zero]
      | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
    · intro z hz
      rcases hz with ⟨u, rfl⟩
      change t (TensorProduct.map (LinearMap.id : A →ₗ[ℤ] A)
        (Submodule.subtype p) u) = 0
      induction u with
      | tmul x y =>
          have hy : s (y : A) = 0 := hp y.property
          change (TensorProduct.lid ℤ ℤ) (s x ⊗ₜ[ℤ] s (y : A)) = 0
          rw [hy, TensorProduct.tmul_zero, map_zero]
      | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  let tbar : ((A ⊗[ℤ] A) ⧸ σ) →ₗ[ℤ] ℤ := (σ).liftQ t hσ
  have hz : (σ).mkQ (a ⊗ₜ[ℤ] a) ≠ 0 := by
    intro h
    have h' := congrArg tbar h
    change (TensorProduct.lid ℤ ℤ) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = tbar 0 at h'
    rw [TensorProduct.lid_tmul, one_smul, map_zero] at h'
    exact one_ne_zero h'
  have hσtop : σ ≠ ⊤ := by
    intro h
    apply hz
    exact (Submodule.Quotient.mk_eq_zero σ).2 (by rw [h]; exact Submodule.mem_top)
  have hu : d ⊗ₜ[ℤ] a ∈ σ :=
    Submodule.mem_sup_left ⟨(⟨d, hd⟩ : p) ⊗ₜ[ℤ] a, rfl⟩
  let r : (A ⊗[ℤ] A) →ₗ[ℤ] ℤ :=
    (TensorProduct.lid ℤ ℤ).toLinearMap.comp
      (TensorProduct.map (LinearMap.fst ℤ ℤ ℤ) s)
  have hu0 : d ⊗ₜ[ℤ] a ≠ 0 := by
    intro h
    have h' := congrArg r h
    change (TensorProduct.lid ℤ ℤ) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = r 0 at h'
    rw [TensorProduct.lid_tmul, one_smul, map_zero] at h'
    exact one_ne_zero h'
  have hσbot : σ ≠ ⊥ := by
    intro h
    apply hu0
    simpa only [h, Submodule.mem_bot] using hu
  exact ⟨hcoideal, hpbot, hptop, hab, ha, hqa, hσbot, hσtop, hu0, hu,
    (Submodule.Quotient.mk_eq_zero σ).2 hu, hz⟩

/-- The scalar bottom boundary needs neither a top coideal nor a replacement quotient carrier. -/
private theorem scalar_bot_boundary :
    (⊥ : Submodule ℤ ℤ).IsCoideal ∧
      LinearMap.range (TensorProduct.map (⊥ : Submodule ℤ ℤ).subtype
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
        (⊥ : Submodule ℤ ℤ).subtype) = ⊥ := by
  constructor
  · constructor <;> intro x hx <;> simp [(Submodule.mem_bot ℤ).mp hx]
  · have h0 : (⊥ : Submodule ℤ ℤ).subtype = 0 := by
      apply LinearMap.ext
      intro x
      exact (Submodule.mem_bot ℤ).mp x.property
    simp [h0]

/-- The integer product example instantiates the tensor-relation coideal theorem. -/
private theorem integerProduct_tensor_quotient_coideal : (σ).IsCoideal := by
  let : (p).IsCoideal := integerProduct_nonvacuity.1
  exact TensorProduct.quotientTensorQuotient_isCoideal p p

/-- The scalar bottom example also instantiates the tensor-relation coideal theorem. -/
private theorem scalar_tensor_quotient_coideal :
    (LinearMap.range (TensorProduct.map (⊥ : Submodule ℤ ℤ).subtype
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
        (⊥ : Submodule ℤ ℤ).subtype)).IsCoideal := by
  let : (⊥ : Submodule ℤ ℤ).IsCoideal := scalar_bot_boundary.1
  exact TensorProduct.quotientTensorQuotient_isCoideal
    (⊥ : Submodule ℤ ℤ) (⊥ : Submodule ℤ ℤ)

section

attribute [local instance] TensorProduct.quotientTensorQuotient_isCoideal

local instance : (p).IsCoideal := integerProduct_nonvacuity.1

local instance quotientTensorCoalgebraStruct :
    @CoalgebraStruct ℤ _ Int.instCommRing.toCommSemiring _
      (@TensorProduct.instModule ℤ Int.instCommRing.toCommSemiring (A ⧸ p) (A ⧸ p)
        (Submodule.Quotient.addCommMonoid p) (Submodule.Quotient.addCommMonoid p)
        (Submodule.Quotient.module p) (Submodule.Quotient.module p)) :=
  @TensorProduct.instCoalgebraStruct ℤ ℤ (A ⧸ p) (A ⧸ p)
    Int.instCommRing.toCommSemiring Int.instCommRing.toCommSemiring
    (Submodule.Quotient.addCommMonoid p) (Submodule.Quotient.addCommMonoid p)
    (Algebra.id ℤ) (Submodule.Quotient.module p) (Submodule.Quotient.module p)
    (Submodule.Quotient.module p) _
    (Coalgebra.Quotient.instCoalgebraStructQuotientSubmodule p)
    (Coalgebra.Quotient.instCoalgebraStructQuotientSubmodule p)

/-- The equivalence carries the surviving tensor class in both directions, and the
quotient projection factors uniquely through the tensor of the quotients. -/
private theorem integerProduct_tensor_quotient_equiv :
    TensorProduct.quotientTensorQuotientCoalgEquiv p p
        ((p).mkQ a ⊗ₜ[ℤ] (p).mkQ a) = (σ).mkQ (a ⊗ₜ[ℤ] a) ∧
      (TensorProduct.quotientTensorQuotientCoalgEquiv p p).symm
        ((σ).mkQ (a ⊗ₜ[ℤ] a)) = (p).mkQ a ⊗ₜ[ℤ] (p).mkQ a ∧
      TensorProduct.quotientTensorQuotientCoalgEquiv p p
        ((p).mkQ a ⊗ₜ[ℤ] (p).mkQ a) ≠ 0 ∧
      ∃! g : @CoalgHom ℤ _ ((A ⊗[ℤ] A) ⧸ σ) Int.instCommRing.toCommSemiring _
          (@TensorProduct.instModule ℤ Int.instCommRing.toCommSemiring (A ⧸ p) (A ⧸ p)
            (Submodule.Quotient.addCommMonoid p) (Submodule.Quotient.addCommMonoid p)
            (Submodule.Quotient.module p) (Submodule.Quotient.module p))
          (Submodule.Quotient.addCommGroup σ).toAddCommMonoid (Submodule.Quotient.module σ)
          quotientTensorCoalgebraStruct
          (Coalgebra.Quotient.instCoalgebraStructQuotientSubmodule σ),
        g.toLinearMap.comp (TensorProduct.map (p).mkQ (p).mkQ) = (σ).mkQ := by
  have hforward :=
    TensorProduct.quotientTensorQuotientCoalgEquiv_apply_tmul_mk_tmul_mk p p a a
  refine ⟨hforward,
    TensorProduct.quotientTensorQuotientCoalgEquiv_symm_apply_mk_tmul p p a a, ?_, ?_⟩
  · simp only [Submodule.mkQ_apply]
    rw [hforward]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnonzero⟩ := integerProduct_nonvacuity
    exact hnonzero
  · exact TensorProduct.quotientTensorQuotientCoalgEquiv_existsUnique_factor p p
      (Coalgebra.Quotient.mkQCoalgHom σ) (Submodule.ker_mkQ σ).symm.le

local instance : (⊥ : Submodule ℤ ℤ).IsCoideal := scalar_bot_boundary.1

/-- The scalar bottom boundary retains the representative formula on the tensor of units. -/
private theorem scalar_bot_tensor_quotient_equiv :
    TensorProduct.quotientTensorQuotientCoalgEquiv
        (⊥ : Submodule ℤ ℤ) (⊥ : Submodule ℤ ℤ)
        ((⊥ : Submodule ℤ ℤ).mkQ (1 : ℤ) ⊗ₜ[ℤ] (⊥ : Submodule ℤ ℤ).mkQ (1 : ℤ)) =
      Submodule.Quotient.mk ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) :=
  TensorProduct.quotientTensorQuotientCoalgEquiv_apply_tmul_mk_tmul_mk
    (⊥ : Submodule ℤ ℤ) (⊥ : Submodule ℤ ℤ) 1 1

end

end AlgebraicGroupsTest.TensorProductQuotient
