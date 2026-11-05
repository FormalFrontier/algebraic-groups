/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Coalgebra.Convolution
public import AlgebraicGroups.Algebra.Coalgebra.DualAnnihilator
public import ProjectiveModules.Dual.TensorProduct

@[expose] public section

/-!
# Coideals and convolution-stable annihilators

A submodule whose quotient module is projective is a coideal if and only if its
full-dual annihilator contains the counit and is closed under convolution.
The characterization needs only a comultiplication and a counit; coassociativity
and the counit identities are not required. Projectivity is imposed on the quotient,
not on the ambient module, and no finite-generation hypothesis is used.

The forward closure statements and the full convolution-subalgebra construction
are provided by `AlgebraicGroups.Algebra.Coalgebra.DualAnnihilator`. The converse
uses tensor-quotient exactness and separation by rank-one dual forms.

## References

* `Mathlib.RingTheory.Coalgebra.Quotient` supplies coideals and quotient-tensor exactness.
* `ProjectiveModules.Dual.TensorProduct` supplies separation by rank-one dual forms.
-/

open TensorProduct

universe uR uM uN uP uQ

section TensorPairing

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

private theorem mul'_map_pairing
    (α : Module.Dual R M) (β : Module.Dual R N) (t : M ⊗[R] N) :
    LinearMap.mul' R R (TensorProduct.map α β t) =
      TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β) t := by
  have h : (LinearMap.mul' R R).comp (TensorProduct.map α β) =
      TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    change LinearMap.mul' R R (TensorProduct.map α β (m ⊗ₜ[R] n)) =
      TensorProduct.dualDistrib R M N (α ⊗ₜ[R] β) (m ⊗ₜ[R] n)
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply,
      TensorProduct.dualDistrib_apply]
  exact LinearMap.congr_fun h t

private theorem dualDistrib_map_pairing
    (u : M →ₗ[R] P) (v : N →ₗ[R] Q)
    (α : Module.Dual R P) (β : Module.Dual R Q) (t : M ⊗[R] N) :
    TensorProduct.dualDistrib R P Q (α ⊗ₜ[R] β) (TensorProduct.map u v t) =
      TensorProduct.dualDistrib R M N ((α.comp u) ⊗ₜ[R] (β.comp v)) t := by
  rw [← mul'_map_pairing, ← mul'_map_pairing, TensorProduct.map_comp,
    LinearMap.comp_apply]

end TensorPairing

section Convolution

variable {R : Type uR} [CommSemiring R]
variable {C : Type uM} {D : Type uP}
variable [AddCommMonoid C] [AddCommMonoid D] [Module R C] [Module R D]
variable [CoalgebraStruct R C]

private theorem convMul_pullback_apply
    (q : C →ₗ[R] D) (f g : Module.Dual R D) (c : C) :
    WithConv.ofConv
        (WithConv.toConv (f.comp q) * WithConv.toConv (g.comp q)) c =
      TensorProduct.dualDistrib R D D (f ⊗ₜ[R] g)
        (TensorProduct.map q q (CoalgebraStruct.comul (R := R) c)) := by
  rw [LinearMap.convMul_apply]
  exact (mul'_map_pairing (f.comp q) (g.comp q) _).trans
    (dualDistrib_map_pairing q q f g _).symm

end Convolution


namespace Submodule

open scoped TensorProduct

universe u v

variable {R : Type u} {C : Type v} [CommRing R] [AddCommGroup C]
  [Module R C] [CoalgebraStruct R C]

/-- If the quotient module is projective, a submodule is a coideal exactly when its
annihilator contains the counit and is closed under convolution. -/
theorem isCoideal_iff_counit_mem_dualAnnihilator_and_convMul_mem
    (p : Submodule R C) [Module.Projective R (C ⧸ p)] :
    p.IsCoideal ↔
      (CoalgebraStruct.counit : Module.Dual R C) ∈ p.dualAnnihilator ∧
      ∀ f ∈ p.dualAnnihilator, ∀ g ∈ p.dualAnnihilator,
        WithConv.ofConv (WithConv.toConv f * WithConv.toConv g) ∈ p.dualAnnihilator := by
  constructor
  · intro hp
    exact ⟨hp.counit_mem_dualAnnihilator,
      fun _ hf _ hg ↦ hp.convMul_mem_dualAnnihilator hf hg⟩
  · rintro ⟨hcounit, hmul⟩
    apply (isCoideal_iff_comul_mem p).2
    refine ⟨(mem_dualAnnihilator _).1 hcounit, ?_⟩
    intro c hc
    have hqann (α : Module.Dual R (C ⧸ p)) : α.comp p.mkQ ∈ p.dualAnnihilator := by
      apply (mem_dualAnnihilator _).2
      intro x hx
      have hxq : p.mkQ x = 0 := by
        change x ∈ LinearMap.ker p.mkQ
        simpa only [p.ker_mkQ] using hx
      simp only [LinearMap.comp_apply, hxq, map_zero]
    -- Separate the image of the comultiplication by duals of the quotient.
    have hzero : TensorProduct.map p.mkQ p.mkQ
        ((CoalgebraStruct.comul : C →ₗ[R] C ⊗[R] C) c) = 0 := by
      rw [← TensorProduct.forall_dualDistrib_apply_eq_zero_iff]
      intro α β
      calc
        TensorProduct.dualDistrib R (C ⧸ p) (C ⧸ p) (α ⊗ₜ[R] β)
            (TensorProduct.map p.mkQ p.mkQ
              ((CoalgebraStruct.comul : C →ₗ[R] C ⊗[R] C) c)) =
            WithConv.ofConv
              (WithConv.toConv (α.comp p.mkQ) * WithConv.toConv (β.comp p.mkQ)) c := by
          exact (convMul_pullback_apply p.mkQ α β c).symm
        _ = 0 := (mem_dualAnnihilator _).1 (hmul _ (hqann α) _ (hqann β)) c hc
    -- The quotient sequences identify the tensor kernel with the coideal sum.
    have hqexact : Function.Exact p.subtype p.mkQ := by
      intro x
      change p.mkQ x = 0 ↔ ∃ y : p, (y : C) = x
      constructor
      · intro hx
        have hxp : x ∈ p := by
          rw [← p.ker_mkQ]
          exact hx
        exact ⟨⟨x, hxp⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        change (y : C) ∈ LinearMap.ker p.mkQ
        rw [p.ker_mkQ]
        exact y.property
    have hker : LinearMap.ker (TensorProduct.map p.mkQ p.mkQ) =
        LinearMap.range (p.subtype.lTensor C) ⊔
          LinearMap.range (p.subtype.rTensor C) :=
      TensorProduct.map_ker hqexact p.mkQ_surjective hqexact p.mkQ_surjective
    rw [← hker]
    exact hzero

end Submodule
