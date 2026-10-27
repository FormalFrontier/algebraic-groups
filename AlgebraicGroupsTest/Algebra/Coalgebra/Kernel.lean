/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.FirstIsomorphism
public import AlgebraicGroups.Algebra.Coalgebra.Quotient
import AlgebraicGroups.Algebra.Coalgebra.CoidealCorrespondence
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Infinite kernels of coalgebra morphisms over a ring with zero divisors

The stock counit on `AddMonoidAlgebra (ZMod 4) ℤ` is surjective and has a
proper, nonzero, infinite kernel. Its coideality is calculated using the
stock quotient definition.

Separately, finite-support sequences carry chosen weak coalgebra data with
zero comultiplication and nonzero counit (coefficient zero). The target has
zero comultiplication and identity counit. Coefficient zero is a surjective
coalgebra morphism with proper, nonzero, infinite kernel, whose coideality
is calculated directly. The left counit law fails on both endpoints.
All chosen weak data are private and local to the second section.
-/

noncomputable section

open Coalgebra TensorProduct

namespace AlgebraicGroupsTest.CoalgebraKernel

private abbrev R := ZMod 4

private theorem zmod_four_two_ne_zero : (2 : R) ≠ 0 := by decide

private theorem zmod_four_two_mul_two_eq_zero : (2 : R) * 2 = 0 := by decide

section Full

private abbrev C := AddMonoidAlgebra R ℤ

private abbrev augmentation : C →ₗc[R] R := counitCoalgHom R C

@[instance_reducible]
private def integerGroupAlgebraCoalgebra : Coalgebra R C := inferInstance

@[instance_reducible]
private def scalarCoalgebra : Coalgebra R R := inferInstance

private theorem infinite_integerGroupAlgebra : Infinite C := by
  let : Fact (1 < 4) := ⟨by decide⟩
  infer_instance

private theorem augmentation_surjective : Function.Surjective augmentation := by
  intro r
  exact ⟨AddMonoidAlgebra.single 0 r, by simp [augmentation]⟩

private theorem difference_mem (n : ℤ) :
    AddMonoidAlgebra.single n (1 : R) - AddMonoidAlgebra.single 0 1 ∈
      (augmentation : C →ₗ[R] R).ker := by
  change counit (R := R) (_ - _) = 0
  simp only [map_sub, AddMonoidAlgebra.counit_single, sub_self]

private theorem difference_one_ne_zero :
    (AddMonoidAlgebra.single (1 : ℤ) (1 : R) - AddMonoidAlgebra.single 0 1 : C) ≠ 0 := by
  let : Fact (1 < 4) := ⟨by decide⟩
  intro h
  have hc := congrArg (fun x : C => x.coeff 1) h
  rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero] at hc
  have hz : (1 : R) = 0 := by
    simp at hc
  exact one_ne_zero hz

private theorem delta_zero_not_mem :
    AddMonoidAlgebra.single (0 : ℤ) (1 : R) ∉ (augmentation : C →ₗ[R] R).ker := by
  let : Fact (1 < 4) := ⟨by decide⟩
  change counit (R := R) _ ≠ 0
  rw [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]
  exact one_ne_zero

private theorem augmentation_ker_ne_bot : (augmentation : C →ₗ[R] R).ker ≠ ⊥ := by
  intro h
  have hz := difference_mem 1
  rw [h, Submodule.mem_bot] at hz
  exact difference_one_ne_zero hz

private theorem augmentation_ker_ne_top : (augmentation : C →ₗ[R] R).ker ≠ ⊤ := by
  intro h
  apply delta_zero_not_mem
  rw [h]
  exact Submodule.mem_top

private theorem infinite_augmentation_ker : Infinite (augmentation : C →ₗ[R] R).ker := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let point (n : ℕ) : (augmentation : C →ₗ[R] R).ker :=
    ⟨AddMonoidAlgebra.single (Int.negSucc n) 1 - AddMonoidAlgebra.single 0 1,
      difference_mem _⟩
  apply Infinite.of_injective point
  intro m n h
  by_contra hmn
  have hindex : Int.negSucc m ≠ Int.negSucc n := fun e => hmn (Int.negSucc.inj e)
  have hc := congrArg
    (fun x : (augmentation : C →ₗ[R] R).ker => x.val.coeff (Int.negSucc m)) h
  have hz : (1 : R) = 0 := by
    simp [point, Ne.symm hindex] at hc
  exact one_ne_zero hz

-- This calculation uses the old coideal fields, not the generic kernel theorem.
private theorem augmentation_ker_isCoideal : (augmentation : C →ₗ[R] R).ker.IsCoideal := by
  let I := (augmentation : C →ₗ[R] R).ker
  have hsingle (n : ℤ) (r : R) :
      I.mkQ (AddMonoidAlgebra.single n r) = I.mkQ (AddMonoidAlgebra.single 0 r) := by
    apply (Submodule.Quotient.eq I).mpr
    change counit (R := R) (_ - _) = 0
    simp
  have hmap (x : C) :
      TensorProduct.map I.mkQ I.mkQ (comul x) =
        I.mkQ (AddMonoidAlgebra.single 0 1) ⊗ₜ[R]
          I.mkQ (AddMonoidAlgebra.single 0 (counit (R := R) x)) := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add, AddMonoidAlgebra.single_add, TensorProduct.tmul_add]
        using congrArg₂ (· + ·) hx hy
    | single n r =>
      simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
        AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]
      rw [hsingle n 1, hsingle n r]
  constructor
  · intro x hx
    exact hx
  · intro x hx
    have heps : counit (R := R) x = 0 := hx
    rw [hmap x, heps, AddMonoidAlgebra.single_zero, I.mkQ.map_zero]
    exact TensorProduct.tmul_zero _ _

private theorem augmentation_ker_isCoideal_use :
    (augmentation : C →ₗ[R] R).ker.IsCoideal :=
  CoalgHomClass.ker_isCoideal_of_surjective augmentation (by
    intro r
    exact ⟨AddMonoidAlgebra.single 0 r, by simp [augmentation]⟩)

private theorem quotKerEquiv_augmentation_single (n : ℤ) (r : R) :
    CoalgHomClass.quotKerEquivOfSurjective augmentation (by
      intro s
      exact ⟨AddMonoidAlgebra.single 0 s, by simp [augmentation]⟩)
      (Submodule.Quotient.mk (p := (augmentation : C →ₗ[R] R).ker)
        (AddMonoidAlgebra.single n r)) = r := by
  calc
    _ = augmentation (AddMonoidAlgebra.single n r) :=
      CoalgHomClass.quotKerEquivOfSurjective_apply_mk augmentation (by
        intro s
        exact ⟨AddMonoidAlgebra.single 0 s, by simp [augmentation]⟩)
        (AddMonoidAlgebra.single n r)
    _ = r := by simp [augmentation]

end Full

section Weak

private abbrev W := ℕ →₀ R

private abbrev sourceData : CoalgebraStruct R W where
  comul := 0
  counit := Finsupp.lapply 0

private abbrev targetData : CoalgebraStruct R R where
  comul := 0
  counit := LinearMap.id

attribute [local instance] sourceData targetData

private abbrev coefficientZero : W →ₗc[R] R where
  toLinearMap := Finsupp.lapply 0
  counit_comp := by
    change LinearMap.id.comp (Finsupp.lapply (R := R) 0) = Finsupp.lapply 0
    rfl
  map_comp_comul := by
    change TensorProduct.map (Finsupp.lapply (R := R) 0) (Finsupp.lapply 0) ∘ₗ
      (0 : W →ₗ[R] W ⊗[R] W) = (0 : R →ₗ[R] R ⊗[R] R) ∘ₗ Finsupp.lapply 0
    simp

private theorem coefficientZero_toLinearMap_eq_lapply :
    (coefficientZero : W →ₗ[R] R) = Finsupp.lapply 0 := rfl

private theorem coefficientZero_apply (x : W) : coefficientZero x = x 0 := rfl

private theorem infinite_finsupp : Infinite W := by
  let : Fact (1 < 4) := ⟨by decide⟩
  infer_instance

private theorem coefficientZero_surjective : Function.Surjective coefficientZero := by
  intro r
  exact ⟨Finsupp.single 0 r, by simp [coefficientZero]⟩

private theorem counit_single_zero_eq_one : counit (R := R) (Finsupp.single 0 (1 : R) : W) = 1 := by
  change (Finsupp.single 0 (1 : R) : W) 0 = 1
  simp

private theorem weak_counit_one_eq_one : counit (R := R) (1 : R) = 1 := rfl

private theorem counit_single_zero_ne_zero :
    counit (R := R) (Finsupp.single 0 (1 : R) : W) ≠ 0 := by
  let : Fact (1 < 4) := ⟨by decide⟩
  change (Finsupp.single 0 (1 : R) : W) 0 ≠ 0
  simp

private theorem weak_counit_one_ne_zero : counit (R := R) (1 : R) ≠ 0 := by
  let : Fact (1 < 4) := ⟨by decide⟩
  change (1 : R) ≠ 0
  exact one_ne_zero

private theorem delta_one_mem :
    Finsupp.single 1 (1 : R) ∈ (coefficientZero : W →ₗ[R] R).ker := by
  change (Finsupp.single 1 (1 : R) : W) 0 = 0
  simp

private theorem delta_one_ne_zero : (Finsupp.single 1 (1 : R) : W) ≠ 0 := by
  let : Fact (1 < 4) := ⟨by decide⟩
  simp

private theorem delta_zero_not_mem_weak :
    Finsupp.single 0 (1 : R) ∉ (coefficientZero : W →ₗ[R] R).ker := by
  let : Fact (1 < 4) := ⟨by decide⟩
  change (Finsupp.single 0 (1 : R) : W) 0 ≠ 0
  simp

private theorem coefficientZero_ker_ne_bot : (coefficientZero : W →ₗ[R] R).ker ≠ ⊥ := by
  intro h
  have hz := delta_one_mem
  rw [h, Submodule.mem_bot] at hz
  exact delta_one_ne_zero hz

private theorem coefficientZero_ker_ne_top : (coefficientZero : W →ₗ[R] R).ker ≠ ⊤ := by
  intro h
  apply delta_zero_not_mem_weak
  rw [h]
  exact Submodule.mem_top

private theorem infinite_coefficientZero_ker : Infinite (coefficientZero : W →ₗ[R] R).ker := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let point (n : ℕ) : (coefficientZero : W →ₗ[R] R).ker :=
    ⟨Finsupp.single (n + 1) 1, by
      change (Finsupp.single (n + 1) (1 : R) : W) 0 = 0
      simp⟩
  apply Infinite.of_injective point
  intro m n h
  by_contra hmn
  have hindex : n + 1 ≠ m + 1 := fun e => hmn (Nat.succ.inj e.symm)
  have hc := congrArg
    (fun x : (coefficientZero : W →ₗ[R] R).ker => x.val (m + 1)) h
  have hz : (1 : R) = 0 := by
    simpa only [point, Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hindex] using hc
  exact one_ne_zero hz

-- The kernel's coideality is independent of any lawful coalgebra instance.
private theorem coefficientZero_ker_isCoideal : (coefficientZero : W →ₗ[R] R).ker.IsCoideal := by
  constructor
  · intro x hx
    exact hx
  · intro x _
    change TensorProduct.map _ _ ((0 : W →ₗ[R] W ⊗[R] W) x) = 0
    exact (TensorProduct.map
      (coefficientZero : W →ₗ[R] R).ker.mkQ
      (coefficientZero : W →ₗ[R] R).ker.mkQ).map_zero

-- Contracting the left counit identity already fails at these nonzero vectors.
private theorem finsupp_left_counit_ne :
    (TensorProduct.lid R W)
      ((counit (R := R) (A := W)).rTensor W
        (comul (Finsupp.single 1 (1 : R) : W))) ≠ Finsupp.single 1 1 := by
  change (TensorProduct.lid R W)
    ((Finsupp.lapply (R := R) 0).rTensor W
      ((0 : W →ₗ[R] W ⊗[R] W) (Finsupp.single 1 1))) ≠ Finsupp.single 1 1
  simpa using Ne.symm delta_one_ne_zero

private theorem scalar_left_counit_ne :
    (TensorProduct.lid R R)
      ((counit (R := R) (A := R)).rTensor R (comul (1 : R))) ≠ (1 : R) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  change (TensorProduct.lid R R)
    ((LinearMap.id : R →ₗ[R] R).rTensor R ((0 : R →ₗ[R] R ⊗[R] R) 1)) ≠ (1 : R)
  simpa only [LinearMap.zero_apply, map_zero] using (zero_ne_one : (0 : R) ≠ 1)

private theorem coefficientZero_ker_isCoideal_use :
    (coefficientZero : W →ₗ[R] R).ker.IsCoideal :=
  CoalgHomClass.ker_isCoideal_of_surjective coefficientZero (by
    intro r
    exact ⟨Finsupp.single 0 r, by simp [coefficientZero]⟩)

private theorem quotKerEquiv_coefficientZero_single_zero (r : R) :
    CoalgHomClass.quotKerEquivOfSurjective coefficientZero (by
      intro s
      exact ⟨Finsupp.single 0 s, by simp [coefficientZero]⟩)
      (Submodule.Quotient.mk (p := (coefficientZero : W →ₗ[R] R).ker)
        (Finsupp.single 0 r)) = r := by
  calc
    _ = coefficientZero (Finsupp.single 0 r) :=
      CoalgHomClass.quotKerEquivOfSurjective_apply_mk coefficientZero (by
        intro s
        exact ⟨Finsupp.single 0 s, by simp [coefficientZero]⟩)
        (Finsupp.single 0 r)
    _ = r := by simp [coefficientZero]

private theorem coefficientZero_coidealOrderIso_symm_bot_val :
    ((Submodule.coidealOrderIsoOfSurjective coefficientZero (by
      intro r
      exact ⟨Finsupp.single 0 r, by simp [coefficientZero]⟩)).symm
        ⟨⊥, by
          constructor <;> intro x hx <;> rw [Submodule.mem_bot] at hx <;>
            subst x <;> simp⟩).val =
      (coefficientZero : W →ₗ[R] R).ker := by
  exact
    (Submodule.coidealOrderIsoOfSurjective_symm_apply_val coefficientZero
      coefficientZero_surjective
      ⟨⊥, by
        constructor <;> intro x hx <;> rw [Submodule.mem_bot] at hx <;>
          subst x <;> simp⟩).trans
      (Submodule.comap_bot (coefficientZero : W →ₗ[R] R))

end Weak

end AlgebraicGroupsTest.CoalgebraKernel
