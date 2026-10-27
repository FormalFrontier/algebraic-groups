/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.DualAnnihilator
public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The augmentation coideal in an infinite monoid algebra

For a nontrivial commutative ring `K`, use the stock coalgebra on
`MonoidAlgebra K ℕ` and the kernel of its counit. The standard basis is
`MonoidAlgebra.basis ℕ K`, with vector `single n 1`. The difference of the
vectors at 1 and 0 witnesses a nonzero augmentation kernel; the vector at 0
witnesses properness. The counit and the coordinate at 1 distinguish a nonzero
proper underlying submodule of the annihilator subalgebra. Both forward
closure results act on these maps; the subalgebra API supplies its unit and
products of scalar multiples of the counit.

The ordinary counit is surjective. Its stock first-isomorphism equivalence
makes its kernel quotient flat, so the coideal proof uses the generic
flat-quotient kernel theorem without a field or flatness hypothesis.
The TOP boundary fails the counit condition on the same stock coalgebra.

## References

Mathlib's `RingTheory.Coalgebra.MonoidAlgebra`, by Amelia Livingston, supplies
the coalgebra. Its basis, coefficient equivalence and coordinate maps are those
of `Algebra.MonoidAlgebra.Module` and `LinearAlgebra.Finsupp.Defs`. The quotient
linear equivalence is `LinearMap.quotKerEquivOfSurjective` from Mathlib;
`Module.Flat.of_linearEquiv` transports its ordinary scalar-module flatness.
-/

@[expose] public section

noncomputable section

universe u

namespace CoalgebraDualAnnihilator

variable {K : Type u} [CommRing K] [Nontrivial K]

local notation "C" => MonoidAlgebra K ℕ
local notation "ε" => (Coalgebra.counit (R := K) (A := C))
local notation "I" => LinearMap.ker ε

omit [Nontrivial K] in
private theorem counit_surjective [Nontrivial K] : Function.Surjective ε := by
  intro r
  refine ⟨r • MonoidAlgebra.single 0 (1 : K), ?_⟩
  simp

private theorem augmentation_isCoideal : (I).IsCoideal := by
  let hflat : Module.Flat K (C ⧸ I) :=
    Module.Flat.of_linearEquiv ((ε).quotKerEquivOfSurjective counit_surjective)
  let : Module.Flat K
      (C ⧸ (Coalgebra.counitCoalgHom K C : C →ₗ[K] K).ker) := by
    have hker : (Coalgebra.counitCoalgHom K C : C →ₗ[K] K).ker = I :=
      congrArg LinearMap.ker (Coalgebra.counitCoalgHom_toLinearMap K C)
    exact Eq.mpr
      (congrArg (fun J : Submodule K C => Module.Flat K (C ⧸ J)) hker) hflat
  exact CoalgHomClass.ker_isCoideal_of_flat_quotient (Coalgebra.counitCoalgHom K C)

local notation "A" =>
  Submodule.IsCoideal.dualAnnihilatorSubalgebra (augmentation_isCoideal (K := K))

omit [Nontrivial K] in
private theorem difference_mem_augmentation [Nontrivial K] :
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single 0 1 : C) ∈ I := by
  rw [LinearMap.mem_ker]
  simp

private theorem difference_ne_zero :
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single 0 1 : C) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hindex : (1 : ℕ) = 0 :=
    MonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0) h
  exact Nat.one_ne_zero hindex

private theorem counit_ne_zero : ε ≠ 0 := by
  intro h
  have hz := LinearMap.congr_fun h (MonoidAlgebra.single 0 (1 : K))
  exact (one_ne_zero : (1 : K) ≠ 0) (by simp at hz)

example : I ≠ ⊥ ∧ I ≠ ⊤ := by
  constructor
  · intro h
    have hz : (MonoidAlgebra.single 1 1 - MonoidAlgebra.single 0 1 : C) = 0 := by
      simpa only [h, Submodule.mem_bot] using difference_mem_augmentation (K := K)
    exact difference_ne_zero hz
  · intro h
    have hx : (MonoidAlgebra.single 0 1 : C) ∈ I := by
      rw [h]
      exact Submodule.mem_top
    exact (one_ne_zero : (1 : K) ≠ 0) (by simp [LinearMap.mem_ker] at hx)

example (a b : K) :
    ε ∈ (I).dualAnnihilator ∧
      (WithConv.toConv (a • ε) * WithConv.toConv (b • ε)).ofConv ∈ (I).dualAnnihilator := by
  have hε := (augmentation_isCoideal (K := K)).counit_mem_dualAnnihilator
  exact ⟨hε, augmentation_isCoideal.convMul_mem_dualAnnihilator
    ((I).dualAnnihilator.smul_mem a hε) ((I).dualAnnihilator.smul_mem b hε)⟩

example (a b : K) :
    (WithConv.toConv (a • ε) * WithConv.toConv (b • ε)).ofConv
      (MonoidAlgebra.single 0 (1 : K)) = a * b := by
  simp [LinearMap.convMul_apply, MonoidAlgebra.comul_single, CommSemiring.comul_apply]

example (a b : K) :
    (1 : WithConv (Module.Dual K C)) ∈ A ∧
      WithConv.toConv (a • ε) * WithConv.toConv (b • ε) ∈ A := by
  have hε : WithConv.toConv ε ∈ A :=
    ((augmentation_isCoideal (K := K)).toConv_mem_dualAnnihilatorSubalgebra).mpr
      (augmentation_isCoideal (K := K)).counit_mem_dualAnnihilator
  exact ⟨(A).one_mem, (A).mul_mem ((A).smul_mem hε a) ((A).smul_mem hε b)⟩

example : (A).toSubmodule ≠ ⊥ ∧ (A).toSubmodule ≠ ⊤ := by
  constructor
  · intro h
    have hε : WithConv.toConv ε ∈ (A).toSubmodule := by
      rw [(augmentation_isCoideal (K := K)).dualAnnihilatorSubalgebra_toSubmodule]
      exact (augmentation_isCoideal (K := K)).counit_mem_dualAnnihilator
    have hz : WithConv.toConv ε = 0 := by
      simpa only [h, Submodule.mem_bot] using hε
    exact counit_ne_zero (WithConv.toConv_eq_zero.mp hz)
  · intro h
    let l : Module.Dual K C :=
      (Finsupp.lapply (1 : ℕ)).comp (MonoidAlgebra.coeffLinearEquiv K).toLinearMap
    have hl : WithConv.toConv l ∈ A := by
      rw [← Subalgebra.mem_toSubmodule, h]
      exact Submodule.mem_top
    have hz := ((augmentation_isCoideal (K := K)).mem_dualAnnihilatorSubalgebra_iff).mp hl
      _ (difference_mem_augmentation (K := K))
    exact (one_ne_zero : (1 : K) ≠ 0) (by simp [l] at hz)

example : ¬ (⊤ : Submodule K C).IsCoideal := by
  intro h
  have hz := h.counit_eq_zero (x := MonoidAlgebra.single 0 (1 : K)) Submodule.mem_top
  exact (one_ne_zero : (1 : K) ≠ 0) (by simp at hz)

example : ε ∉ (⊤ : Submodule K C).dualAnnihilator := by
  simpa only [Submodule.dualAnnihilator_top, Submodule.mem_bot] using
    (counit_ne_zero (K := K))

end CoalgebraDualAnnihilator
