/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The counit range and its action on the coalgebra

The range of the counit of an `R`-coalgebra is an ideal of the commutative
semiring `R`. Its square equals itself: the fact that the counit is a
coalgebra homomorphism expresses each counit value as a sum of products of
counit values. Tensor induction proves membership in the square without
any freeness or finiteness assumption on the coalgebra.

The counit range also generates the whole coalgebra under scalar multiplication:
every element is a sum of terms `ε(x) • y` by the left counit identity. Thus its
action on the top submodule is top, even when the counit range is a proper ideal.
For a nontrivial coalgebra whose underlying module is free, a basis coordinate
maps this identity to the scalar semiring, so the counit is surjective. Neither
a finite basis nor a ring or field structure on the scalars is required.

## References

Mathlib supplies the counit coalgebra homomorphism, tensor induction,
free-module bases, ideal multiplication and submodule scalar action used here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace Coalgebra

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The scalar ideal given by the range of the counit is idempotent. -/
@[simp] theorem counit_range_mul_self :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) *
      LinearMap.range (counit (R := R) (A := C)) =
    LinearMap.range (counit (R := R) (A := C)) := by
  let I : Ideal R := LinearMap.range (counit (R := R) (A := C))
  apply le_antisymm Ideal.mul_le_right
  rintro r ⟨c, rfl⟩
  have h (t : C ⊗[R] C) :
      TensorProduct.lid R R (TensorProduct.map (counit (R := R)) (counit (R := R)) t) ∈
        I * I := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul] using
        (Ideal.mul_mem_mul (LinearMap.mem_range_self (counit (R := R)) x)
          (LinearMap.mem_range_self (counit (R := R)) y))
    | add x y hx hy =>
      simpa only [map_add] using (I * I).add_mem hx hy
  have hε : TensorProduct.map (counit (R := R)) (counit (R := R)) (comul c) =
      (1 : R) ⊗ₜ[R] counit (R := R) c := by
    simpa only [CoalgHom.toLinearMap_eq_coe, counitCoalgHom_toLinearMap,
      LinearMap.comp_apply, CommSemiring.comul_apply] using
      (LinearMap.congr_fun (counitCoalgHom R C).map_comp_comul c)
  simpa only [hε, TensorProduct.lid_tmul, one_smul] using h (comul c)

/-- The counit range generates the whole coalgebra under scalar multiplication.
This does not require the counit range to be the whole scalar semiring. -/
@[simp] theorem counit_range_smul_top :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) •
      (⊤ : Submodule R C) = ⊤ := by
  let I : Ideal R := LinearMap.range (counit (R := R) (A := C))
  apply top_unique
  intro c _
  have h (t : C ⊗[R] C) :
      TensorProduct.lid R C ((counit (R := R)).rTensor C t) ∈
        I • (⊤ : Submodule R C) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] using
        (Submodule.smul_mem_smul (LinearMap.mem_range_self (counit (R := R)) x)
          (Submodule.mem_top : y ∈ (⊤ : Submodule R C)))
    | add x y hx hy =>
      simpa only [map_add] using (I • (⊤ : Submodule R C)).add_mem hx hy
  simpa only [rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] using h (comul c)

/-- The counit range of a nontrivial coalgebra with free underlying module is the
whole scalar semiring. No finiteness assumption on a basis is needed. -/
@[simp] theorem counit_range_eq_top_of_free [Module.Free R C] [Nontrivial C] :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis R C
  let i : Module.Free.ChooseBasisIndex R C := Classical.choice inferInstance
  have hcoord : LinearMap.range (b.coord i) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro r
    refine ⟨r • b i, ?_⟩
    simp [Module.Basis.coord_apply]
  have h := congrArg (Submodule.map (b.coord i)) (counit_range_smul_top R C)
  rw [Submodule.map_smul'', Submodule.map_top, hcoord, Ideal.smul_eq_mul,
    Ideal.mul_top] at h
  exact h

/-- The counit of a nontrivial coalgebra with free underlying module is surjective
onto its commutative scalar semiring. -/
theorem counit_surjective_of_free [Module.Free R C] [Nontrivial C] :
    Function.Surjective (counit (R := R) (A := C)) :=
  LinearMap.range_eq_top.mp (counit_range_eq_top_of_free R C)

end Coalgebra
