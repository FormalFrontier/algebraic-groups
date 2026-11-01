/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Coalgebra.BaseChange

/-!
# Extension of scalars for right comodules

The scalar extension of a specified right coaction uses the tensor coalgebra
on the scalar-extended coalgebra and the tensor-distribution equivalence.
No flatness, projectivity or finiteness is needed for the construction.

## References

Mathlib's tensor-product coalgebras and scalar-extension equivalences.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {K : Type u} {C : Type v} {W : Type w}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid W] [Module K W]
variable (R : Type z) [CommSemiring R] [Algebra K R]

omit [Coalgebra K C] in
private theorem distribBaseChange_assoc (r : R) (t : W ⊗[K] C) (c : C) :
    _root_.TensorProduct.assoc R (R ⊗[K] W) (R ⊗[K] C) (R ⊗[K] C)
        ((_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
          (r ⊗ₜ[K] t)) ⊗ₜ[R] ((1 : R) ⊗ₜ[K] c)) =
      (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R C C).toLinearMap.lTensor
        (R ⊗[K] W)
        (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W (C ⊗[K] C)
          (r ⊗ₜ[K] _root_.TensorProduct.assoc K W C C (t ⊗ₜ[K] c))) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul w d =>
    simp only [_root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      _root_.TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
  | add x y hx hy =>
    simp only [_root_.TensorProduct.tmul_add, _root_.TensorProduct.add_tmul, map_add, hx, hy]

/-- Extend a specified right coaction to the scalar-extended module and coalgebra. -/
noncomputable def baseChange (X : RightComodule K C W) :
    RightComodule R (R ⊗[K] C) (R ⊗[K] W) where
  coaction :=
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C).toLinearMap ∘ₗ
      X.coaction.baseChange R
  coassoc := by
    let ρ : (R ⊗[K] W) →ₗ[R] (R ⊗[K] W) ⊗[R] (R ⊗[K] C) :=
      (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C).toLinearMap ∘ₗ
        X.coaction.baseChange R
    let T : R ⊗[K] (W ⊗[K] (C ⊗[K] C)) →ₗ[R]
        (R ⊗[K] W) ⊗[R] ((R ⊗[K] C) ⊗[R] (R ⊗[K] C)) :=
      (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R C C).toLinearMap.lTensor
        (R ⊗[K] W) ∘ₗ
          (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W
            (C ⊗[K] C)).toLinearMap
    -- The two iterated coactions are images under the same triple-tensor comparison.
    have hleft (r : R) (t : W ⊗[K] C) :
        _root_.TensorProduct.assoc R (R ⊗[K] W) (R ⊗[K] C) (R ⊗[K] C)
            (ρ.rTensor (R ⊗[K] C)
              (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
                (r ⊗ₜ[K] t))) =
          T (r ⊗ₜ[K] _root_.TensorProduct.assoc K W C C (X.coaction.rTensor C t)) := by
      induction t using _root_.TensorProduct.inductionOn with
      | tmul w c =>
        simpa only [ρ, T, LinearMap.comp_apply, LinearMap.rTensor_tmul,
          LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
          _root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul] using
            distribBaseChange_assoc (K := K) R r (X.coaction w) c
      | add x y hx hy =>
        simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]
    have hright (r : R) (t : W ⊗[K] C) :
        (comul (R := R) (A := R ⊗[K] C)).lTensor (R ⊗[K] W)
            (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
              (r ⊗ₜ[K] t)) =
          T (r ⊗ₜ[K] (comul (R := K) (A := C)).lTensor W t) := by
      induction t using _root_.TensorProduct.inductionOn with
      | tmul w c =>
        simp only [T, _root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          LinearMap.lTensor_tmul, Coalgebra.comul_baseChange K R C,
          LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
      | add x y hx hy =>
        simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]
    change _root_.TensorProduct.assoc R (R ⊗[K] W) (R ⊗[K] C) (R ⊗[K] C) ∘ₗ
        ρ.rTensor (R ⊗[K] C) ∘ₗ ρ =
      (comul (R := R) (A := R ⊗[K] C)).lTensor (R ⊗[K] W) ∘ₗ ρ
    apply _root_.TensorProduct.AlgebraTensorModule.ext
    intro r w
    change _root_.TensorProduct.assoc R (R ⊗[K] W) (R ⊗[K] C) (R ⊗[K] C)
        (ρ.rTensor (R ⊗[K] C)
          (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
            (r ⊗ₜ[K] X.coaction w))) =
      (comul (R := R) (A := R ⊗[K] C)).lTensor (R ⊗[K] W)
        (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
          (r ⊗ₜ[K] X.coaction w))
    rw [hleft, hright]
    exact congrArg (fun t : W ⊗[K] (C ⊗[K] C) => T (r ⊗ₜ[K] t))
      (congrArg (fun f : W →ₗ[K] W ⊗[K] (C ⊗[K] C) => f w) X.coassoc)
  counit_comp := by
    have h (r : R) (t : W ⊗[K] C) :
        _root_.TensorProduct.rid R (R ⊗[K] W)
            ((counit (R := R) (A := R ⊗[K] C)).lTensor (R ⊗[K] W)
              (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
                (r ⊗ₜ[K] t))) =
          r ⊗ₜ[K] _root_.TensorProduct.rid K W ((counit (R := K) (A := C)).lTensor W t) := by
      induction t using _root_.TensorProduct.inductionOn with
      | tmul w c =>
        simp only [_root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          LinearMap.lTensor_tmul, _root_.TensorProduct.counit_tmul, CommSemiring.counit_apply,
          _root_.TensorProduct.rid_tmul, _root_.TensorProduct.tmul_smul,
          _root_.TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
          Algebra.algebraMap_self_apply]
      | add x y hx hy =>
        simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]
    apply _root_.TensorProduct.AlgebraTensorModule.ext
    intro r w
    apply (_root_.TensorProduct.rid R (R ⊗[K] W)).injective
    change _root_.TensorProduct.rid R (R ⊗[K] W)
        ((counit (R := R) (A := R ⊗[K] C)).lTensor (R ⊗[K] W)
          (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
            (r ⊗ₜ[K] X.coaction w))) =
      _root_.TensorProduct.rid R (R ⊗[K] W)
        ((_root_.TensorProduct.rid R (R ⊗[K] W)).symm (r ⊗ₜ[K] w))
    rw [h, LinearEquiv.apply_symm_apply]
    have hc := congrArg (fun f : W →ₗ[K] W ⊗[K] K => f w) X.counit_comp
    change (counit (R := K) (A := C)).lTensor W (X.coaction w) =
      (_root_.TensorProduct.rid K W).symm w at hc
    rw [hc, LinearEquiv.apply_symm_apply]

/-- The coaction of scalar extension is the extended original coaction followed
by the tensor-distribution equivalence. -/
theorem baseChange_coaction (X : RightComodule K C W) :
    (X.baseChange R).coaction =
      (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C).toLinearMap ∘ₗ
        X.coaction.baseChange R := by
  rfl

/-- The coaction formula on a pure tensor. -/
@[simp] theorem baseChange_coaction_tmul (X : RightComodule K C W) (r : R) (w : W) :
    (X.baseChange R).coaction (r ⊗ₜ[K] w) =
      _root_.TensorProduct.AlgebraTensorModule.distribBaseChange K R W C
        (r ⊗ₜ[K] X.coaction w) := by
  simp only [baseChange_coaction, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe]

end Coalgebra.RightComodule
