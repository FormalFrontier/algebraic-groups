/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Evaluation
public import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators

/-!
# Convolution and evaluation of right coactions

For a specified right coaction `ρ : V →ₗ[K] V ⊗[K] C`, evaluation against
linear coefficients in a commutative `K`-algebra preserves convolution:
`T_(φ * ψ) = T_φ.comp T_ψ`. Thus evaluation gives a monoid homomorphism to
the composition monoid of endomorphisms of `A ⊗[K] V`, with no algebra
structure on `C` or multiplicativity assumption on the coefficients.

The proof reuses the weak coefficient-composition theorem. Commuting the
coalgebra factor to the left reverses the coproduct. The order reversal in
that theorem cancels this reversal, using commutativity of the coefficient
algebra. No opposite coalgebra instance is installed.

## References

* The weak composition theorem in `AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators`.
* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `RingTheory/Coalgebra/Convolution`, for the `WithConv` operations.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for right-coaction
  and convolution conventions (bibliographic credit).
-/

@[expose] public section

open scoped TensorProduct
open WithConv

universe u c v a

namespace Coalgebra.RightComodule

variable {K : Type u} {C : Type c} {V : Type v}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid V] [Module K V]

/-- Commuting a right coaction gives the left coassociativity equation with
reversed coproduct. This is only a tensor-coherence calculation. -/
private theorem commuted_coassoc (X : RightComodule K C V) :
    (_root_.TensorProduct.map
      ((TensorProduct.comm K C C).toLinearMap.comp (comul (R := K) (A := C)))
      (LinearMap.id : V →ₗ[K] V)).comp
        ((TensorProduct.comm K V C).toLinearMap.comp X.coaction) =
      (_root_.TensorProduct.assoc K C C V).symm.toLinearMap.comp
        ((_root_.TensorProduct.map (LinearMap.id : C →ₗ[K] C)
          ((TensorProduct.comm K V C).toLinearMap.comp X.coaction)).comp
            ((TensorProduct.comm K V C).toLinearMap.comp X.coaction)) := by
  let δ := (TensorProduct.comm K V C).toLinearMap.comp X.coaction
  let Δ := (TensorProduct.comm K C C).toLinearMap.comp (comul (R := K) (A := C))
  let F : V ⊗[K] (C ⊗[K] C) →ₗ[K] (C ⊗[K] C) ⊗[K] V :=
    (_root_.TensorProduct.map (TensorProduct.comm K C C).toLinearMap
      (LinearMap.id : V →ₗ[K] V)).comp (TensorProduct.comm K V (C ⊗[K] C)).toLinearMap
  have hleft :
      (_root_.TensorProduct.map Δ (LinearMap.id : V →ₗ[K] V)).comp
          (TensorProduct.comm K V C).toLinearMap =
        F.comp ((comul (R := K) (A := C)).lTensor V) := by
    ext v c
    simp [F, Δ, LinearMap.lTensor_tmul]
  have hswap (t : V ⊗[K] C) (c : C) :
      (_root_.TensorProduct.assoc K C C V).symm
          (c ⊗ₜ[K] TensorProduct.comm K V C t) =
        F (_root_.TensorProduct.assoc K V C C (t ⊗ₜ[K] c)) := by
    induction t using TensorProduct.inductionOn with
    | tmul v d => rfl
    | add x y hx hy =>
        simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, hx, hy]
  have hright :
      (_root_.TensorProduct.assoc K C C V).symm.toLinearMap.comp
          ((_root_.TensorProduct.map (LinearMap.id : C →ₗ[K] C) δ).comp
            (TensorProduct.comm K V C).toLinearMap) =
        F.comp ((_root_.TensorProduct.assoc K V C C).toLinearMap.comp
          (X.coaction.rTensor C)) := by
    ext v c
    simpa only [TensorProduct.AlgebraTensorModule.curry_apply,
      _root_.TensorProduct.curry_apply, LinearMap.restrictScalars_apply, δ,
      LinearMap.comp_apply, TensorProduct.comm_tmul, _root_.TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe] using
        hswap (X.coaction v) c
  apply LinearMap.ext
  intro v
  calc
    _root_.TensorProduct.map Δ (LinearMap.id : V →ₗ[K] V) (δ v) =
        F ((comul (R := K) (A := C)).lTensor V (X.coaction v)) :=
      LinearMap.congr_fun hleft (X.coaction v)
    _ = F (_root_.TensorProduct.assoc K V C C
        (X.coaction.rTensor C (X.coaction v))) :=
      congrArg F (X.coassoc_apply v).symm
    _ = (_root_.TensorProduct.assoc K C C V).symm
        (_root_.TensorProduct.map (LinearMap.id : C →ₗ[K] C) δ (δ v)) :=
      (LinearMap.congr_fun hright (X.coaction v)).symm

variable {A : Type a} [CommSemiring A] [Algebra K A]

/-- For the original right coaction, convolution acts on the left:
`T_(φ * ψ) = T_φ.comp T_ψ`, so the operator for `ψ` is applied first.
The coalgebra needs no multiplication, and the coefficients are arbitrary
linear maps to a commutative algebra. -/
theorem evaluate_convMul (X : RightComodule K C V) (φ ψ : WithConv (C →ₗ[K] A)) :
    X.evaluate (φ * ψ).ofConv = (X.evaluate φ.ofConv).comp (X.evaluate ψ.ofConv) := by
  let δ := (TensorProduct.comm K V C).toLinearMap.comp X.coaction
  let Δ := (TensorProduct.comm K C C).toLinearMap.comp (comul (R := K) (A := C))
  have hpair :
      (LinearMap.mul' K A).comp
          ((_root_.TensorProduct.map ψ.ofConv φ.ofConv).comp
            (TensorProduct.comm K C C).toLinearMap) =
        (LinearMap.mul' K A).comp (_root_.TensorProduct.map φ.ofConv ψ.ofConv) := by
    ext c d
    simp [mul_comm]
  have hcoeff :
      (LinearMap.mul' K A).comp ((_root_.TensorProduct.map ψ.ofConv φ.ofConv).comp Δ) =
        (φ * ψ).ofConv := by
    simpa only [Δ, LinearMap.convMul_def, ofConv_toConv, LinearMap.comp_assoc] using
      congrArg (fun f : C ⊗[K] C →ₗ[K] A ↦ f.comp (comul (R := K) (A := C))) hpair
  -- The weak left-coaction law applies φ after ψ. Its reversed coproduct
  -- pairs ψ with the second leg and φ with the first, giving φ * ψ.
  have h := TensorProduct.AlgebraTensorModule.lift_toSpanSingleton_comp_map_of_coassoc
    Δ δ ψ.ofConv φ.ofConv (commuted_coassoc X)
  rw [hcoeff] at h
  simpa only [TensorProduct.AlgebraTensorModule.lift_toSpanSingleton_eq_liftBaseChange,
    evaluate, δ, LinearMap.comp_assoc] using h.symm

/-- The convolution unit evaluates to the identity operator. -/
@[simp] theorem evaluate_convOne (X : RightComodule K C V) :
    X.evaluate (1 : WithConv (C →ₗ[K] A)).ofConv = 1 :=
  X.evaluate_counit

/-- Linear coefficient evaluation as a homomorphism from the existing
convolution monoid to the composition monoid of scalar-extended endomorphisms. -/
def evaluateMonoidHom (X : RightComodule K C V) :
    WithConv (C →ₗ[K] A) →* Module.End A (A ⊗[K] V) where
  toFun φ := X.evaluate φ.ofConv
  map_one' := X.evaluate_convOne
  map_mul' := X.evaluate_convMul

/-- The endomorphism underlying the evaluation homomorphism is evaluation
against the original coefficient map. -/
@[simp] theorem evaluateMonoidHom_apply (X : RightComodule K C V)
    (φ : WithConv (C →ₗ[K] A)) :
    X.evaluateMonoidHom φ = X.evaluate φ.ofConv := rfl

/-- The left-action order on arbitrary tensors, not just one-tensors. -/
theorem evaluate_convMul_apply (X : RightComodule K C V)
    (φ ψ : WithConv (C →ₗ[K] A)) (z : A ⊗[K] V) :
    X.evaluate (φ * ψ).ofConv z = X.evaluate φ.ofConv (X.evaluate ψ.ofConv z) :=
  LinearMap.congr_fun (X.evaluate_convMul φ ψ) z

end Coalgebra.RightComodule
