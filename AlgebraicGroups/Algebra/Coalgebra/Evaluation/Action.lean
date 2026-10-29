/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Evaluation.Convolution
public import AlgebraicGroups.Algebra.HopfAlgebra.Convolution
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The point action associated to a right coaction

A specified right coaction of a Hopf algebra `C` on `V` gives invertible
`A`-linear operators on `A ⊗[K] V` for every commutative coefficient algebra
`A`. The map `Coalgebra.RightComodule.pointAction` is a monoid homomorphism
from the existing convolution points to Mathlib's general linear group, the
units of the endomorphism monoid. It uses the named convolution group and
`MonoidHom.toHomUnits`; no inverse construction or global group instance is
added here. The source Hopf algebra need not be commutative, and the target
algebra needs no coalgebra structure.

The action is on the left: `T_(φ * ψ) = T_φ.comp T_ψ`. Its value on a
one-tensor is coefficient evaluation of the original right coaction, and its
inverse is evaluation after precomposition with the source antipode.
Coefficient change and colinear maps intertwine the operators. Image-stable
submodules have invariant scalar-extension images, in both directions.

## References

* The linear-coefficient evaluation and composition APIs in
  `AlgebraicGroups.Algebra.Coalgebra.Evaluation` and its convolution module.
* The named convolution group in `AlgebraicGroups.Algebra.HopfAlgebra.Convolution`.
* Johan Commelin, Chris Hughes and Kevin Buzzard, Mathlib,
  `Algebra/Group/Units/Hom`, for `MonoidHom.toHomUnits`.
* Johan Commelin, Mathlib, `LinearAlgebra/GeneralLinearGroup/Basic`, for
  `LinearMap.GeneralLinearGroup` and its linear-automorphism comparison.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the
  coaction/action construction (bibliographic credit).
-/

@[expose] public section

open scoped TensorProduct
open WithConv

universe u c v a b w

namespace Coalgebra.RightComodule

variable {K : Type u} {C : Type c} {V : Type v}
variable [CommSemiring K] [AddCommMonoid V] [Module K V]
variable {A : Type a} [CommSemiring A] [Algebra K A]

section Bialgebra

variable [Semiring C] [Bialgebra K C]

/-- Evaluation restricted to algebra-valued points of a bialgebra. The product
is the existing convolution product and the target product is composition. -/
def evaluateAlgHomMonoidHom (X : RightComodule K C V) :
    WithConv (C →ₐ[K] A) →* Module.End A (A ⊗[K] V) where
  toFun φ := X.evaluate φ.ofConv.toLinearMap
  map_one' := X.evaluate_counit
  map_mul' φ ψ := by
    change X.evaluate (φ * ψ).ofConv.toLinearMap =
      (X.evaluate φ.ofConv.toLinearMap).comp (X.evaluate ψ.ofConv.toLinearMap)
    calc
      _ = X.evaluate
          ((toConv φ.ofConv.toLinearMap * toConv ψ.ofConv.toLinearMap :
            WithConv (C →ₗ[K] A)).ofConv) :=
        congrArg X.evaluate (congrArg ofConv (AlgHom.toLinearMap_convMul φ ψ))
      _ = _ := (X.evaluateMonoidHom (A := A)).map_mul _ _

/-- Forgetting the point-evaluation homomorphism gives the original evaluation. -/
@[simp] theorem evaluateAlgHomMonoidHom_apply (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) :
    X.evaluateAlgHomMonoidHom φ = X.evaluate φ.ofConv.toLinearMap := rfl

/-- Algebra-valued points have the same left-action order as linear coefficients. -/
theorem evaluate_algHom_convMul (X : RightComodule K C V)
    (φ ψ : WithConv (C →ₐ[K] A)) :
    X.evaluate (φ * ψ).ofConv.toLinearMap =
      (X.evaluate φ.ofConv.toLinearMap).comp (X.evaluate ψ.ofConv.toLinearMap) :=
  (X.evaluateAlgHomMonoidHom (A := A)).map_mul φ ψ

end Bialgebra

section HopfAlgebra

variable [Semiring C] [HopfAlgebra K C]

/-- The left point action of a right comodule on its scalar extension. This
homomorphism takes values in Mathlib's units of the endomorphism monoid. -/
noncomputable def pointAction (X : RightComodule K C V) :
    WithConv (C →ₐ[K] A) →* LinearMap.GeneralLinearGroup A (A ⊗[K] V) := by
  letI := AlgHom.convolutionGroup K C A
  exact (X.evaluateAlgHomMonoidHom (A := A)).toHomUnits

/-- The underlying endomorphism of the point action is coefficient evaluation. -/
@[simp] theorem pointAction_val (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) :
    (X.pointAction φ).val = X.evaluate φ.ofConv.toLinearMap := rfl

/-- The inverse endomorphism uses the source antipode, with no target coalgebra. -/
theorem pointAction_inv_val (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) :
    (X.pointAction φ).inv = X.evaluate (AlgHom.convolutionInverse φ).ofConv.toLinearMap := rfl

/-- The underlying map of the inverse point action evaluates the source antipode. -/
@[simp] theorem pointAction_coe_inv (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) :
    (↑(X.pointAction φ)⁻¹ : Module.End A (A ⊗[K] V)) =
      X.evaluate (AlgHom.convolutionInverse φ).ofConv.toLinearMap := by
  simpa only [Units.inv_eq_val_inv] using X.pointAction_inv_val φ

/-- Evaluation at the counit point is the identity unit. -/
@[simp] theorem pointAction_one (X : RightComodule K C V) :
    X.pointAction (1 : WithConv (C →ₐ[K] A)) = 1 :=
  (X.pointAction (A := A)).map_one

/-- Point multiplication is operator multiplication, in left-action order. -/
theorem pointAction_mul (X : RightComodule K C V) (φ ψ : WithConv (C →ₐ[K] A)) :
    X.pointAction (φ * ψ) = X.pointAction φ * X.pointAction ψ :=
  (X.pointAction (A := A)).map_mul φ ψ

/-- The named convolution inverse maps to the inverse general-linear operator. -/
@[simp] theorem pointAction_convolutionInverse (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) :
    X.pointAction (AlgHom.convolutionInverse φ) = (X.pointAction φ)⁻¹ := by
  let := AlgHom.convolutionGroup K C A
  exact map_inv (X.pointAction (A := A)) φ

/-- Characteristic one-tensor formula, evaluated on the original right coaction. -/
theorem pointAction_one_tmul (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) (v : V) :
    (X.pointAction φ).val (1 ⊗ₜ[K] v) =
      _root_.TensorProduct.map φ.ofConv.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V C (X.coaction v)) :=
  X.evaluate_one_tmul φ.ofConv.toLinearMap v

/-- The inverse one-tensor formula reads back antipode precomposition. -/
theorem pointAction_inv_one_tmul (X : RightComodule K C V)
    (φ : WithConv (C →ₐ[K] A)) (v : V) :
    (X.pointAction φ).inv (1 ⊗ₜ[K] v) =
      _root_.TensorProduct.map (φ.ofConv.toLinearMap.comp (HopfAlgebra.antipode K))
        (LinearMap.id : V →ₗ[K] V) (TensorProduct.comm K V C (X.coaction v)) := by
  rw [pointAction_inv_val, AlgHom.toLinearMap_convolutionInverse]
  exact X.evaluate_one_tmul _ v

/-- On every tensor, the operator for `ψ` acts first in the product `φ * ψ`. -/
theorem pointAction_mul_apply (X : RightComodule K C V)
    (φ ψ : WithConv (C →ₐ[K] A)) (z : A ⊗[K] V) :
    (X.pointAction (φ * ψ)).val z = (X.pointAction φ).val ((X.pointAction ψ).val z) :=
  LinearMap.congr_fun (X.evaluate_algHom_convMul φ ψ) z

/-- The point action commutes with every change of coefficient algebra. The
comparison map is only `K`-linear; no action of one algebra on the other is chosen. -/
theorem pointAction_naturality (X : RightComodule K C V)
    {B : Type b} [CommSemiring B] [Algebra K B] (q : A →ₐ[K] B)
    (φ : WithConv (C →ₐ[K] A)) :
    (_root_.TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
        ((X.pointAction φ).val.restrictScalars K) =
      ((X.pointAction (AlgHom.convolutionPostcomp q φ)).val.restrictScalars K).comp
        (_root_.TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)) := by
  simpa only [pointAction_val, AlgHom.convolutionPostcomp_ofConv, AlgHom.comp_toLinearMap]
    using X.evaluate_naturality φ.ofConv.toLinearMap q

/-- A stable submodule has invariant scalar-extension image under every point,
including the inverse operator. No injectivity of the tensor inclusion is needed. -/
theorem IsStable.pointAction_mem_baseChange_iff {X : RightComodule K C V}
    {U : Submodule K V} (hU : X.IsStable U) (φ : WithConv (C →ₐ[K] A))
    (z : A ⊗[K] V) :
    (X.pointAction φ).val z ∈ U.baseChange A ↔ z ∈ U.baseChange A := by
  constructor
  · intro hz
    have hinv := hU.evaluate_mem_baseChange
      (AlgHom.convolutionInverse φ).ofConv.toLinearMap hz
    rw [← pointAction_inv_val] at hinv
    have hcancel := LinearMap.congr_fun (X.pointAction φ).inv_val z
    change (X.pointAction φ).inv ((X.pointAction φ).val z) = z at hcancel
    rwa [hcancel] at hinv
  · exact hU.evaluate_mem_baseChange φ.ofConv.toLinearMap

end HopfAlgebra

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

variable {K : Type u} {C : Type c} {V : Type v} {W : Type w}
variable [CommSemiring K] [Semiring C] [HopfAlgebra K C]
variable [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
variable {A : Type a} [CommSemiring A] [Algebra K A]
variable {X : RightComodule K C V} {Y : RightComodule K C W}

/-- The scalar extension of a colinear map intertwines the associated point actions. -/
theorem baseChange_comp_pointAction (l : RightComoduleHom X Y)
    (φ : WithConv (C →ₐ[K] A)) :
    l.toLinearMap.baseChange A ∘ₗ (X.pointAction φ).val =
      (Y.pointAction φ).val ∘ₗ l.toLinearMap.baseChange A :=
  l.baseChange_comp_evaluate φ.ofConv.toLinearMap

end Coalgebra.RightComoduleHom
