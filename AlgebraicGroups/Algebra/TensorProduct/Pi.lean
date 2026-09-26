/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Tensor products and arbitrary products

This file proves that the canonical map from a tensor product to a product of tensor products is
injective when the tensor factor is free. It then applies this to arbitrary families of
scalar-valued algebra homomorphisms under scalar extension, and derives geometric reducedness
from such a jointly injective family over a field.

## Main results

- `TensorProduct.piScalarRightHom_injective_of_free`
- `Algebra.TensorProduct.baseChangeEvaluation`
- `Algebra.TensorProduct.pi_baseChangeEvaluation_injective_of_free`
- `Algebra.IsGeometricallyReduced.of_joint_evaluations`
- `Algebra.IsGeometricallyReduced.of_iInf_eval_ker_eq_bot`
-/

public section

noncomputable section

universe uR uS uI uA

namespace TensorProduct

variable (R : Type uR) (S : Type uS) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (I : Type uI)

private lemma equivFinsuppOfBasisLeft_apply_piScalarRightHom
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R S)
    (z : S ⊗[R] (I → R)) (j : ι) (i : I) :
    (equivFinsuppOfBasisLeft b z j) i = b.coord j (piScalarRightHom R S S I z i) := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul x f => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- If `S` is free as an `R`-module, the canonical map
`S ⊗[R] (I → R) →ₗ[S] (I → S)` is injective, even when `I` is infinite. -/
theorem piScalarRightHom_injective_of_free [Module.Free R S] :
    Function.Injective (piScalarRightHom R S S I) := by
  let b := Module.Free.chooseBasis R S
  intro x y hxy
  apply (equivFinsuppOfBasisLeft b).injective
  ext j i
  rw [equivFinsuppOfBasisLeft_apply_piScalarRightHom,
    equivFinsuppOfBasisLeft_apply_piScalarRightHom]
  exact congrArg (fun f : I → S ↦ b.coord j (f i)) hxy

end TensorProduct

namespace Algebra.TensorProduct

variable (R : Type uR) (S : Type uS) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Extend a scalar-valued `R`-algebra homomorphism to `S` after base change. -/
def baseChangeEvaluation {A : Type uA} [CommSemiring A] [Algebra R A]
    (f : A →ₐ[R] R) : AlgHom S (TensorProduct R S A) S :=
  (Algebra.TensorProduct.rid R S S).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id S S) f)

variable (I : Type uI)

private lemma pi_baseChangeEvaluation_eq
    {A : Type uA} [CommSemiring A] [Algebra R A] (f : I → A →ₐ[R] R) :
    (AlgHom.pi (fun i ↦ baseChangeEvaluation R S (f i))).toLinearMap =
      (TensorProduct.piScalarRightHom R S S I).comp
        (map (AlgHom.id S S) (AlgHom.pi f)).toLinearMap := by
  ext x a
  simp [baseChangeEvaluation]

/-- Joint injectivity of a family of scalar-valued algebra homomorphisms is preserved by a free
scalar extension. No finiteness assumption on the index type is needed. -/
theorem pi_baseChangeEvaluation_injective_of_free
    {A : Type uA} [CommSemiring A] [Algebra R A] (f : I → A →ₐ[R] R)
    [Module.Free R S] (hf : Function.Injective (AlgHom.pi f)) :
    Function.Injective (AlgHom.pi (fun i ↦ baseChangeEvaluation R S (f i))) := by
  have hmap : Function.Injective (map (AlgHom.id S S) (AlgHom.pi f)) := by
    let _ : Module.Flat R S := Module.Flat.of_free
    have heq :
        (map (AlgHom.id S S) (AlgHom.pi f)).toLinearMap.restrictScalars R =
          LinearMap.lTensor S (AlgHom.pi f).toLinearMap := by
      ext x a
      simp
    intro x y hxy
    apply Module.Flat.lTensor_preserves_injective_linearMap (AlgHom.pi f).toLinearMap hf
    rw [← heq]
    exact hxy
  intro x y hxy
  apply hmap
  apply TensorProduct.piScalarRightHom_injective_of_free R S I
  change (TensorProduct.piScalarRightHom R S S I)
      ((map (AlgHom.id S S) (AlgHom.pi f)).toLinearMap x) =
    (TensorProduct.piScalarRightHom R S S I)
      ((map (AlgHom.id S S) (AlgHom.pi f)).toLinearMap y)
  change (AlgHom.pi (fun i ↦ baseChangeEvaluation R S (f i))).toLinearMap x =
    (AlgHom.pi (fun i ↦ baseChangeEvaluation R S (f i))).toLinearMap y at hxy
  exact (LinearMap.congr_fun (pi_baseChangeEvaluation_eq R S I f) x).symm.trans <|
    hxy.trans (LinearMap.congr_fun (pi_baseChangeEvaluation_eq R S I f) y)

end Algebra.TensorProduct

namespace Algebra.IsGeometricallyReduced

variable (k : Type uR) [Field k]
variable (I : Type uI) (A : Type uA) [CommRing A] [Algebra k A]

/-- A commutative algebra over a field is geometrically reduced if a family of algebra
homomorphisms back to the field is jointly injective. -/
theorem of_joint_evaluations (f : I → A →ₐ[k] k) (hf : Function.Injective (AlgHom.pi f)) :
    IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_injective
    (AlgHom.pi (fun i ↦ Algebra.TensorProduct.baseChangeEvaluation
      k (AlgebraicClosure k) (f i)))
    (Algebra.TensorProduct.pi_baseChangeEvaluation_injective_of_free
      k (AlgebraicClosure k) I f hf)

/-- A commutative algebra over a field is geometrically reduced if the intersection of the
kernels of a family of algebra homomorphisms back to the field is zero. -/
theorem of_iInf_eval_ker_eq_bot (f : I → A →ₐ[k] k)
    (hf : (⨅ i, RingHom.ker (f i).toRingHom) = ⊥) : IsGeometricallyReduced k A := by
  apply of_joint_evaluations k I A f
  rw [RingHom.injective_iff_ker_eq_bot]
  change RingHom.ker (RingHom.pi fun i ↦ (f i).toRingHom) = ⊥
  rwa [Pi.ker_ringHom]

end Algebra.IsGeometricallyReduced
