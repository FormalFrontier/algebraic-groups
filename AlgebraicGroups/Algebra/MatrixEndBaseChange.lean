/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Source-order tensors and endomorphism base change

The usual scalar extension of `V` is `R ⊗[K] V`. We use this canonical
`R`-module while recording explicitly the comparison with `V ⊗[K] R`.
-/

public section

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (R : Type u) [CommRing R] [Algebra K R]

/-- The `R`-module denoted by `V ⊗[K] R` in source-order notation; its
underlying implementation is the canonically scalar-extended module `R ⊗[K] V`. -/
abbrev SourceOrderTensor : Type u := R ⊗[K] V

/-- Comparison from source-order tensors to the canonical scalar extension. -/
@[expose] def sourceOrderTensorEquiv : (V ⊗[K] R) ≃ₗ[K] SourceOrderTensor K V R :=
  TensorProduct.comm K V R

@[simp]
theorem sourceOrderTensorEquiv_tmul (v : V) (r : R) :
    sourceOrderTensorEquiv K V R (v ⊗ₜ[K] r) = r ⊗ₜ[K] v := rfl

/-- Multiplication on the right coefficient is the transported scalar action. -/
theorem sourceOrderTensor_smul_tmul (v : V) (r s : R) :
    r • sourceOrderTensorEquiv K V R (v ⊗ₜ[K] s) =
      sourceOrderTensorEquiv K V R (v ⊗ₜ[K] (r * s)) := by
  simp [sourceOrderTensorEquiv, TensorProduct.smul_tmul']

/-- A separate type carries the scalar structure transported to the literal
source-order tensor product. It creates no module instance on `V ⊗[K] R`. -/
structure SourceOrderedTensor where
  /-- The literal tensor with the coefficient algebra on the right. -/
  tensor : V ⊗[K] R

/-- Forget the wrapper around the source-order tensor product. -/
@[expose] def sourceOrderedEquiv : SourceOrderedTensor K V R ≃ V ⊗[K] R where
  toFun := SourceOrderedTensor.tensor
  invFun := SourceOrderedTensor.mk
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by intro x; rfl

instance sourceOrderedAddCommGroup : AddCommGroup (SourceOrderedTensor K V R) :=
  (sourceOrderedEquiv K V R).addCommGroup

/-- The transported additive comparison to the canonical scalar extension. -/
@[expose] def sourceOrderedCanonicalAddEquiv : SourceOrderedTensor K V R ≃+
    SourceOrderTensor K V R :=
  { (sourceOrderedEquiv K V R).trans (TensorProduct.comm K V R).toEquiv with
    map_add' := by
      intro x y
      exact (TensorProduct.comm K V R).map_add x.tensor y.tensor }

instance sourceOrderedModule : Module R (SourceOrderedTensor K V R) :=
  (sourceOrderedCanonicalAddEquiv K V R).module R

/-- The source-order scalar extension is `R`-linearly equivalent to `R ⊗ V`. -/
@[expose] def sourceOrderedCanonicalLinearEquiv : SourceOrderedTensor K V R ≃ₗ[R]
    SourceOrderTensor K V R :=
  { sourceOrderedCanonicalAddEquiv K V R with
    map_smul' := by
      intro r x
      change (sourceOrderedCanonicalAddEquiv K V R) (r • x) =
        r • (sourceOrderedCanonicalAddEquiv K V R) x
      rw [Equiv.smul_def (sourceOrderedCanonicalAddEquiv K V R).toEquiv]
      simp }

/-- Pure tensors in the separate transported module. -/
@[expose] def sourceOrderedTmul (v : V) (s : R) : SourceOrderedTensor K V R :=
  ⟨v ⊗ₜ[K] s⟩

@[simp]
theorem sourceOrderedCanonicalLinearEquiv_tmul (v : V) (s : R) :
    sourceOrderedCanonicalLinearEquiv K V R (sourceOrderedTmul K V R v s) =
      s ⊗ₜ[K] v := rfl

@[simp]
theorem sourceOrderedTmul_smul (v : V) (r s : R) :
    r • sourceOrderedTmul K V R v s = sourceOrderedTmul K V R v (r * s) := by
  apply (sourceOrderedCanonicalLinearEquiv K V R).injective
  simp only [map_smul, sourceOrderedCanonicalLinearEquiv_tmul]
  change (r * s) ⊗ₜ[K] v = (r * s) ⊗ₜ[K] v
  rfl

/-- Endomorphisms of the transported source-order module match the canonical
endomorphism model by conjugating the explicit `R`-linear comparison. -/
@[expose] def sourceOrderedEndEquiv : Module.End R (SourceOrderedTensor K V R) ≃ₗ[R]
    Module.End R (SourceOrderTensor K V R) :=
  (sourceOrderedCanonicalLinearEquiv K V R).conj

@[simp]
theorem sourceOrderedEndEquiv_apply (f : Module.End R (SourceOrderedTensor K V R))
    (x : SourceOrderedTensor K V R) :
    sourceOrderedEndEquiv K V R f (sourceOrderedCanonicalLinearEquiv K V R x) =
      sourceOrderedCanonicalLinearEquiv K V R (f x) := by
  simp [sourceOrderedEndEquiv, LinearEquiv.conj_apply_apply]

/-- Scalar extension of endomorphisms along any algebra map, including non-flat maps. -/
@[expose] def endBaseChange (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderTensor K V R)) :
    Module.End S (SourceOrderTensor K V S) :=
  letI : Algebra R S := g.toRingHom.toAlgebra
  (AlgebraTensorModule.cancelBaseChange K R S S V).toLinearMap.comp
    ((f.baseChange S).comp
      (AlgebraTensorModule.cancelBaseChange K R S S V).symm.toLinearMap)

/-- Readback of the canonical cancellation at every tensor, including sums. -/
theorem cancelBaseChange_apply (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (s : S) (x : R ⊗[K] V) :
    letI : Algebra R S := g.toRingHom.toAlgebra
    (AlgebraTensorModule.cancelBaseChange K R S S V) (s ⊗ₜ[R] x) =
      s • (g.toLinearMap.rTensor V) x := by
  let : Algebra R S := g.toRingHom.toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul]
    change (r • s) ⊗ₜ[K] v = s • (g r ⊗ₜ[K] v)
    simp only [TensorProduct.smul_tmul']
    change (g r * s) ⊗ₜ[K] v = (s * g r) ⊗ₜ[K] v
    rw [mul_comm]
  | add x y hx hy =>
    simpa only [tmul_add, map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- An extended endomorphism acts on pure tensors by transporting its value at
`1 ⊗ v`, and hence also specifies its action on arbitrary tensor sums. -/
@[simp]
theorem endBaseChange_tmul (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderTensor K V R))
    (s : S) (v : V) :
    endBaseChange K V R S g f (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] v)) := by
  let : Algebra R S := g.toRingHom.toAlgebra
  change (AlgebraTensorModule.cancelBaseChange K R S S V)
      ((f.baseChange S) ((AlgebraTensorModule.cancelBaseChange K R S S V).symm
        (s ⊗ₜ[K] v))) = _
  rw [AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]
  exact cancelBaseChange_apply K V R S g s (f (1 ⊗ₜ[K] v))

/-- The base-change map preserves the additive group of endomorphisms. -/
@[expose] def endBaseChangeAddHom (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) : Module.End R (SourceOrderTensor K V R) →+
      Module.End S (SourceOrderTensor K V S) where
  toFun := endBaseChange K V R S g
  map_zero' := by
    ext x
    simp [endBaseChange]
  map_add' f h := by
    ext x
    simp [endBaseChange]

@[simp]
theorem endBaseChange_id (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V R R (AlgHom.id K R) f = f := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    rw [endBaseChange_tmul]
    change r • ((LinearMap.id : R →ₗ[K] R).rTensor V)
        (f (1 ⊗ₜ[K] v)) = f (r ⊗ₜ[K] v)
    rw [LinearMap.rTensor_id, LinearMap.id_apply]
    conv_rhs => rw [TensorProduct.tmul_eq_smul_one_tmul r v]
    exact (f.map_smul r (1 ⊗ₜ[K] v)).symm
  | add x y hx hy =>
    simp only [map_add, hx, hy]

@[simp]
theorem endBaseChange_comp (S T : Type u) [CommRing S] [Algebra K S]
    [CommRing T] [Algebra K T] (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V S T h (endBaseChange K V R S g f) =
      endBaseChange K V R T (h.comp g) f := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t v =>
    simp only [endBaseChange_tmul]
    simp only [one_smul]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]

end AlgebraicGeometry

#lint
