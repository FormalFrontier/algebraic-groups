/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import ProjectiveModules.Dual.TensorProduct

/-!
# Dual evaluation and right Hopf-module compatibility

For a projective Hopf algebra, evaluation detects equality in the tensor product
of its scalar dual with the algebra. Consequently a specified coaction on that
dual, together with a given right action, is a right Hopf module if their
functional formulas are right translation and antipode-twisted evaluation.

The action, scalar tower and coaction are supplied, not constructed. In
particular this criterion does not assert that the full dual of every infinite
projective Hopf algebra admits such a coaction. No finite generation or inverse
antipode is used.

## References

The proof uses the standard antipode identities from Hopf algebra theory,
formalized in Mathlib, and the projective tensor equality-separation theorem
from ProjectiveModules. The compatibility convention is the ordered right
Hopf-module convention of `HopfModule.Basic`.
-/

@[expose] public section

universe uR uH

open scoped TensorProduct RingTheory.LinearMap
open WithConv

namespace Coalgebra.RightComodule

/-- Functional right translation and antipode-twisted evaluation imply right
Hopf-module compatibility for the specified coaction on the original scalar dual.
Only projectivity of the Hopf algebra is needed: evaluations separate tensors by
ProjectiveModules' projective-right equality criterion. The antipode calculation
uses Mathlib's antimultiplicativity and convolution cancellation identities. -/
theorem isHopfModule_of_dual_eval
    {R : Type uR} {H : Type uH}
    [CommSemiring R] [Semiring H] [HopfAlgebra R H]
    [Module.Projective R H]
    [Module Hᵐᵒᵖ (Module.Dual R H)]
    [IsScalarTower R Hᵐᵒᵖ (Module.Dual R H)]
    (X : RightComodule R H (Module.Dual R H))
    (hact : ∀ (h : H) (φ : Module.Dual R H) (x : H),
      (MulOpposite.op h • φ) x = φ (h * x))
    (hρ : ∀ (φ : Module.Dual R H) (x : H),
      _root_.TensorProduct.map (Module.Dual.eval R H x)
          (LinearMap.id : H →ₗ[R] H) (X.coaction φ) =
        _root_.TensorProduct.map φ (HopfAlgebra.antipode R)
          (Coalgebra.comul (R := R) x)) :
    X.IsHopfModule := by
  apply X.isHopfModule_of_coaction_smul
  intro φ h
  apply (_root_.TensorProduct.forall_map_id_right_apply_eq_iff_of_projective
    (R := R) (P := H) (A := Module.Dual R H) (I := H) (B := fun _ : H => R)
    (fun x : H => Module.Dual.eval R H x)
    (fun ψ χ heq => LinearMap.ext fun x => by
      simpa only [Module.Dual.eval_apply] using heq x) _ _).mp
  intro x
  apply (_root_.TensorProduct.lid R H).injective
  let E (y : H) : Module.Dual R H ⊗[R] H →ₗ[R] H :=
    (_root_.TensorProduct.lid R H).toLinearMap ∘ₗ
      _root_.TensorProduct.map (Module.Dual.eval R H y) (LinearMap.id : H →ₗ[R] H)
  let F (u : H ⊗[R] H) : H →ₗ[R] H :=
    { toFun := fun a => _root_.TensorProduct.lid R H
        (_root_.TensorProduct.map (φ ∘ₗ LinearMap.mul R H a)
          (HopfAlgebra.antipode R) u)
      map_add' := by
        intro a b
        have hadd : φ ∘ₗ LinearMap.mul R H (a + b) =
            (φ ∘ₗ LinearMap.mul R H a) + (φ ∘ₗ LinearMap.mul R H b) := by
          apply LinearMap.ext
          intro y
          simp
        rw [hadd, _root_.TensorProduct.map_add_left]
        simp
      map_smul' := by
        intro r a
        have hsmul : φ ∘ₗ LinearMap.mul R H (r • a) =
            r • (φ ∘ₗ LinearMap.mul R H a) := by
          apply LinearMap.ext
          intro y
          simp
        rw [hsmul, _root_.TensorProduct.map_smul_left]
        simp }
  let L : H →ₗ[R] H := F (Coalgebra.comul (R := R) x)
  let K : H →ₗ[R] H :=
    { toFun := fun a => E (a * x) (X.coaction φ)
      map_add' := by
        intro a b
        simp [E, add_mul, _root_.TensorProduct.map_add_left]
      map_smul' := by
        intro r a
        simp [E, _root_.TensorProduct.map_smul_left] }
  -- Antimultiplicativity retains the order S(d) * S(b).
  have hproduct (t u : H ⊗[R] H) :
      _root_.TensorProduct.lid R H
          (_root_.TensorProduct.map φ (HopfAlgebra.antipode R) (t * u)) =
        LinearMap.mul' R H
          (_root_.TensorProduct.map (F u) (HopfAlgebra.antipode R) t) := by
    have ht :
        (_root_.TensorProduct.lid R H).toLinearMap ∘ₗ
            _root_.TensorProduct.map φ (HopfAlgebra.antipode R) ∘ₗ
              (LinearMap.mul R (H ⊗[R] H)).flip u =
          LinearMap.mul' R H ∘ₗ
            _root_.TensorProduct.map (F u) (HopfAlgebra.antipode R) := by
      apply _root_.TensorProduct.ext'
      intro a b
      have hu :
          (_root_.TensorProduct.lid R H).toLinearMap ∘ₗ
              _root_.TensorProduct.map φ (HopfAlgebra.antipode R) ∘ₗ
                LinearMap.mul R (H ⊗[R] H) (a ⊗ₜ[R] b) =
            (LinearMap.mul R H).flip (HopfAlgebra.antipode R b) ∘ₗ
              (_root_.TensorProduct.lid R H).toLinearMap ∘ₗ
                _root_.TensorProduct.map (φ ∘ₗ LinearMap.mul R H a)
                  (HopfAlgebra.antipode R) := by
        apply _root_.TensorProduct.ext'
        intro c d
        simp [Algebra.TensorProduct.tmul_mul_tmul,
          HopfAlgebra.antipode_mul_antidistrib]
      simpa [F] using LinearMap.congr_fun hu u
    exact LinearMap.congr_fun ht t
  have hKL :
      toConv K = toConv L * toConv (HopfAlgebra.antipode R : H →ₗ[R] H) := by
    rw [LinearMap.convMul_def]
    congr 1
    apply LinearMap.ext
    intro a
    have hmul : Coalgebra.comul (R := R) (a * x) =
        Coalgebra.comul (R := R) a * Coalgebra.comul (R := R) x := by
      simpa only [← Bialgebra.toLinearMap_comulAlgHom, AlgHom.toLinearMap_apply] using
        map_mul (Bialgebra.comulAlgHom R H) a x
    calc
      K a = _root_.TensorProduct.lid R H
          (_root_.TensorProduct.map φ (HopfAlgebra.antipode R)
            (Coalgebra.comul (R := R) (a * x))) := by
        exact congrArg (_root_.TensorProduct.lid R H) (hρ φ (a * x))
      _ = LinearMap.mul' R H
          (_root_.TensorProduct.map L (HopfAlgebra.antipode R)
            (Coalgebra.comul (R := R) a)) := by
        rw [hmul]
        exact hproduct _ _
      _ = _ := rfl
  -- Convolution cancellation uses S * id, not an inverse of S under composition.
  have hS :
      toConv (HopfAlgebra.antipode R : H →ₗ[R] H) *
          toConv (LinearMap.id : H →ₗ[R] H) = 1 := by
    rw [LinearMap.convMul_def, LinearMap.convOne_def]
    congr 1
    apply LinearMap.ext
    intro a
    have hmap : _root_.TensorProduct.map (HopfAlgebra.antipode R)
          (LinearMap.id : H →ₗ[R] H) =
        (HopfAlgebra.antipode R : H →ₗ[R] H).rTensor H := by
      apply _root_.TensorProduct.ext'
      intro b c
      simp
    simpa only [LinearMap.comp_apply, hmap, Algebra.linearMap_apply] using
      HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) a
  have hKI : toConv K * toConv (LinearMap.id : H →ₗ[R] H) = toConv L := by
    rw [hKL, mul_assoc, hS, mul_one]
  have hleft : E x (X.coaction (MulOpposite.op h • φ)) = L h := by
    have hφ : MulOpposite.op h • φ = φ ∘ₗ LinearMap.mul R H h := by
      apply LinearMap.ext
      intro y
      simpa only [LinearMap.comp_apply, LinearMap.mul_apply'] using hact h φ y
    simpa [hφ, E, L, F] using
      congrArg (_root_.TensorProduct.lid R H)
      (hρ (MulOpposite.op h • φ) x)
  -- Evaluation of the ordered compatibility diagram is K * id.
  let i : H ⊗[R] H →ₗ[R]
      (Module.Dual R H ⊗[R] H) ⊗[R] (H ⊗[R] H) :=
    _root_.TensorProduct.mk R _ _ (X.coaction φ)
  have hdiagram :
      E x ∘ₗ _root_.TensorProduct.map
          (_root_.TensorProduct.rightAction R H (Module.Dual R H)) (LinearMap.mul' R H) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R
            (Module.Dual R H) H H H).toLinearMap ∘ₗ i =
        LinearMap.mul' R H ∘ₗ _root_.TensorProduct.map K (LinearMap.id : H →ₗ[R] H) := by
    apply _root_.TensorProduct.ext'
    intro a b
    let j : Module.Dual R H ⊗[R] H →ₗ[R]
        (Module.Dual R H ⊗[R] H) ⊗[R] (H ⊗[R] H) :=
      (_root_.TensorProduct.mk R _ _).flip (a ⊗ₜ[R] b)
    have ht :
        E x ∘ₗ _root_.TensorProduct.map
            (_root_.TensorProduct.rightAction R H (Module.Dual R H)) (LinearMap.mul' R H) ∘ₗ
            (_root_.TensorProduct.tensorTensorTensorComm R
              (Module.Dual R H) H H H).toLinearMap ∘ₗ j =
          (LinearMap.mul R H).flip b ∘ₗ E (a * x) := by
      apply _root_.TensorProduct.ext'
      intro ψ c
      simp [E, j, _root_.TensorProduct.tensorTensorTensorComm_tmul, hact]
    simpa [i, j, K] using LinearMap.congr_fun ht (X.coaction φ)
  change E x (X.coaction (MulOpposite.op h • φ)) =
    E x (_root_.TensorProduct.map
      (_root_.TensorProduct.rightAction R H (Module.Dual R H)) (LinearMap.mul' R H)
      (_root_.TensorProduct.tensorTensorTensorComm R (Module.Dual R H) H H H
        (X.coaction φ ⊗ₜ[R] Coalgebra.comul (R := R) h)))
  rw [hleft]
  have hright := LinearMap.congr_fun hdiagram (Coalgebra.comul (R := R) h)
  have hcancel := congrArg (fun f : WithConv (H →ₗ[R] H) => f h) hKI
  simpa only [LinearMap.comp_apply, i, _root_.TensorProduct.mk_apply,
    LinearEquiv.coe_coe, LinearMap.convMul_apply] using
    (hright.trans hcancel).symm

end Coalgebra.RightComodule
