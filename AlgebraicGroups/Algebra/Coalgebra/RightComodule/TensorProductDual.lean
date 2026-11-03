/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Duality
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Reversed tensor comparison for dual right comodules

The tensor product of two right comodules over the same Hopf algebra is obtained
by transporting the external tensor product along the multiplication coalgebra
homomorphism. The tensor of the duals, in reversed order, maps isomorphically to
the dual of this tensor product. Its underlying linear equivalence is the tensor
swap followed by `TensorProduct.dualDistribEquiv`.

Colinearity follows from contraction against the original coactions and the
anti-multiplicativity of the antipode. The inverse is colinear because it is the
inverse of the same linear equivalence.

## References

The underlying linear equivalence is Mathlib's `TensorProduct.dualDistribEquiv`.
The coaction proof uses the contraction characterization from
`AlgebraicGroups.Algebra.Coalgebra.RightComodule.Duality`.
-/

@[expose] public section

open TensorProduct

universe uR uC uV uW uV2 uW2

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

section Contraction

variable [Semiring C] [Algebra R C]

/-- Contracting a tensor covector after shuffling and multiplying the coefficient
factors is the product of the two contractions. -/
private theorem dualContraction_dualDistrib_mul_shuffle
    (f : Module.Dual R V) (g : Module.Dual R W)
    (t : V ⊗[R] C) (z : W ⊗[R] C) :
    dualContraction (C := C) (_root_.TensorProduct.dualDistrib R V W (f ⊗ₜ[R] g))
        ((LinearMap.mul' R C).lTensor (V ⊗[R] W)
          (_root_.TensorProduct.tensorTensorTensorComm R V C W C (t ⊗ₜ[R] z))) =
      dualContraction (C := C) f t * dualContraction (C := C) g z := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul v c =>
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w d =>
      simp only [tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul,
        LinearMap.mul'_apply, dualContraction_tmul, dualDistrib_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
      exact congrArg (fun r : R => r • (c * d)) (mul_comm (f v) (g w))
    | add z z' hz hz' =>
      simp [_root_.TensorProduct.tmul_add, hz, hz', mul_add]
  | add t t' ht ht' =>
    simp [_root_.TensorProduct.add_tmul, ht, ht', add_mul]

end Contraction

variable [Semiring C] [HopfAlgebra R C]
variable [Module.Finite R V] [Module.Projective R V]
variable [Module.Finite R W] [Module.Projective R W]

/-- The reversed tensor of dual right comodules maps to the dual of their tensor. -/
noncomputable def tensorDual (X : Coalgebra.RightComodule R C V)
    (Y : Coalgebra.RightComodule R C W) :
    Coalgebra.RightComoduleHom
      ((externalTensor (dual Y) (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C))
      (dual ((externalTensor X Y).mapCoalgebra (Bialgebra.mulCoalgHom R C))) := by
  let e := (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
    (_root_.TensorProduct.dualDistribEquiv R V W)
  refine { toLinearMap := e.toLinearMap, colinear := ?_ }
  let A := (externalTensor (dual Y) (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)
  let T := (externalTensor X Y).mapCoalgebra (Bialgebra.mulCoalgHom R C)
  have he : e.toLinearMap = _root_.TensorProduct.dualDistrib R V W ∘ₗ
      (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).toLinearMap := by
    change (_root_.TensorProduct.dualDistribEquiv R V W).toLinearMap ∘ₗ
      (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).toLinearMap = _
    rw [_root_.TensorProduct.toLinearMap_dualDistribEquiv]
  have he_tmul (g : Module.Dual R W) (f : Module.Dual R V) :
      e (g ⊗ₜ[R] f) = _root_.TensorProduct.dualDistrib R V W (f ⊗ₜ[R] g) := by
    change e.toLinearMap (g ⊗ₜ[R] f) = _
    rw [he]
    simp
  ext g f
  change dualCoaction T (e (g ⊗ₜ[R] f)) =
    e.toLinearMap.rTensor C (A.coaction (g ⊗ₜ[R] f))
  symm
  apply (eq_dualCoaction_iff T _ _).2
  intro z
  induction z using _root_.TensorProduct.inductionOn with
  | tmul v w =>
    have hpull :
        e.toLinearMap.dualMap (Module.Dual.eval R (V ⊗[R] W) (v ⊗ₜ[R] w)) =
          _root_.TensorProduct.dualDistrib R (Module.Dual R W) (Module.Dual R V)
            (Module.Dual.eval R W w ⊗ₜ[R] Module.Dual.eval R V v) := by
      ext g' f'
      simp [e]
    calc
      dualTensorHom R (V ⊗[R] W) C
          (e.toLinearMap.rTensor C (A.coaction (g ⊗ₜ[R] f))) (v ⊗ₜ[R] w) =
          dualContraction (C := C)
            (e.toLinearMap.dualMap (Module.Dual.eval R (V ⊗[R] W) (v ⊗ₜ[R] w)))
            (A.coaction (g ⊗ₜ[R] f)) := by
        rw [dualContraction_dualMap]
        exact (dualContraction_eval (v ⊗ₜ[R] w) _).symm
      _ = HopfAlgebra.antipode R (A := C) (dualContraction g (Y.coaction w)) *
          HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v)) := by
        rw [hpull]
        change dualContraction (C := C)
            (_root_.TensorProduct.dualDistrib R (Module.Dual R W) (Module.Dual R V)
              (Module.Dual.eval R W w ⊗ₜ[R] Module.Dual.eval R V v))
            ((LinearMap.mul' R C).lTensor (Module.Dual R W ⊗[R] Module.Dual R V)
              (_root_.TensorProduct.tensorTensorTensorComm R (Module.Dual R W) C
                (Module.Dual R V) C (dualCoaction Y g ⊗ₜ[R] dualCoaction X f))) = _
        rw [dualContraction_dualDistrib_mul_shuffle,
          dualContraction_eval, dualContraction_eval,
          dualCoaction_characteristic, dualCoaction_characteristic]
      _ = HopfAlgebra.antipode R (A := C)
          (dualContraction (e (g ⊗ₜ[R] f)) (T.coaction (v ⊗ₜ[R] w))) := by
        rw [he_tmul]
        change HopfAlgebra.antipode R (A := C) (dualContraction g (Y.coaction w)) *
            HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v)) =
          HopfAlgebra.antipode R (A := C)
            (dualContraction (_root_.TensorProduct.dualDistrib R V W (f ⊗ₜ[R] g))
              ((LinearMap.mul' R C).lTensor (V ⊗[R] W)
                (_root_.TensorProduct.tensorTensorTensorComm R V C W C
                  (X.coaction v ⊗ₜ[R] Y.coaction w))))
        rw [dualContraction_dualDistrib_mul_shuffle,
          HopfAlgebra.antipode_mul_antidistrib]
  | add z z' hz hz' =>
    simp only [map_add, hz, hz']

variable (X : Coalgebra.RightComodule R C V) (Y : Coalgebra.RightComodule R C W)

/-- The underlying linear map is the tensor-dual equivalence after a swap. -/
theorem tensorDual_toLinearMap :
    (tensorDual X Y).toLinearMap =
      ((_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
        (_root_.TensorProduct.dualDistribEquiv R V W)).toLinearMap := rfl

/-- A pure reversed tensor is sent to the tensor covector in the original order. -/
@[simp] theorem tensorDual_apply_tmul (g : Module.Dual R W) (f : Module.Dual R V) :
    tensorDual X Y (g ⊗ₜ[R] f) =
      _root_.TensorProduct.dualDistribEquiv R V W (f ⊗ₜ[R] g) := by
  change _root_.TensorProduct.dualDistribEquiv R V W
    (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V) (g ⊗ₜ[R] f)) = _
  rw [_root_.TensorProduct.comm_tmul]

/-- The comparison evaluates a reversed tensor of covectors on a pure tensor. -/
theorem tensorDual_apply_tmul_tmul (g : Module.Dual R W)
    (f : Module.Dual R V) (v : V) (w : W) :
    tensorDual X Y (g ⊗ₜ[R] f) (v ⊗ₜ[R] w) = f v * g w := by
  rw [tensorDual_apply_tmul, _root_.TensorProduct.dualDistribEquiv_tmul_tmul]
  exact mul_comm (g w) (f v)

/-- Values on pure covectors and pure vectors characterize the comparison. -/
theorem tensorDual_unique
    (T : Coalgebra.RightComoduleHom
      ((externalTensor (dual Y) (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C))
      (dual ((externalTensor X Y).mapCoalgebra (Bialgebra.mulCoalgHom R C))))
    (hT : ∀ (g : Module.Dual R W) (f : Module.Dual R V) (v : V) (w : W),
      T (g ⊗ₜ[R] f) (v ⊗ₜ[R] w) = f v * g w) :
    T = tensorDual X Y := by
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  apply _root_.TensorProduct.ext'
  intro g f
  apply _root_.TensorProduct.ext'
  intro v w
  exact (hT g f v w).trans (tensorDual_apply_tmul_tmul X Y g f v w).symm

/-- The inverse comparison is a right-comodule homomorphism. -/
noncomputable def tensorDualInv :
    Coalgebra.RightComoduleHom
      (dual ((externalTensor X Y).mapCoalgebra (Bialgebra.mulCoalgHom R C)))
      ((externalTensor (dual Y) (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)) where
  toLinearMap :=
    ((_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
      (_root_.TensorProduct.dualDistribEquiv R V W)).symm.toLinearMap
  colinear := by
    apply Coalgebra.RightComoduleHom.colinear_symm
      ((_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
        (_root_.TensorProduct.dualDistribEquiv R V W))
    simpa only [tensorDual_toLinearMap] using (tensorDual X Y).colinear

/-- The inverse has the inverse of the underlying tensor-dual equivalence. -/
theorem tensorDualInv_toLinearMap :
    (tensorDualInv X Y).toLinearMap =
      ((_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
        (_root_.TensorProduct.dualDistribEquiv R V W)).symm.toLinearMap := rfl

/-- Applying the comparison and then its inverse fixes the tensor of covectors. -/
@[simp] theorem tensorDualInv_apply_tensorDual
    (t : Module.Dual R W ⊗[R] Module.Dual R V) :
    tensorDualInv X Y (tensorDual X Y t) = t := by
  let e := (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
    (_root_.TensorProduct.dualDistribEquiv R V W)
  change e.symm (e t) = t
  exact e.symm_apply_apply t

/-- Applying the inverse and then the comparison fixes the tensor covector. -/
@[simp] theorem tensorDual_apply_tensorDualInv
    (F : Module.Dual R (V ⊗[R] W)) :
    tensorDual X Y (tensorDualInv X Y F) = F := by
  let e := (_root_.TensorProduct.comm R (Module.Dual R W) (Module.Dual R V)).trans
    (_root_.TensorProduct.dualDistribEquiv R V W)
  change e (e.symm F) = F
  exact e.apply_symm_apply F

/-- Evaluation of a decomposable tensor covector factors into two evaluations. -/
theorem evaluation_tensorDual_tmul (g : Module.Dual R W)
    (f : Module.Dual R V) (v : V) (w : W) :
    evaluation ((externalTensor X Y).mapCoalgebra (Bialgebra.mulCoalgHom R C))
        (tensorDual X Y (g ⊗ₜ[R] f) ⊗ₜ[R] (v ⊗ₜ[R] w)) =
      evaluation X (f ⊗ₜ[R] v) * evaluation Y (g ⊗ₜ[R] w) := by
  simp only [evaluation_apply_tmul, tensorDual_apply_tmul_tmul]

variable {V2 : Type uV2} {W2 : Type uW2}
variable [AddCommMonoid V2] [Module R V2] [AddCommMonoid W2] [Module R W2]
variable [Module.Finite R V2] [Module.Projective R V2]
variable [Module.Finite R W2] [Module.Projective R W2]

/-- The reversed tensor comparison is contravariantly natural in both comodules. -/
theorem tensorDual_naturality
    {X2 : Coalgebra.RightComodule R C V2} {Y2 : Coalgebra.RightComodule R C W2}
    (a : Coalgebra.RightComoduleHom X X2) (b : Coalgebra.RightComoduleHom Y Y2)
    (t : Module.Dual R W2 ⊗[R] Module.Dual R V2) :
    (Coalgebra.RightComoduleHom.dualMap
      ((Coalgebra.RightComoduleHom.externalTensor a b).mapCoalgebra
        (Bialgebra.mulCoalgHom R C))) (tensorDual X2 Y2 t) =
      tensorDual X Y
        (((Coalgebra.RightComoduleHom.externalTensor
          (Coalgebra.RightComoduleHom.dualMap b)
          (Coalgebra.RightComoduleHom.dualMap a)).mapCoalgebra
            (Bialgebra.mulCoalgHom R C)) t) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul g f =>
    ext v w
    change tensorDual X2 Y2 (g ⊗ₜ[R] f)
        (_root_.TensorProduct.map a.toLinearMap b.toLinearMap (v ⊗ₜ[R] w)) =
      tensorDual X Y
        (_root_.TensorProduct.map
          (Coalgebra.RightComoduleHom.dualMap b).toLinearMap
          (Coalgebra.RightComoduleHom.dualMap a).toLinearMap (g ⊗ₜ[R] f))
        (v ⊗ₜ[R] w)
    simp only [_root_.TensorProduct.map_tmul, tensorDual_apply_tmul_tmul]
    rfl
  | add t t' ht ht' =>
    simp only [map_add, ht, ht']

end Coalgebra.RightComodule
