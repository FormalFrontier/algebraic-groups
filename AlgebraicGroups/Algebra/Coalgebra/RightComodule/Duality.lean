/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.LinearAlgebra.Coevaluation
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Evaluation and coevaluation for dual right comodules

Evaluation has source `V* ⊗ V` and coevaluation has target `V ⊗ V*`.
Their right coactions use the existing external tensor product followed by
multiplication of coefficients. The scalar unit is transported along the
bialgebra unit. Thus these are the evaluation and coevaluation of a left dual,
while both objects carry right coactions.

The linear coevaluation and both linear triangle identities are the intrinsic
finite-projective constructions in `AlgebraicGroups.LinearAlgebra.Coevaluation`.
-/

@[expose] public section

open Module TensorProduct

universe u v w

namespace Coalgebra.RightComodule

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommSemiring R] [Semiring C] [HopfAlgebra R C]
variable [AddCommMonoid V] [Module R V]

local notation "D" => Module.Dual R V
local notation "S" => HopfAlgebra.antipode R (A := C)
local notation "μ" => LinearMap.mul' R C
local notation "Δ" => Coalgebra.comul (R := R) (A := C)
local notation "η" => BialgHom.toCoalgHom (Bialgebra.unitBialgHom R C)

private theorem scalar_map_unit_coaction (r : R) :
    ((scalar R R).mapCoalgebra η).coaction r = r ⊗ₜ[R] (1 : C) := by
  change r ⊗ₜ[R] algebraMap R C 1 = r ⊗ₜ[R] (1 : C)
  rw [map_one]

private theorem contractLeft_mul_shuffle (t : D ⊗[R] C) (z : V ⊗[R] C) :
    _root_.TensorProduct.lid R C
        ((contractLeft R V).rTensor C
          ((μ).lTensor (D ⊗[R] V)
            (_root_.TensorProduct.tensorTensorTensorComm R D C V C (t ⊗ₜ[R] z)))) =
      μ (_root_.TensorProduct.map (dualTensorHom R V C t) LinearMap.id z) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul f c =>
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w d => simp
    | add z z' hz hz' =>
      simp only [_root_.TensorProduct.tmul_add, map_add, hz, hz']
  | add t t' ht ht' =>
    simp only [_root_.TensorProduct.add_tmul, map_add,
      _root_.TensorProduct.map_add_left, LinearMap.add_apply, ht, ht']

variable [Module.Finite R V] [Module.Projective R V]

omit [Module.Finite R V] [Module.Projective R V] in
private theorem evaluation_antipode_coaction (X : Coalgebra.RightComodule R C V)
    (f : D) (v : V) :
    μ (_root_.TensorProduct.map (S ∘ₗ dualContraction f ∘ₗ X.coaction) LinearMap.id
      (X.coaction v)) = algebraMap R C (f v) := by
  have h (z : V ⊗[R] C) :
      _root_.TensorProduct.map (S ∘ₗ dualContraction f ∘ₗ X.coaction) LinearMap.id z =
        (S).rTensor C
          (_root_.TensorProduct.map (dualContraction f ∘ₗ X.coaction) LinearMap.id z) := by
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w c => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
  rw [h, ← comul_dualContraction_coaction,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, counit_dualContraction_coaction]

/-- Evaluation of the tensor coaction has trivial coefficient. The order of
coefficient multiplication is the dual coefficient followed by the original one. -/
theorem evaluation_coaction (X : Coalgebra.RightComodule R C V) (t : D ⊗[R] V) :
    (contractLeft R V).rTensor C
        (((externalTensor (dual X) X).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction t) =
      contractLeft R V t ⊗ₜ[R] (1 : C) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul f v =>
    apply (_root_.TensorProduct.lid R C).injective
    change _root_.TensorProduct.lid R C
        ((contractLeft R V).rTensor C
          ((μ).lTensor (D ⊗[R] V)
            (_root_.TensorProduct.tensorTensorTensorComm R D C V C
              (dualCoaction X f ⊗ₜ[R] X.coaction v)))) =
      _root_.TensorProduct.lid R C (f v ⊗ₜ[R] (1 : C))
    calc
      _ = μ (_root_.TensorProduct.map (dualTensorHom R V C (dualCoaction X f))
          LinearMap.id (X.coaction v)) :=
        contractLeft_mul_shuffle (dualCoaction X f) (X.coaction v)
      _ = algebraMap R C (f v) := by
        rw [dualTensorHom_dualCoaction]
        exact evaluation_antipode_coaction X f v
      _ = _ := by simp [Algebra.smul_def]
  | add t t' ht ht' =>
    simp only [map_add, _root_.TensorProduct.add_tmul, ht, ht']

/-- Evaluation is a morphism of the specified right comodules. -/
noncomputable def evaluation (X : Coalgebra.RightComodule R C V) :
    Coalgebra.RightComoduleHom
      ((externalTensor (dual X) X).mapCoalgebra (Bialgebra.mulCoalgHom R C))
      ((scalar R R).mapCoalgebra η) where
  toLinearMap := contractLeft R V
  colinear := by
    apply LinearMap.ext
    intro t
    change ((scalar R R).mapCoalgebra η).coaction (contractLeft R V t) =
      (contractLeft R V).rTensor C
        (((externalTensor (dual X) X).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction t)
    rw [scalar_map_unit_coaction]
    exact (evaluation_coaction X t).symm

@[simp] theorem evaluation_toLinearMap (X : Coalgebra.RightComodule R C V) :
    (evaluation X).toLinearMap = contractLeft R V := rfl

@[simp] theorem evaluation_apply (X : Coalgebra.RightComodule R C V) (t : D ⊗[R] V) :
    evaluation X t = contractLeft R V t := rfl

@[simp] theorem evaluation_apply_tmul (X : Coalgebra.RightComodule R C V)
    (f : D) (v : V) :
    evaluation X (f ⊗ₜ[R] v) = f v := rfl

/-- A fixed permutation of three tensor factors, used only to test coevaluation
with the global tensor--Hom equivalence. -/
private def dualityReorder : ((V ⊗[R] D) ⊗[R] C) →ₗ[R] D ⊗[R] (V ⊗[R] C) :=
  (_root_.TensorProduct.assoc R D V C).toLinearMap ∘ₗ
    (_root_.TensorProduct.comm R V D).toLinearMap.rTensor C

private def multiplyRight : (V ⊗[R] C) ⊗[R] C →ₗ[R] V ⊗[R] C :=
  (μ).lTensor V ∘ₗ (_root_.TensorProduct.assoc R V C C).toLinearMap

local notation "mR" => multiplyRight (R := R) (C := C) (V := V)
local notation "reorder" => dualityReorder (R := R) (C := C) (V := V)

omit [Module.Finite R V] [Module.Projective R V] in
private theorem dualityReorder_tmul_right (t : V ⊗[R] D) (c : C) (v : V) :
    dualTensorHom R V (V ⊗[R] C) (reorder (t ⊗ₜ[R] c)) v =
      dualTensorHom R V V ((_root_.TensorProduct.comm R D V).symm t) v ⊗ₜ[R] c := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul w f => simp [dualityReorder, _root_.TensorProduct.smul_tmul']
  | add t t' ht ht' =>
    simp only [map_add, LinearMap.add_apply, _root_.TensorProduct.add_tmul, ht, ht']

omit [Module.Finite R V] [Module.Projective R V] in
private theorem dualTensorHom_mul_shuffle (z : V ⊗[R] C) (t : D ⊗[R] C) (v : V) :
    dualTensorHom R V (V ⊗[R] C)
        (reorder ((μ).lTensor (V ⊗[R] D)
          (_root_.TensorProduct.tensorTensorTensorComm R V C D C (z ⊗ₜ[R] t)))) v =
      mR (z ⊗ₜ[R] dualTensorHom R V C t v) := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul w c =>
    induction t using _root_.TensorProduct.inductionOn with
    | tmul f d =>
      simp [dualityReorder, multiplyRight, _root_.TensorProduct.tmul_smul]
    | add t t' ht ht' =>
      simp only [_root_.TensorProduct.tmul_add, map_add, LinearMap.add_apply, ht, ht']
  | add z z' hz hz' =>
    simp only [_root_.TensorProduct.add_tmul, map_add, LinearMap.add_apply, hz, hz']

private theorem coevaluation_transport_characteristic
    (X : Coalgebra.RightComodule R C V) (t : V ⊗[R] D) (v : V) :
    dualTensorHom R V (V ⊗[R] C)
        (reorder
          (((externalTensor X (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction t)) v =
      mR ((S).lTensor (V ⊗[R] C)
        ((dualTensorHom R V (V ⊗[R] C)
          (_root_.TensorProduct.comm R (V ⊗[R] C) D (X.coaction.rTensor D t))).rTensor C
            (X.coaction v))) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul w f =>
    change dualTensorHom R V (V ⊗[R] C)
        (reorder ((μ).lTensor (V ⊗[R] D)
          (_root_.TensorProduct.tensorTensorTensorComm R V C D C
            (X.coaction w ⊗ₜ[R] dualCoaction X f)))) v = _
    rw [dualTensorHom_mul_shuffle, dualCoaction_characteristic]
    simp only [LinearMap.rTensor_tmul, _root_.TensorProduct.comm_tmul]
    induction X.coaction v using _root_.TensorProduct.inductionOn with
    | tmul a c => simp [_root_.TensorProduct.smul_tmul', _root_.TensorProduct.tmul_smul]
    | add z z' hz hz' => simp [hz, hz', _root_.TensorProduct.tmul_add]
  | add t t' ht ht' =>
    simp only [map_add, LinearMap.add_apply, LinearMap.rTensor_add]
    rw [ht, ht']

private theorem coevaluation_reconstruction (X : Coalgebra.RightComodule R C V) :
    dualTensorHom R V (V ⊗[R] C)
        (_root_.TensorProduct.comm R (V ⊗[R] C) D
          (X.coaction.rTensor D (Module.coevaluationTensor R V))) = X.coaction := by
  have h : _root_.TensorProduct.comm R (V ⊗[R] C) D
        (X.coaction.rTensor D (Module.coevaluationTensor R V)) =
      (dualTensorHomEquiv R V (V ⊗[R] C)).symm X.coaction := by
    rw [← LinearMap.lTensor_comm]
    simpa only [_root_.TensorProduct.comm_symm] using
      (Module.dualTensorHomEquiv_symm_eq_coevaluationTensor R V X.coaction).symm
  rw [h, dualTensorHom_dualTensorHomEquiv_symm]

omit [Module.Finite R V] [Module.Projective R V] in
private theorem multiplyRight_antipode_assoc_tmul (w : V) (t : C ⊗[R] C) :
    mR ((S).lTensor (V ⊗[R] C)
        ((_root_.TensorProduct.assoc R V C C).symm (w ⊗ₜ[R] t))) =
      w ⊗ₜ[R] μ ((S).lTensor C t) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul a b => simp [multiplyRight]
  | add t t' ht ht' =>
    simp only [map_add, _root_.TensorProduct.tmul_add, ht, ht']

omit [Module.Finite R V] [Module.Projective R V] in
private theorem multiplyRight_antipode_coaction (X : Coalgebra.RightComodule R C V)
    (v : V) :
    mR ((S).lTensor (V ⊗[R] C) (X.coaction.rTensor C (X.coaction v))) =
      v ⊗ₜ[R] (1 : C) := by
  rw [← X.coassoc_symm_apply v]
  have h (z : V ⊗[R] C) :
      mR ((S).lTensor (V ⊗[R] C)
          ((_root_.TensorProduct.assoc R V C C).symm ((Δ).lTensor V z))) =
        (η).toLinearMap.lTensor V ((Coalgebra.counit (R := R) (A := C)).lTensor V z) := by
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w c =>
      simp only [LinearMap.lTensor_tmul, multiplyRight_antipode_assoc_tmul,
        HopfAlgebra.mul_antipode_lTensor_comul_apply]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  rw [h, X.counit_coaction]
  change v ⊗ₜ[R] algebraMap R C 1 = v ⊗ₜ[R] (1 : C)
  rw [map_one]

/-- The intrinsic coevaluation tensor is invariant under the tensor right
coaction. The coefficient order is the original coefficient followed by its dual. -/
theorem coevaluationTensor_coaction (X : Coalgebra.RightComodule R C V) :
    ((externalTensor X (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction
        (Module.coevaluationTensor R V) =
      Module.coevaluationTensor R V ⊗ₜ[R] (1 : C) := by
  apply (_root_.TensorProduct.congr
    (_root_.TensorProduct.comm R V D) (LinearEquiv.refl R C)).injective
  apply (_root_.TensorProduct.assoc R D V C).injective
  apply (dualTensorHomEquiv R V (V ⊗[R] C)).injective
  ext v
  change dualTensorHom R V (V ⊗[R] C)
      (reorder
        (((externalTensor X (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction
          (Module.coevaluationTensor R V))) v =
    dualTensorHom R V (V ⊗[R] C)
      (reorder (Module.coevaluationTensor R V ⊗ₜ[R] (1 : C))) v
  rw [coevaluation_transport_characteristic, coevaluation_reconstruction,
    multiplyRight_antipode_coaction, dualityReorder_tmul_right,
    Module.coevaluationTensor_characteristic_apply]

/-- The intrinsic linear coevaluation is a morphism of the specified right
comodules. Its underlying map is exactly `Module.coevaluation`. -/
noncomputable def coevaluation (X : Coalgebra.RightComodule R C V) :
    Coalgebra.RightComoduleHom
      ((scalar R R).mapCoalgebra η)
      ((externalTensor X (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)) where
  toLinearMap := Module.coevaluation R V
  colinear := by
    apply LinearMap.ext
    intro r
    change
      ((externalTensor X (dual X)).mapCoalgebra (Bialgebra.mulCoalgHom R C)).coaction
          (Module.coevaluation R V r) =
        (Module.coevaluation R V).rTensor C (((scalar R R).mapCoalgebra η).coaction r)
    simp only [scalar_map_unit_coaction, LinearMap.rTensor_tmul, Module.coevaluation_apply,
      map_smul, coevaluationTensor_coaction, _root_.TensorProduct.smul_tmul']

@[simp] theorem coevaluation_toLinearMap (X : Coalgebra.RightComodule R C V) :
    (coevaluation X).toLinearMap = Module.coevaluation R V := rfl

@[simp] theorem coevaluation_apply (X : Coalgebra.RightComodule R C V) (r : R) :
    coevaluation X r = Module.coevaluation R V r := rfl

theorem coevaluation_one (X : Coalgebra.RightComodule R C V) :
    coevaluation X 1 = Module.coevaluationTensor R V := by
  simp

/-- The underlying maps of the bundled evaluation and coevaluation satisfy the
stock linear triangle on the original module. -/
theorem evaluation_coevaluation_triangle (X : Coalgebra.RightComodule R C V) :
    (_root_.TensorProduct.rid R V).toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : V →ₗ[R] V) (evaluation X).toLinearMap ∘ₗ
          (_root_.TensorProduct.assoc R V D V).toLinearMap ∘ₗ
            _root_.TensorProduct.map (coevaluation X).toLinearMap (LinearMap.id : V →ₗ[R] V) ∘ₗ
              (_root_.TensorProduct.lid R V).symm.toLinearMap =
      LinearMap.id := by
  simpa only [evaluation_toLinearMap, coevaluation_toLinearMap] using
    Module.coevaluation_triangle R V

/-- The same bundled maps satisfy the stock linear triangle on the dual module;
no additional finite-projectivity assumption on that dual is needed. -/
theorem evaluation_coevaluation_dual_triangle (X : Coalgebra.RightComodule R C V) :
    (_root_.TensorProduct.lid R D).toLinearMap ∘ₗ
        _root_.TensorProduct.map (evaluation X).toLinearMap (LinearMap.id : D →ₗ[R] D) ∘ₗ
          (_root_.TensorProduct.assoc R D V D).symm.toLinearMap ∘ₗ
            _root_.TensorProduct.map (LinearMap.id : D →ₗ[R] D) (coevaluation X).toLinearMap ∘ₗ
              (_root_.TensorProduct.rid R D).symm.toLinearMap =
      LinearMap.id := by
  simpa only [evaluation_toLinearMap, coevaluation_toLinearMap] using
    Module.coevaluation_dual_triangle R V

end Coalgebra.RightComodule
