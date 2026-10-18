/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# External tensor products of specified right comodules

For specified right coactions of `C` on `V` and `D` on `W`,
`Coalgebra.RightComodule.externalTensorCoaction` tensors the coaction maps and
then interchanges the middle factors. It is a linear map from `V ⊗[R] W` to
`(V ⊗[R] W) ⊗[R] (C ⊗[R] D)`, over any commutative semiring. All five
universes are independent, and no flatness, projectivity or finiteness is
required.

The application formula retains the shuffle of the two coaction values:
those values need not themselves be pure tensors. The coassociativity and
counit equalities use Mathlib's tensor coalgebra on `C ⊗[R] D`. The counit
equality has codomain `(V ⊗[R] W) ⊗[R] R`, with the inverse right unitor on
the right. For the regular input comodules, the map is the comultiplication
of that same tensor coalgebra.

`Coalgebra.RightComodule.externalTensor` equips `V ⊗[R] W` with this
coaction as a specified right comodule over `C ⊗[R] D`. Its coaction API gives
map, application and pure-input formulas, and `externalTensor_regular`
identifies the external tensor product of regular comodules with the regular
comodule of the tensor coalgebra. The general right-comodule coassociativity,
counit, injectivity and zero-map lemmas apply to the constructed object.

This is an external tensor product over two coalgebras, not an internal tensor
product over a fixed bialgebra. No morphism action or coherence is asserted here.

## References

The specified right comodules and regular coactions are the existing
AlgebraicGroups constructions by Formal Frontier Agents. Tensor maps,
associators, unitors and the middle-factor interchange are Mathlib's
formalizations by Kenny Lau and Mario Carneiro. Mathlib's tensor coalgebra,
by Amelia Livingston and Andrew Yang, uses the scalar-tower tensor APIs of
Kim Morrison, Johan Commelin and Eric Wieser. Classical comodules are credited
bibliographically to M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969.
-/

@[expose] public section

universe uR uC uD uV uW

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable {V : Type uV} {W : Type uW}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Tensor the two specified coactions and interchange their middle factors,
placing the tensor of the coalgebra factors on the right. -/
def externalTensorCoaction (X : RightComodule R C V) (Y : RightComodule R D W) :
    V ⊗[R] W →ₗ[R] (V ⊗[R] W) ⊗[R] (C ⊗[R] D) :=
  (_root_.TensorProduct.tensorTensorTensorComm R V C W D).toLinearMap ∘ₗ
    _root_.TensorProduct.map X.coaction Y.coaction

/-- On a pure input tensor, apply the forward shuffle to the tensor of the
coaction values, without requiring those values to be pure tensors. -/
theorem externalTensorCoaction_tmul (X : RightComodule R C V)
    (Y : RightComodule R D W) (v : V) (w : W) :
    externalTensorCoaction X Y (v ⊗ₜ[R] w) =
      _root_.TensorProduct.tensorTensorTensorComm R V C W D
        (X.coaction v ⊗ₜ[R] Y.coaction w) := by
  rfl

/-- Coassociativity of the external tensor coaction, using the tensor
coalgebra's comultiplication and the forward associator. -/
theorem externalTensorCoaction_coassoc (X : RightComodule R C V)
    (Y : RightComodule R D W) :
    (_root_.TensorProduct.assoc R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        (externalTensorCoaction X Y).rTensor (C ⊗[R] D) ∘ₗ externalTensorCoaction X Y =
      (Coalgebra.comul (R := R) (A := C ⊗[R] D)).lTensor (V ⊗[R] W) ∘ₗ
        externalTensorCoaction X Y := by
  let s := (_root_.TensorProduct.tensorTensorTensorComm R V C W D).toLinearMap
  let s₂ := (_root_.TensorProduct.tensorTensorTensorComm
    R (V ⊗[R] C) C (W ⊗[R] D) D).toLinearMap
  let F := (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap.lTensor
      (V ⊗[R] W) ∘ₗ
    (_root_.TensorProduct.tensorTensorTensorComm R V (C ⊗[R] C) W (D ⊗[R] D)).toLinearMap
  -- Both routes send the six factors to (V, W), ((C, D), (C, D)), in that order.
  have hshuffle :
      (_root_.TensorProduct.assoc R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
          s.rTensor (C ⊗[R] D) ∘ₗ s₂ =
        F ∘ₗ _root_.TensorProduct.map
          (_root_.TensorProduct.assoc R V C C).toLinearMap
          (_root_.TensorProduct.assoc R W D D).toLinearMap := by
    apply _root_.TensorProduct.ext
    apply _root_.TensorProduct.ext_threefold
    intro v c₁ c₂
    apply _root_.TensorProduct.ext_threefold
    intro w d₁ d₂
    rfl
  have hnatural :
      s₂ ∘ₗ _root_.TensorProduct.map (X.coaction.rTensor C) (Y.coaction.rTensor D) =
        (_root_.TensorProduct.map X.coaction Y.coaction).rTensor (C ⊗[R] D) ∘ₗ s := by
    simpa only [s, s₂, LinearMap.rTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.tensorTensorTensorComm_comp_map R X.coaction
        (LinearMap.id : C →ₗ[R] C) Y.coaction (LinearMap.id : D →ₗ[R] D))
  have hcomul :
      Coalgebra.comul (R := R) (A := C ⊗[R] D) =
        (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap ∘ₗ
          _root_.TensorProduct.map (Coalgebra.comul (R := R) (A := C))
            (Coalgebra.comul (R := R) (A := D)) := by
    simpa only [_root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq,
      _root_.TensorProduct.AlgebraTensorModule.map_eq] using
      (_root_.TensorProduct.comul_def (R := R) (S := R) (A := C) (B := D))
  have hdelta :
      (_root_.TensorProduct.tensorTensorTensorComm
          R V (C ⊗[R] C) W (D ⊗[R] D)).toLinearMap ∘ₗ
        _root_.TensorProduct.map
          ((Coalgebra.comul (R := R) (A := C)).lTensor V)
          ((Coalgebra.comul (R := R) (A := D)).lTensor W) =
        (_root_.TensorProduct.map (Coalgebra.comul (R := R) (A := C))
          (Coalgebra.comul (R := R) (A := D))).lTensor (V ⊗[R] W) ∘ₗ s := by
    simpa only [s, LinearMap.lTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.tensorTensorTensorComm_comp_map R (LinearMap.id : V →ₗ[R] V)
        (Coalgebra.comul (R := R) (A := C)) (LinearMap.id : W →ₗ[R] W)
        (Coalgebra.comul (R := R) (A := D)))
  calc
    _ = (_root_.TensorProduct.assoc
          R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        s.rTensor (C ⊗[R] D) ∘ₗ
          (((_root_.TensorProduct.map X.coaction Y.coaction).rTensor (C ⊗[R] D) ∘ₗ s) ∘ₗ
            _root_.TensorProduct.map X.coaction Y.coaction) := by
      simp only [externalTensorCoaction, s, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (_root_.TensorProduct.assoc
          R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        s.rTensor (C ⊗[R] D) ∘ₗ
          ((s₂ ∘ₗ _root_.TensorProduct.map (X.coaction.rTensor C) (Y.coaction.rTensor D)) ∘ₗ
            _root_.TensorProduct.map X.coaction Y.coaction) := by rw [hnatural]
    _ = ((_root_.TensorProduct.assoc
          R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        s.rTensor (C ⊗[R] D) ∘ₗ s₂) ∘ₗ
          _root_.TensorProduct.map (X.coaction.rTensor C) (Y.coaction.rTensor D) ∘ₗ
            _root_.TensorProduct.map X.coaction Y.coaction := by
      simp only [LinearMap.comp_assoc]
    _ = F ∘ₗ _root_.TensorProduct.map
        ((_root_.TensorProduct.assoc R V C C).toLinearMap ∘ₗ
          X.coaction.rTensor C ∘ₗ X.coaction)
        ((_root_.TensorProduct.assoc R W D D).toLinearMap ∘ₗ
          Y.coaction.rTensor D ∘ₗ Y.coaction) := by
      rw [hshuffle]
      simp only [LinearMap.comp_assoc, ← _root_.TensorProduct.map_comp]
    _ = F ∘ₗ _root_.TensorProduct.map
        ((Coalgebra.comul (R := R) (A := C)).lTensor V ∘ₗ X.coaction)
        ((Coalgebra.comul (R := R) (A := D)).lTensor W ∘ₗ Y.coaction) := by
      rw [X.coassoc, Y.coassoc]
    _ = (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap.lTensor
          (V ⊗[R] W) ∘ₗ
        ((_root_.TensorProduct.tensorTensorTensorComm
            R V (C ⊗[R] C) W (D ⊗[R] D)).toLinearMap ∘ₗ
          _root_.TensorProduct.map
            ((Coalgebra.comul (R := R) (A := C)).lTensor V)
            ((Coalgebra.comul (R := R) (A := D)).lTensor W)) ∘ₗ
          _root_.TensorProduct.map X.coaction Y.coaction := by
      simp only [F, LinearMap.comp_assoc, ← _root_.TensorProduct.map_comp]
    _ = (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap.lTensor
          (V ⊗[R] W) ∘ₗ
        ((_root_.TensorProduct.map (Coalgebra.comul (R := R) (A := C))
          (Coalgebra.comul (R := R) (A := D))).lTensor (V ⊗[R] W) ∘ₗ s) ∘ₗ
          _root_.TensorProduct.map X.coaction Y.coaction := by rw [hdelta]
    _ = _ := by
      rw [hcomul, LinearMap.lTensor_comp]
      simp only [externalTensorCoaction, s, LinearMap.comp_assoc]

/-- Right counitality of the external tensor coaction as an equality of maps
into `(V ⊗[R] W) ⊗[R] R`. -/
theorem externalTensorCoaction_counit_comp (X : RightComodule R C V)
    (Y : RightComodule R D W) :
    (Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor (V ⊗[R] W) ∘ₗ
        externalTensorCoaction X Y =
      (_root_.TensorProduct.rid R (V ⊗[R] W)).symm.toLinearMap := by
  -- Contracting the shuffled coefficients is natural in both module factors.
  have hnatural :
      (_root_.TensorProduct.rid R (V ⊗[R] W)).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor (V ⊗[R] W) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R V C W D).toLinearMap =
        _root_.TensorProduct.map
          ((_root_.TensorProduct.rid R V).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := C)).lTensor V)
          ((_root_.TensorProduct.rid R W).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := D)).lTensor W) := by
    apply _root_.TensorProduct.ext_fourfold'
    intro v c w d
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      _root_.TensorProduct.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul,
      _root_.TensorProduct.counit_tmul, _root_.TensorProduct.map_tmul,
      _root_.TensorProduct.rid_tmul, _root_.TensorProduct.smul_tmul',
      _root_.TensorProduct.tmul_smul, smul_smul, smul_eq_mul]
  apply _root_.TensorProduct.ext'
  intro v w
  apply (_root_.TensorProduct.rid R (V ⊗[R] W)).injective
  simpa only [externalTensorCoaction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    _root_.TensorProduct.map_tmul, X.rid_counit_coaction, Y.rid_counit_coaction,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun hnatural (X.coaction v ⊗ₜ[R] Y.coaction w)

/-- The external tensor coaction of the two regular comodules is the
comultiplication of the canonical tensor coalgebra. -/
theorem externalTensorCoaction_regular :
    externalTensorCoaction (regular R C) (regular R D) =
      Coalgebra.comul (R := R) (A := C ⊗[R] D) := by
  simpa only [externalTensorCoaction, regular,
    _root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq,
    _root_.TensorProduct.AlgebraTensorModule.map_eq] using
    (_root_.TensorProduct.comul_def (R := R) (S := R) (A := C) (B := D)).symm

universe uM uN

variable {M : Type uM} {N : Type uN}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The external tensor product of two specified right comodules, over the tensor
coalgebra. Its coaction tensors the input coactions and interchanges the middle
factors. This is the classical external tensor construction for comodules
(Sweedler, *Hopf Algebras*, 1969), here over a commutative semiring. -/
def externalTensor (X : RightComodule R C M) (Y : RightComodule R D N) :
    RightComodule R (C ⊗[R] D) (M ⊗[R] N) where
  coaction := externalTensorCoaction X Y
  coassoc := externalTensorCoaction_coassoc X Y
  counit_comp := externalTensorCoaction_counit_comp X Y

/-- The coaction map of the external tensor product is the external tensor coaction. -/
@[simp] theorem externalTensor_coaction (X : RightComodule R C M) (Y : RightComodule R D N) :
    (externalTensor X Y).coaction = externalTensorCoaction X Y := by
  rfl

/-- Evaluate the external tensor product's coaction at any tensor. -/
theorem externalTensor_coaction_apply (X : RightComodule R C M)
    (Y : RightComodule R D N) (t : M ⊗[R] N) :
    (externalTensor X Y).coaction t = externalTensorCoaction X Y t := by
  rfl

/-- On pure inputs, shuffle the tensor of the coaction values. Neither input
coaction value is required to be a pure tensor. -/
@[simp] theorem externalTensor_coaction_tmul (X : RightComodule R C M)
    (Y : RightComodule R D N) (m : M) (n : N) :
    (externalTensor X Y).coaction (m ⊗ₜ[R] n) =
      _root_.TensorProduct.tensorTensorTensorComm R M C N D
        (X.coaction m ⊗ₜ[R] Y.coaction n) := by
  exact externalTensorCoaction_tmul X Y m n

/-- A coefficient of an external tensor product on a pure input is the tensor
of the corresponding coefficients. The functional is the tensor of the two
functionals followed by the left unitor. -/
@[simp] theorem externalTensor_coefficient_tmul (X : RightComodule R C M)
    (Y : RightComodule R D N) (ell : M →ₗ[R] R) (eta : N →ₗ[R] R) (m : M) (n : N) :
    (X.externalTensor Y).coefficient
        ((_root_.TensorProduct.lid R R).toLinearMap ∘ₗ _root_.TensorProduct.map ell eta)
        (m ⊗ₜ[R] n) =
      X.coefficient ell m ⊗ₜ[R] Y.coefficient eta n := by
  have hunitor :
      (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap =
        _root_.TensorProduct.map (_root_.TensorProduct.lid R C).toLinearMap
          (_root_.TensorProduct.lid R D).toLinearMap := by
    apply _root_.TensorProduct.ext_fourfold'
    intro r c s d
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      _root_.TensorProduct.tensorTensorTensorComm_tmul, LinearMap.rTensor_tmul,
      _root_.TensorProduct.map_tmul, _root_.TensorProduct.lid_tmul,
      _root_.TensorProduct.smul_tmul_smul, smul_eq_mul]
  have hnatural :
      (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap ∘ₗ
          _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D) =
        (_root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap := by
    simpa only [LinearMap.rTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.tensorTensorTensorComm_comp_map R ell
        (LinearMap.id : C →ₗ[R] C) eta (LinearMap.id : D →ₗ[R] D))
  have hcontract :
      (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          ((_root_.TensorProduct.lid R R).toLinearMap ∘ₗ
            _root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap =
        _root_.TensorProduct.map
          ((_root_.TensorProduct.lid R C).toLinearMap ∘ₗ ell.rTensor C)
          ((_root_.TensorProduct.lid R D).toLinearMap ∘ₗ eta.rTensor D) := by
    calc
      _ = (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          ((_root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
            (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap) := by
        simp only [LinearMap.rTensor_comp, LinearMap.comp_assoc]
      _ = (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          ((_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap ∘ₗ
            _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D)) := by rw [hnatural]
      _ = ((_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap) ∘ₗ
          _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D) := by
        simp only [LinearMap.comp_assoc]
      _ = _ := by rw [hunitor, ← _root_.TensorProduct.map_comp]
  simpa only [coefficient_eq, externalTensor_coaction_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.map_tmul] using
    LinearMap.congr_fun hcontract (X.coaction m ⊗ₜ[R] Y.coaction n)

/-- The external tensor product of regular comodules is the regular comodule
of the same tensor coalgebra. -/
theorem externalTensor_regular :
    externalTensor (regular R C) (regular R D) = regular R (C ⊗[R] D) := by
  apply RightComodule.ext
  rw [externalTensor_coaction]
  exact externalTensorCoaction_regular

end Coalgebra.RightComodule
