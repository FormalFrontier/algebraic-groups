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

For specified right coacts of `C` on `V` and `D` on `W`,
`TauCeti.Comodule.externalTensorCoaction` tensors the coact maps and
then interchanges the middle factors. It is a linear map from `V ⊗[R] W` to
`(V ⊗[R] W) ⊗[R] (C ⊗[R] D)`, over any commutative semiring. All five
universes are independent, and no flatness, projectivity or finiteness is
required.

The application formula retains the shuffle of the two coact values:
those values need not themselves be pure tensors. The coassociativity and
counit equalities use Mathlib's tensor coalgebra on `C ⊗[R] D`. The counit
equality has codomain `(V ⊗[R] W) ⊗[R] R`, with the inverse right unitor on
the right. For the regular input comodules, the map is the comultiplication
of that same tensor coalgebra.

`TauCeti.Comodule.externalTensor` equips `V ⊗[R] W` with this
coact as a specified right comodule over `C ⊗[R] D`. Its coact API gives
map, application and pure-input formulas, and `externalTensor_regular`
identifies the external tensor product of regular comodules with the regular
comodule of the tensor coalgebra. The general right-comodule coassociativity,
counit, injectivity and zero-map lemmas apply to the constructed object.

`TauCeti.Comodule.Hom.externalTensor` tensors specified comodule morphisms,
with underlying linear map `TensorProduct.map`. Its pure-tensor, identity and
composition laws make the external tensor construction functorial in both inputs.

This is an external tensor product over two coalgebras, not an internal tensor
product over a fixed bialgebra. No coherence is asserted here.

## References

The specified right comodules and regular coacts are the existing
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
open Coalgebra

namespace TauCeti.Comodule

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable {V : Type uV} {W : Type uW}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Tensor the two specified coacts and interchange their middle factors,
placing the tensor of the coalgebra factors on the right. -/
def externalTensorCoaction (X : Comodule R C V) (Y : Comodule R D W) :
    V ⊗[R] W →ₗ[R] (V ⊗[R] W) ⊗[R] (C ⊗[R] D) :=
  (_root_.TensorProduct.tensorTensorTensorComm R V C W D).toLinearMap ∘ₗ
    _root_.TensorProduct.map X.coact Y.coact

/-- On a pure input tensor, apply the forward shuffle to the tensor of the
coact values, without requiring those values to be pure tensors. -/
theorem externalTensorCoaction_tmul (X : Comodule R C V)
    (Y : Comodule R D W) (v : V) (w : W) :
    externalTensorCoaction X Y (v ⊗ₜ[R] w) =
      _root_.TensorProduct.tensorTensorTensorComm R V C W D
        (X.coact v ⊗ₜ[R] Y.coact w) := by
  rfl

/-- Coassociativity of the external tensor coact, using the tensor
coalgebra's comultiplication and the forward associator. -/
theorem externalTensorCoaction_coassoc (X : Comodule R C V)
    (Y : Comodule R D W) :
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
      s₂ ∘ₗ _root_.TensorProduct.map (X.coact.rTensor C) (Y.coact.rTensor D) =
        (_root_.TensorProduct.map X.coact Y.coact).rTensor (C ⊗[R] D) ∘ₗ s := by
    simpa only [s, s₂, LinearMap.rTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.tensorTensorTensorComm_comp_map R X.coact
        (LinearMap.id : C →ₗ[R] C) Y.coact (LinearMap.id : D →ₗ[R] D))
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
          (((_root_.TensorProduct.map X.coact Y.coact).rTensor (C ⊗[R] D) ∘ₗ s) ∘ₗ
            _root_.TensorProduct.map X.coact Y.coact) := by
      simp only [externalTensorCoaction, s, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (_root_.TensorProduct.assoc
          R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        s.rTensor (C ⊗[R] D) ∘ₗ
          ((s₂ ∘ₗ _root_.TensorProduct.map (X.coact.rTensor C) (Y.coact.rTensor D)) ∘ₗ
            _root_.TensorProduct.map X.coact Y.coact) := by rw [hnatural]
    _ = ((_root_.TensorProduct.assoc
          R (V ⊗[R] W) (C ⊗[R] D) (C ⊗[R] D)).toLinearMap ∘ₗ
        s.rTensor (C ⊗[R] D) ∘ₗ s₂) ∘ₗ
          _root_.TensorProduct.map (X.coact.rTensor C) (Y.coact.rTensor D) ∘ₗ
            _root_.TensorProduct.map X.coact Y.coact := by
      simp only [LinearMap.comp_assoc]
    _ = F ∘ₗ _root_.TensorProduct.map
        ((_root_.TensorProduct.assoc R V C C).toLinearMap ∘ₗ
          X.coact.rTensor C ∘ₗ X.coact)
        ((_root_.TensorProduct.assoc R W D D).toLinearMap ∘ₗ
          Y.coact.rTensor D ∘ₗ Y.coact) := by
      rw [hshuffle]
      simp only [LinearMap.comp_assoc, ← _root_.TensorProduct.map_comp]
    _ = F ∘ₗ _root_.TensorProduct.map
        ((Coalgebra.comul (R := R) (A := C)).lTensor V ∘ₗ X.coact)
        ((Coalgebra.comul (R := R) (A := D)).lTensor W ∘ₗ Y.coact) := by
      rw [X.coassoc, Y.coassoc]
    _ = (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap.lTensor
          (V ⊗[R] W) ∘ₗ
        ((_root_.TensorProduct.tensorTensorTensorComm
            R V (C ⊗[R] C) W (D ⊗[R] D)).toLinearMap ∘ₗ
          _root_.TensorProduct.map
            ((Coalgebra.comul (R := R) (A := C)).lTensor V)
            ((Coalgebra.comul (R := R) (A := D)).lTensor W)) ∘ₗ
          _root_.TensorProduct.map X.coact Y.coact := by
      simp only [F, LinearMap.comp_assoc, ← _root_.TensorProduct.map_comp]
    _ = (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap.lTensor
          (V ⊗[R] W) ∘ₗ
        ((_root_.TensorProduct.map (Coalgebra.comul (R := R) (A := C))
          (Coalgebra.comul (R := R) (A := D))).lTensor (V ⊗[R] W) ∘ₗ s) ∘ₗ
          _root_.TensorProduct.map X.coact Y.coact := by rw [hdelta]
    _ = _ := by
      rw [hcomul, LinearMap.lTensor_comp]
      simp only [externalTensorCoaction, s, LinearMap.comp_assoc]

/-- Right counitality of the external tensor coact as an equality of maps
into `(V ⊗[R] W) ⊗[R] R`. -/
theorem externalTensorCoaction_counit_comp (X : Comodule R C V)
    (Y : Comodule R D W) :
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
    _root_.TensorProduct.map_tmul, (@Comodule.lTensor_counit_coact R C V _ _ _ _ _ _ X),
    (@Comodule.lTensor_counit_coact R D W _ _ _ _ _ _ Y),
    TensorProduct.rid_tmul, one_smul,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun hnatural (X.coact v ⊗ₜ[R] Y.coact w)

/-- The external tensor coact of the two regular comodules is the
comultiplication of the canonical tensor coalgebra. -/
theorem externalTensorCoaction_regular :
    externalTensorCoaction (Comodule.instSelf R C) (Comodule.instSelf R D) =
      Coalgebra.comul (R := R) (A := C ⊗[R] D) := by
  simpa only [externalTensorCoaction, Comodule.instSelf_coact,
    _root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq,
    _root_.TensorProduct.AlgebraTensorModule.map_eq] using
    (_root_.TensorProduct.comul_def (R := R) (S := R) (A := C) (B := D)).symm

universe uM uN

variable {M : Type uM} {N : Type uN}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The external tensor product of two specified right comodules, over the tensor
coalgebra. Its coact tensors the input coacts and interchanges the middle
factors. This is the classical external tensor construction for comodules
(Sweedler, *Hopf Algebras*, 1969), here over a commutative semiring. -/
@[instance_reducible] def externalTensor (X : Comodule R C M) (Y : Comodule R D N) :
    Comodule R (C ⊗[R] D) (M ⊗[R] N) where
  coact := externalTensorCoaction X Y
  coassoc := externalTensorCoaction_coassoc X Y
  lTensor_counit_comp_coact := externalTensorCoaction_counit_comp X Y

/-- The coact map of the external tensor product is the external tensor coact. -/
@[simp] theorem externalTensor_coact (X : Comodule R C M) (Y : Comodule R D N) :
    (externalTensor X Y).coact = externalTensorCoaction X Y := by
  rfl

/-- Evaluate the external tensor product's coact at any tensor. -/
theorem externalTensor_coact_apply (X : Comodule R C M)
    (Y : Comodule R D N) (t : M ⊗[R] N) :
    (externalTensor X Y).coact t = externalTensorCoaction X Y t := by
  rfl

/-- On pure inputs, shuffle the tensor of the coact values. Neither input
coact value is required to be a pure tensor. -/
@[simp] theorem externalTensor_coact_tmul (X : Comodule R C M)
    (Y : Comodule R D N) (m : M) (n : N) :
    externalTensorCoaction X Y (m ⊗ₜ[R] n) =
      _root_.TensorProduct.tensorTensorTensorComm R M C N D
        (X.coact m ⊗ₜ[R] Y.coact n) := by
  exact externalTensorCoaction_tmul X Y m n

/-- A coefficient of an external tensor product on a pure input is the tensor
of the corresponding coefficients. The functional is the tensor of the two
functionals followed by the left unitor. -/
@[simp] theorem externalTensor_coefficient_tmul (X : Comodule R C M)
    (Y : Comodule R D N) (ell : M →ₗ[R] R) (eta : N →ₗ[R] R) (m : M) (n : N) :
    (@matrixCoefficient R (C ⊗[R] D) (M ⊗[R] N) _ _ _ _ _ _ (X.externalTensor Y))
        ((_root_.TensorProduct.lid R R).toLinearMap ∘ₗ _root_.TensorProduct.map ell eta)
        (m ⊗ₜ[R] n) =
      (@matrixCoefficient R C M _ _ _ _ _ _ X) ell m ⊗ₜ[R] (@matrixCoefficient R D N _ _ _ _ _ _
        Y) eta n := by
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
  simpa only [matrixCoefficient_def, ← LinearMap.rTensor_def, externalTensor_coact,
    externalTensorCoaction_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.map_tmul] using
    LinearMap.congr_fun hcontract (X.coact m ⊗ₜ[R] Y.coact n)

/-- The external tensor product of regular comodules is the regular comodule
of the same tensor coalgebra. -/
theorem externalTensor_regular :
    externalTensor (Comodule.instSelf R C) (Comodule.instSelf R D) = Comodule.instSelf R (C ⊗[R]
      D) := by
  apply Comodule.ext
  rw [externalTensor_coact]
  exact externalTensorCoaction_regular

end TauCeti.Comodule


namespace TauCeti.Comodule.Hom

universe uM0 uM1 uM2 uN0 uN1 uN2

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M0 : Type uM0} {M1 : Type uM1} {N0 : Type uN0} {N1 : Type uN1}
variable [AddCommMonoid M0] [Module R M0] [AddCommMonoid M1] [Module R M1]
variable [AddCommMonoid N0] [Module R N0] [AddCommMonoid N1] [Module R N1]
variable [X0 : Comodule R C M0] [X1 : Comodule R C M1]
variable [Y0 : Comodule R D N0] [Y1 : Comodule R D N1]


/-- The source tensor coaction used to interpret external comodule morphisms. -/
local instance instExternalTensorSource : Comodule R (C ⊗[R] D) (M0 ⊗[R] N0) :=
  Comodule.externalTensor X0 Y0

/-- The target tensor coaction used to interpret external comodule morphisms. -/
local instance instExternalTensorTarget : Comodule R (C ⊗[R] D) (M1 ⊗[R] N1) :=
  Comodule.externalTensor X1 Y1

/-- The external tensor product of two specified right-comodule morphisms.
Its underlying linear map is the tensor product of the two underlying maps. -/
def externalTensor (f : (@Hom R C M0 M1 _ _ _ _ _ _ X0 _ _ X1)) (g : (@Hom R D N0 N1 _ _ _ _ _ _
  Y0 _ _ Y1)) :
    (@Hom R (C ⊗[R] D) (M0 ⊗[R] N0) (M1 ⊗[R] N1) _ _ _ _ _ _ (X0.externalTensor Y0) _ _
      (X1.externalTensor Y1)) where
  toLinearMap := _root_.TensorProduct.map f.toLinearMap g.toLinearMap
  map_coact := by
    symm
    have hf : X1.coact ∘ₗ f.toLinearMap = f.toLinearMap.rTensor C ∘ₗ X0.coact := by
      simpa only [LinearMap.rTensor_def] using f.map_coact.symm
    have hg : Y1.coact ∘ₗ g.toLinearMap = g.toLinearMap.rTensor D ∘ₗ Y0.coact := by
      simpa only [LinearMap.rTensor_def] using g.map_coact.symm
    have hshuffle :
        (_root_.TensorProduct.tensorTensorTensorComm R M1 C N1 D).toLinearMap ∘ₗ
            _root_.TensorProduct.map (f.toLinearMap.rTensor C) (g.toLinearMap.rTensor D) =
          (_root_.TensorProduct.map f.toLinearMap g.toLinearMap).rTensor (C ⊗[R] D) ∘ₗ
            (_root_.TensorProduct.tensorTensorTensorComm R M0 C N0 D).toLinearMap := by
      simpa only [LinearMap.rTensor_def, _root_.TensorProduct.map_id] using
        (_root_.TensorProduct.tensorTensorTensorComm_comp_map R f.toLinearMap
          (LinearMap.id : C →ₗ[R] C) g.toLinearMap (LinearMap.id : D →ₗ[R] D))
    simp only [Comodule.externalTensor_coact, Comodule.externalTensorCoaction,
      LinearMap.comp_assoc]
    rw [← _root_.TensorProduct.map_comp, hf, hg,
      _root_.TensorProduct.map_comp, ← LinearMap.comp_assoc, hshuffle, LinearMap.comp_assoc]
    rfl

/-- Forgetting colinearity gives the tensor product of the underlying linear maps. -/
@[simp] theorem toLinearMap_externalTensor (f : (@Hom R C M0 M1 _ _ _ _ _ _ X0 _ _ X1))
    (g : (@Hom R D N0 N1 _ _ _ _ _ _ Y0 _ _ Y1)) :
    (f.externalTensor g).toLinearMap = _root_.TensorProduct.map f.toLinearMap g.toLinearMap := rfl

/-- Evaluate the external tensor product of morphisms at an arbitrary tensor. -/
@[simp] theorem externalTensor_apply (f : (@Hom R C M0 M1 _ _ _ _ _ _ X0 _ _ X1))
    (g : (@Hom R D N0 N1 _ _ _ _ _ _ Y0 _ _ Y1)) (t : M0 ⊗[R] N0) :
    (f.externalTensor g) t = _root_.TensorProduct.map f.toLinearMap g.toLinearMap t := rfl

/-- On pure tensors, the external tensor product applies each morphism to its factor. -/
@[simp] theorem externalTensor_tmul (f : (@Hom R C M0 M1 _ _ _ _ _ _ X0 _ _ X1))
    (g : (@Hom R D N0 N1 _ _ _ _ _ _ Y0 _ _ Y1)) (m : M0) (n : N0) :
    (f.externalTensor g) (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  _root_.TensorProduct.map_tmul f.toLinearMap g.toLinearMap m n

/-- The external tensor product preserves identity morphisms. -/
theorem externalTensor_id :
    (@Hom.id R C M0 _ _ _ _ _ _ X0).externalTensor (@Hom.id R D N0 _ _ _ _ _ _ Y0) = (@Hom.id R
      (C ⊗[R] D) (M0 ⊗[R] N0) _ _ _ _ _ _ (X0.externalTensor Y0)) := by
  apply toLinearMap_injective
  exact _root_.TensorProduct.map_id

variable {M2 : Type uM2} {N2 : Type uN2}
variable [AddCommMonoid M2] [Module R M2] [AddCommMonoid N2] [Module R N2]
variable [X2 : Comodule R C M2] [Y2 : Comodule R D N2]


/-- The final tensor coaction for a composite of external comodule morphisms. -/
local instance instExternalTensorComposite : Comodule R (C ⊗[R] D) (M2 ⊗[R] N2) :=
  Comodule.externalTensor X2 Y2

/-- The external tensor product preserves composition in both factors. -/
theorem externalTensor_comp (f2 : (@Hom R C M1 M2 _ _ _ _ _ _ X1 _ _ X2)) (f1 : (@Hom R C M0 M1 _
  _ _ _ _ _ X0 _ _ X1))
    (g2 : (@Hom R D N1 N2 _ _ _ _ _ _ Y1 _ _ Y2)) (g1 : (@Hom R D N0 N1 _ _ _ _ _ _ Y0 _ _ Y1)) :
    (f2.comp f1).externalTensor (g2.comp g1) =
      (f2.externalTensor g2).comp (f1.externalTensor g1) := by
  apply toLinearMap_injective
  exact _root_.TensorProduct.map_comp f2.toLinearMap g2.toLinearMap f1.toLinearMap g1.toLinearMap

end TauCeti.Comodule.Hom
