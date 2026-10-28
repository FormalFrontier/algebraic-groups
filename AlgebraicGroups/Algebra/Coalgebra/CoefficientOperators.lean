/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.TensorProduct.Extension
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Composition of linear coefficient operators

Given an `R`-linear map `δ : M →ₗ[R] C ⊗[R] M` and a linear coefficient
`α : C →ₗ[R] A`, the tensor extension of `(TensorProduct.map α LinearMap.id).comp δ`
is an `A`-linear endomorphism of `A ⊗[R] M`. It sends `a ⊗ₜ m` to
`a • (TensorProduct.map α LinearMap.id) (δ m)`.

Applying the operator for `β` to a tensor mapped by `α` computes by
reassociation and ordered multiplication of the two coefficients. This
calculation requires no coassociativity assumption on `δ`.

Relative coassociativity of `δ` with respect to an explicit linear map
`Δ : C →ₗ[R] C ⊗[R] C` implies a composition law: applying the operator for `α`
first and that for `β` second multiplies the outer coefficient `α` before the
inner coefficient `β`. The tester algebra `A` need not be commutative.

The weak composition theorem uses Mathlib's tensor extension and tensor universal
properties, without multiplication on `C`, a counit, or global coassociativity of `Δ`.
For scalar-valued coefficients, conjugation by the left unitor gives the usual
first-factor contraction. On a coalgebra, postcomposition with the counit recovers
the coefficient. The regular composition law is convolution in left-coaction
order: the operator for `β` after the operator for `α` has coefficient `α * β`.

These calculations use Mathlib's tensor extension, unitors and convolution unit
law. The same unitor and counit calculation specializes to general-linear
coordinate evaluations; no algebra structure on the coalgebra module is needed.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe uR uC uM uA

variable {R : Type uR} {C : Type uC} {M : Type uM} {A : Type uA}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid M] [Module R M] [Semiring A] [Algebra R A]

/-- Applying the tensor-extended operator for `β` to a tensor with coefficient `α`
multiplies the outer coefficient `α` before the inner coefficient `β`.
No coassociativity assumption on the given linear map is needed. -/
theorem lift_toSpanSingleton_apply_map
    (δ : M →ₗ[R] C ⊗[R] M) (α β : C →ₗ[R] A) (x : C ⊗[R] M) :
    lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
      ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))
        (TensorProduct.map α (LinearMap.id : M →ₗ[R] M) x) =
      TensorProduct.map ((LinearMap.mul' R A).comp (TensorProduct.map α β))
        (LinearMap.id : M →ₗ[R] M)
        ((TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ x)) := by
  let F : (C ⊗[R] C) ⊗[R] M →ₗ[R] A ⊗[R] M :=
    TensorProduct.map ((LinearMap.mul' R A).comp (TensorProduct.map α β))
      (LinearMap.id : M →ₗ[R] M)
  -- Evaluate the two coefficients on a reassociated tensor, without choosing
  -- a decomposition of the given coaction.
  have hF (c : C) (x : C ⊗[R] M) :
      F ((TensorProduct.assoc R C C M).symm (c ⊗ₜ[R] x)) =
        α c • TensorProduct.map β (LinearMap.id : M →ₗ[R] M) x := by
    induction x using TensorProduct.inductionOn with
    | tmul d m =>
        simp only [F, TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
          LinearMap.comp_apply, LinearMap.id_apply, LinearMap.mul'_apply,
          TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy, smul_add]
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply, lift_tmul,
        LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
        LinearMap.comp_apply] using (hF c (δ m)).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Relative coassociativity of a given left linear coaction implies composition
of its tensor-extended coefficient operators. The operator for `β` is applied
after the operator for `α`, so their coefficient is
`(LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ)` in this order.
Only the displayed relative coassociativity equation is needed; neither a counit
nor a coalgebra structure on `C` is assumed. -/
theorem lift_toSpanSingleton_comp_map_of_coassoc
    (Δ : C →ₗ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M)
    (α β : C →ₗ[R] A)
    (hδ : (TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) :
    (lift
      (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
      (lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map α (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map
            ((LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ))
            (LinearMap.id : M →ₗ[R] M)).comp δ)) := by
  let F : (C ⊗[R] C) ⊗[R] M →ₗ[R] A ⊗[R] M :=
    TensorProduct.map ((LinearMap.mul' R A).comp (TensorProduct.map α β))
      (LinearMap.id : M →ₗ[R] M)
  have hseed (m : M) :
      lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β (LinearMap.id : M →ₗ[R] M)).comp δ))
          (TensorProduct.map α (LinearMap.id : M →ₗ[R] M) (δ m)) =
        TensorProduct.map
          ((LinearMap.mul' R A).comp ((TensorProduct.map α β).comp Δ))
          (LinearMap.id : M →ₗ[R] M) (δ m) := by
    have hδm : TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M) (δ m) =
        (TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ (δ m)) :=
      LinearMap.congr_fun hδ m
    calc
      _ = F ((TensorProduct.assoc R C C M).symm
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ (δ m))) :=
        lift_toSpanSingleton_apply_map δ α β (δ m)
      _ = F (TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M) (δ m)) :=
        congrArg F hδm.symm
      _ = _ := by
        simp only [F, TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_assoc]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simpa only [LinearMap.comp_apply, lift_tmul, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, map_smul] using
    congrArg (fun z : A ⊗[R] M => a • z) (hseed m)

end TensorProduct.AlgebraTensorModule

namespace TensorProduct.AlgebraTensorModule

universe uR uC

variable {R : Type uR} {C : Type uC}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]

/-- Conjugating the tensor extension of a scalar-valued first-factor coefficient
by the left unitor gives its `rTensor` contraction. The given map `Δ` need not
satisfy any coalgebra law. -/
theorem lid_comp_lift_toSpanSingleton_map
    (Δ : C →ₗ[R] C ⊗[R] C) (ell : C →ₗ[R] R) :
    (TensorProduct.lid R C).toLinearMap.comp
      ((lift
        (LinearMap.toSpanSingleton R (C →ₗ[R] R ⊗[R] C)
          ((TensorProduct.map ell (LinearMap.id : C →ₗ[R] C)).comp Δ))).comp
        (TensorProduct.lid R C).symm.toLinearMap) =
      (TensorProduct.lid R C).toLinearMap.comp ((ell.rTensor C).comp Δ) := by
  simpa only [LinearMap.rTensor_def] using
    lid_comp_lift_toSpanSingleton ((TensorProduct.map ell (LinearMap.id : C →ₗ[R] C)).comp Δ)

end TensorProduct.AlgebraTensorModule

namespace Coalgebra

universe uR uC

variable {R : Type uR} {C : Type uC}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The counit recovers a linear functional from the first-factor contraction of
comultiplication. This is the right unit law for convolution; the carrier only
needs a coalgebra structure, not a multiplication. -/
theorem counit_comp_lid_comp_rTensor_comul (ell : C →ₗ[R] R) :
    (counit : C →ₗ[R] R).comp
      ((_root_.TensorProduct.lid R C).toLinearMap.comp
        ((ell.rTensor C).comp (comul : C →ₗ[R] C ⊗[R] C))) = ell := by
  have hTensor :
      (counit : C →ₗ[R] R).comp
          ((_root_.TensorProduct.lid R C).toLinearMap.comp (ell.rTensor C)) =
        (LinearMap.mul' R R).comp
          (_root_.TensorProduct.map ell (counit : C →ₗ[R] R)) := by
    ext a b
    simp [smul_eq_mul]
  calc
    _ = ((counit : C →ₗ[R] R).comp
        ((_root_.TensorProduct.lid R C).toLinearMap.comp (ell.rTensor C))).comp
          (comul : C →ₗ[R] C ⊗[R] C) := by
      simp only [LinearMap.comp_assoc]
    _ = (LinearMap.mul' R R).comp
        ((_root_.TensorProduct.map ell (counit : C →ₗ[R] R)).comp comul) := by
      rw [hTensor, LinearMap.comp_assoc]
    _ = ell := by
      simpa only [LinearMap.convMul_def, LinearMap.convOne_def,
        WithConv.ofConv_toConv, Algebra.linearMap_self, LinearMap.id_comp] using
        congrArg WithConv.ofConv
          (mul_one (WithConv.toConv ell : WithConv (C →ₗ[R] R)))

end Coalgebra

namespace TensorProduct.AlgebraTensorModule

universe uR uC uA

variable {R : Type uR} {C : Type uC} {A : Type uA}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Reading a regular coefficient operator through the left unitor and counit
recovers the coefficient as an equality of linear maps. -/
theorem counit_comp_lid_comp_lift_toSpanSingleton_comul (ell : C →ₗ[R] R) :
    (Coalgebra.counit : C →ₗ[R] R).comp
      ((TensorProduct.lid R C).toLinearMap.comp
        ((lift
          (LinearMap.toSpanSingleton R (C →ₗ[R] R ⊗[R] C)
            ((TensorProduct.map ell (LinearMap.id : C →ₗ[R] C)).comp
              (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)))).comp
          (TensorProduct.lid R C).symm.toLinearMap)) = ell := by
  rw [lid_comp_lift_toSpanSingleton_map, Coalgebra.counit_comp_lid_comp_rTensor_comul]

/-- For a coalgebra's regular left coaction, applying the operator for `β` after
that for `α` gives the operator for the convolution product `α * β`.
The coefficient algebra may be noncommutative. -/
theorem lift_toSpanSingleton_comp_map_comul [Semiring A] [Algebra R A]
    (α β : WithConv (C →ₗ[R] A)) :
    (lift
      (LinearMap.toSpanSingleton A (C →ₗ[R] A ⊗[R] C)
        ((TensorProduct.map β.ofConv (LinearMap.id : C →ₗ[R] C)).comp
          (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)))).comp
      (lift
        (LinearMap.toSpanSingleton A (C →ₗ[R] A ⊗[R] C)
          ((TensorProduct.map α.ofConv (LinearMap.id : C →ₗ[R] C)).comp
            (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)))) =
      lift
        (LinearMap.toSpanSingleton A (C →ₗ[R] A ⊗[R] C)
          ((TensorProduct.map (α * β).ofConv (LinearMap.id : C →ₗ[R] C)).comp
            (Coalgebra.comul : C →ₗ[R] C ⊗[R] C))) := by
  have hCoassoc :
      (TensorProduct.map (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)
        (LinearMap.id : C →ₗ[R] C)).comp Coalgebra.comul =
      (TensorProduct.assoc R C C C).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) Coalgebra.comul).comp
          Coalgebra.comul) := by
    simpa only [LinearMap.rTensor_def, LinearMap.lTensor_def] using
      (Coalgebra.coassoc_symm (R := R) (A := C)).symm
  simpa only [LinearMap.convMul_def, WithConv.ofConv_toConv] using
    lift_toSpanSingleton_comp_map_of_coassoc
      (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) Coalgebra.comul α.ofConv β.ofConv hCoassoc

/-- The counit readback of two regular scalar coefficient operators is their
convolution product, with `β` applied after `α`. Both unitors are retained. -/
theorem counit_comp_lid_comp_lift_toSpanSingleton_comp_comul
    (α β : WithConv (C →ₗ[R] R)) :
    (Coalgebra.counit : C →ₗ[R] R).comp
      ((TensorProduct.lid R C).toLinearMap.comp
        (((lift
          (LinearMap.toSpanSingleton R (C →ₗ[R] R ⊗[R] C)
            ((TensorProduct.map β.ofConv (LinearMap.id : C →ₗ[R] C)).comp
              (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)))).comp
          (lift
            (LinearMap.toSpanSingleton R (C →ₗ[R] R ⊗[R] C)
              ((TensorProduct.map α.ofConv (LinearMap.id : C →ₗ[R] C)).comp
                (Coalgebra.comul : C →ₗ[R] C ⊗[R] C))))).comp
          (TensorProduct.lid R C).symm.toLinearMap)) = (α * β).ofConv := by
  rw [lift_toSpanSingleton_comp_map_comul,
    counit_comp_lid_comp_lift_toSpanSingleton_comul]

end TensorProduct.AlgebraTensorModule
