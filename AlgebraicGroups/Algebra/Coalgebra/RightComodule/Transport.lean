/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Transport of specified right comodules along linear equivalences

`Coalgebra.RightComodule.transport` changes the module carrying a specified
right coaction along an `R`-linear equivalence `e : V ≃ₗ[R] W`. The coalgebra
`C` and all given additive and scalar-module structures remain fixed. The new
coaction is `(e tensor id_C) ∘ ρ ∘ e.symm`: only the first tensor factor changes.

The constructor works over a commutative semiring, for additive commutative
monoid modules, with independent universes for the scalars, coalgebra and two
carriers. It needs no flatness, projectivity, basis or finiteness assumption.
`transport_coaction` and `transport_coaction_apply` read back its coaction.

## References

Mathlib supplies `LinearEquiv.arrowCongr`, tensor extensions, associators,
unitors and their naturality laws. The construction retains the earlier
project raw-conjugation and tensor-naturality proof approach for specified
right comodules, including its closed coassociativity and counit arguments.
-/

@[expose] public section

universe uR uC uV uW

open scoped TensorProduct

namespace Coalgebra.RightComodule

noncomputable section

section Conjugation

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Conjugation of a specified coaction, changing only its module factor. -/
private def conjugatedCoaction (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    W →ₗ[R] W ⊗[R] C :=
  LinearEquiv.arrowCongr e (e.rTensor C) X.coaction

private theorem conjugatedCoaction_coassoc (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (TensorProduct.assoc R W C C).toLinearMap ∘ₗ (conjugatedCoaction X e).rTensor C ∘ₗ
        conjugatedCoaction X e =
      (comul (R := R) (A := C)).lTensor W ∘ₗ conjugatedCoaction X e := by
  have hconj (w : W) : conjugatedCoaction X e w =
      e.toLinearMap.rTensor C (X.coaction (e.symm w)) := by
    rfl
  have hcolinear : conjugatedCoaction X e ∘ₗ e.toLinearMap =
      e.toLinearMap.rTensor C ∘ₗ X.coaction := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hconj,
      LinearEquiv.symm_apply_apply]
  have htensor : (conjugatedCoaction X e).rTensor C ∘ₗ e.toLinearMap.rTensor C =
      (e.toLinearMap.rTensor C).rTensor C ∘ₗ X.coaction.rTensor C := by
    rw [← LinearMap.rTensor_comp, hcolinear, LinearMap.rTensor_comp]
  have hassoc : (TensorProduct.assoc R W C C).toLinearMap ∘ₗ
        (e.toLinearMap.rTensor C).rTensor C =
      e.toLinearMap.rTensor (C ⊗[R] C) ∘ₗ (TensorProduct.assoc R V C C).toLinearMap := by
    simpa only [LinearMap.rTensor_def, TensorProduct.map_id] using
      (TensorProduct.map_map_comp_assoc_eq e.toLinearMap
        (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)).symm
  have hcomul : e.toLinearMap.rTensor (C ⊗[R] C) ∘ₗ (comul (R := R) (A := C)).lTensor V =
      (comul (R := R) (A := C)).lTensor W ∘ₗ e.toLinearMap.rTensor C := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  ext w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hconj]
  calc
    TensorProduct.assoc R W C C
        ((conjugatedCoaction X e).rTensor C
          (e.toLinearMap.rTensor C (X.coaction (e.symm w)))) =
        TensorProduct.assoc R W C C
          ((e.toLinearMap.rTensor C).rTensor C
            (X.coaction.rTensor C (X.coaction (e.symm w)))) := by
      congr 1
      exact LinearMap.congr_fun htensor (X.coaction (e.symm w))
    _ = e.toLinearMap.rTensor (C ⊗[R] C)
        (TensorProduct.assoc R V C C
          (X.coaction.rTensor C (X.coaction (e.symm w)))) :=
      LinearMap.congr_fun hassoc (X.coaction.rTensor C (X.coaction (e.symm w)))
    _ = e.toLinearMap.rTensor (C ⊗[R] C)
        ((comul (R := R) (A := C)).lTensor V (X.coaction (e.symm w))) := by
      rw [X.coassoc_apply]
    _ = (comul (R := R) (A := C)).lTensor W
        (e.toLinearMap.rTensor C (X.coaction (e.symm w))) :=
      LinearMap.congr_fun hcomul (X.coaction (e.symm w))

private theorem conjugatedCoaction_counit_comp (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (counit (R := R) (A := C)).lTensor W ∘ₗ conjugatedCoaction X e =
      (TensorProduct.rid R W).symm.toLinearMap := by
  have hnatural :
      (counit (R := R) (A := C)).lTensor W ∘ₗ (e.rTensor C).toLinearMap =
        (e.rTensor R).toLinearMap ∘ₗ (counit (R := R) (A := C)).lTensor V := by
    simp only [LinearEquiv.coe_rTensor, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, conjugatedCoaction, LinearEquiv.arrowCongr_apply,
    LinearEquiv.coe_coe]
  calc
    (counit (R := R) (A := C)).lTensor W ((e.rTensor C) (X.coaction (e.symm w))) =
        (e.rTensor R)
          ((counit (R := R) (A := C)).lTensor V (X.coaction (e.symm w))) :=
      LinearMap.congr_fun hnatural _
    _ = (e.rTensor R) ((TensorProduct.rid R V).symm (e.symm w)) :=
      congrArg (e.rTensor R) (LinearMap.congr_fun X.counit_comp (e.symm w))
    _ = (TensorProduct.rid R W).symm w := by
      simp only [TensorProduct.rid_symm_apply, LinearEquiv.rTensor_tmul,
        LinearEquiv.apply_symm_apply]


/-- Transport a specified right `C`-comodule along an `R`-linear equivalence of
its carrier, keeping `C` and the given module structures fixed. -/
@[no_expose]
def transport (X : RightComodule R C V) (e : V ≃ₗ[R] W) : RightComodule R C W where
  coaction := conjugatedCoaction X e
  coassoc := conjugatedCoaction_coassoc X e
  counit_comp := conjugatedCoaction_counit_comp X e

/-- The transported coaction is arrow congruence on the source coaction,
with the equivalence extended only on the module tensor factor. -/
theorem transport_coaction (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (X.transport e).coaction = LinearEquiv.arrowCongr e (e.rTensor C) X.coaction := (rfl)

/-- At a target vector, transport first applies the inverse carrier equivalence,
then the original coaction, then the equivalence on the first tensor factor. -/
theorem transport_coaction_apply (X : RightComodule R C V) (e : V ≃ₗ[R] W) (w : W) :
    (X.transport e).coaction w = e.toLinearMap.rTensor C (X.coaction (e.symm w)) := (rfl)

end Conjugation

end

end Coalgebra.RightComodule
