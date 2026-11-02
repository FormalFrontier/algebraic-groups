/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
public import AlgebraicGroups.Algebra.HopfAlgebra.AntipodeSquare

/-!
# Bidual coactions and the square of the antipode

For a specified right comodule on a finite projective module, canonical evaluation
identifies its bidual with the original coaction twisted on the coefficient factor
by the square of the antipode. The coefficient Hopf algebra need not be commutative,
and its antipode need not be invertible. For commutative coefficients the twist is
the identity.

## References

* Mathlib, `LinearAlgebra/Contraction` and `LinearAlgebra/Dual/Lemmas`: the
  finite-projective tensor--Hom equivalence and canonical bidual equivalence.
* `AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual`: the characteristic
  contraction identity for dual coactions.
* `AlgebraicGroups.Algebra.HopfAlgebra.AntipodeSquare`: the square of the antipode
  as a bialgebra endomorphism.
-/

@[expose] public section

open Module TensorProduct

universe uR uC uV

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {V : Type uV}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]
variable [Module.Finite R V] [Module.Projective R V]

section HopfAlgebra

variable [Semiring C] [HopfAlgebra R C]

/-- The bidual coaction at canonical evaluation is the original coaction with
canonical evaluation on the module factor and the antipode square on coefficients. -/
theorem dual_dual_coaction_eval (X : Coalgebra.RightComodule R C V) (v : V) :
    (dual (dual X)).coaction (Module.Dual.eval R V v) =
      _root_.TensorProduct.map (Module.Dual.eval R V)
        ((HopfAlgebra.antipode R (A := C)).comp
          (HopfAlgebra.antipode R (A := C))) (X.coaction v) := by
  apply (dualTensorHomEquiv R (Module.Dual R V) C).injective
  change dualTensorHom R (Module.Dual R V) C
      ((dual (dual X)).coaction (Module.Dual.eval R V v)) = _
  ext f
  rw [dual_coaction, dualCoaction_characteristic, dualContraction_eval,
    dual_coaction, dualCoaction_characteristic]
  have hmap (t : V ⊗[R] C) :
      dualTensorHom R (Module.Dual R V) C
          (_root_.TensorProduct.map (Module.Dual.eval R V)
            ((HopfAlgebra.antipode R (A := C)).comp
              (HopfAlgebra.antipode R (A := C))) t) f =
        HopfAlgebra.antipode R (A := C)
          (HopfAlgebra.antipode R (A := C) (dualContraction f t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul v c => simp
    | add t t' ht ht' => simp [ht, ht']
  exact (hmap (X.coaction v)).symm

/-- Canonical evaluation intertwines the bidual coaction with the antipode-square
twist, as an equality of linear maps. -/
theorem dual_dual_coaction_comp_eval (X : Coalgebra.RightComodule R C V) :
    (dual (dual X)).coaction ∘ₗ Module.Dual.eval R V =
      _root_.TensorProduct.map (Module.Dual.eval R V)
        ((HopfAlgebra.antipode R (A := C)).comp
          (HopfAlgebra.antipode R (A := C))) ∘ₗ X.coaction := by
  ext v
  exact dual_dual_coaction_eval X v

/-- The bidual is the transport, along canonical bidual evaluation, of the original
comodule after changing coefficients by the antipode-square coalgebra map. -/
theorem dual_dual_eq_transport (X : Coalgebra.RightComodule R C V) :
    dual (dual X) =
      (X.mapCoalgebra
        (BialgHom.toCoalgHom (HopfAlgebra.antipodeSquareBialgHom R C))).transport
        (Module.evalEquiv R V) := by
  symm
  apply (transport_eq_iff_colinear _ _ _).2
  rw [Module.evalEquiv_toLinearMap, dual_dual_coaction_comp_eval,
    mapCoalgebra_coaction]
  rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor]
  exact congrArg (fun s : C →ₗ[R] C =>
    _root_.TensorProduct.map (Module.Dual.eval R V) s ∘ₗ X.coaction)
    (HopfAlgebra.antipodeSquareBialgHom_toLinearMap R C).symm

end HopfAlgebra

section Commutative

variable [CommSemiring C] [HopfAlgebra R C]

/-- For commutative Hopf coefficients, canonical bidual evaluation transports the
original specified comodule to its bidual without a coefficient twist. -/
theorem dual_dual_eq_transport_of_comm (X : Coalgebra.RightComodule R C V) :
    dual (dual X) = X.transport (Module.evalEquiv R V) := by
  have hid : (BialgHom.id R C).toCoalgHom = CoalgHom.id R C := rfl
  simpa only [HopfAlgebra.antipodeSquareBialgHom_eq_id, hid, mapCoalgebra_id]
    using dual_dual_eq_transport X

end Commutative

end Coalgebra.RightComodule
