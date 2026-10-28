/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Equalities characterizing transport of comodules

The underlying comodule structure, transported morphisms, and their evaluation laws
are provided by Tau Ceti. We record functoriality of the transported structures and
the criterion expressing transport as colinearity of the chosen linear equivalence.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uV uW uZ

namespace TauCeti.Comodule

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable [X : Comodule R C V]

/-- Transport along the identity leaves the specified comodule unchanged. -/
@[simp] theorem transport_refl : Transport (C := C) (LinearEquiv.refl R V) = X := by
  apply Comodule.ext
  ext v
  simp

/-- Successive carrier transport agrees with transport along the composite. -/
theorem transport_trans {Z : Type uZ} [AddCommMonoid Z] [Module R Z]
    (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] Z) :
    (letI := Transport (C := C) e; Transport (C := C) f) =
      Transport (C := C) (e.trans f) := by
  apply Comodule.ext
  ext z
  simp [TensorProduct.map_map]

/-- Transporting back along the inverse recovers the original comodule. -/
@[simp] theorem transport_symm (e : V ≃ₗ[R] W) :
    (letI := Transport (C := C) e; Transport (C := C) e.symm) = X := by
  rw [transport_trans, LinearEquiv.self_trans_symm, transport_refl]

/-- A target coaction is the transported one precisely when the equivalence is colinear. -/
theorem transport_eq_iff_colinear (e : V ≃ₗ[R] W) (Y : Comodule R C W) :
    Transport (C := C) e = Y ↔
      Y.coact ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coact := by
  constructor
  · intro h
    subst Y
    ext v
    simp [LinearMap.rTensor_def]
  · intro h
    apply Comodule.ext
    ext w
    rw [transport_coact_apply]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.rTensor_def] using
      (LinearMap.congr_fun h (e.symm w)).symm

end TauCeti.Comodule
