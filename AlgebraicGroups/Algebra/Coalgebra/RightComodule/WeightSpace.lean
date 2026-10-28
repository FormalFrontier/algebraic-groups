/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Order.SupIndep
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Inverse relations on regular weight spaces

Tau Ceti supplies normalized group-like weight spaces and their independence.
This file retains the coaction equation for arbitrary coalgebra elements and its
preservation by comodule morphisms. The counit recovers the scalar multiple of
a chosen group-like vector in the regular comodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.22–4.26.
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra

universe u v

namespace TauCeti.Comodule

variable {R : Type u} {C : Type v}
variable {V : Type*}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V]

/-- The vectors with coact `v ↦ v ⊗ c`, for a specified coalgebra element `c`. -/
def elementWeightSpace (X : Comodule R C V) (c : C) : Submodule R V :=
  LinearMap.eqLocus X.coact ((TensorProduct.mk R V C).flip c)

/-- Membership in a weight space is the corresponding coact equation. -/
@[simp] theorem mem_elementWeightSpace (X : Comodule R C V) (c : C) {v : V} :
    v ∈ X.elementWeightSpace c ↔ X.coact v = v ⊗ₜ[R] c :=
  Iff.rfl

/-- The coact equation for an element of a weight space. -/
theorem coact_elementWeightSpace (X : Comodule R C V) (c : C) (v : X.elementWeightSpace c) :
    X.coact (v : V) = (v : V) ⊗ₜ[R] c :=
  (mem_elementWeightSpace X c).mp v.property

/-- The counit and scalar multiplication satisfy the inverse relations on a regular weight space.

For the motivating regular-weight viewpoint, see Milne, *Algebraic Groups* (2017), §§4.22–4.26.
The equations here concern a specified coalgebra coaction. -/
theorem regular_elementWeightSpace_inverse (g : GroupLike R C) :
    (∀ r : R, counit (R := R) (r • g.val) = r) ∧
      (∀ v : (Comodule.instSelf R C).elementWeightSpace g.val,
        (counit (R := R) (v : C)) • g.val = (v : C)) := by
  constructor
  · intro r
    rw [map_smul, g.isGroupLikeElem_val.counit_eq_one, smul_eq_mul, mul_one]
  · intro v
    have hv : comul (R := R) (v : C) = (v : C) ⊗ₜ[R] g.val :=
      (mem_elementWeightSpace (Comodule.instSelf R C) g.val).mp v.property
    have h := congrArg
      (fun t : C ⊗[R] C ↦
        TensorProduct.lid R C ((counit (R := R) (A := C)).rTensor C t)) hv
    simpa only [Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, one_smul] using h.symm


end TauCeti.Comodule

namespace TauCeti.Comodule.Hom

variable {R C V W : Type*}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [X : Comodule R C V]
variable [AddCommMonoid W] [Module R W] [Y : Comodule R C W]

/-- A comodule morphism preserves the weight space of any coalgebra element. -/
theorem map_mem_elementWeightSpace (f : Hom R C V W) (c : C) {v : V}
    (hv : v ∈ X.elementWeightSpace c) : f v ∈ Y.elementWeightSpace c := by
  rw [Comodule.mem_elementWeightSpace] at hv ⊢
  simpa only [hv, TensorProduct.map_tmul, LinearMap.id_apply, Hom.coe_toLinearMap] using
    (f.map_coact_apply v).symm

end TauCeti.Comodule.Hom
