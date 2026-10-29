/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotients of specified right comodules

For a specified right comodule `X` and an image-stable ordinary submodule `U`,
`Coalgebra.RightComodule.quotient` descends the coaction to the existing module
quotient `M ⧸ U`. The coefficient coalgebra is unchanged. Image stability alone
suffices: tensoring the quotient map kills the image of the subtype inclusion,
without any flatness or injectivity hypothesis.

`Coalgebra.RightComodule.mkQ` is the canonical surjective comodule morphism.
`Coalgebra.RightComoduleHom.liftQ` descends every colinear map vanishing on `U`,
and `Coalgebra.RightComoduleHom.existsUnique_liftQ` gives its universal property
in the existing type of specified-comodule morphisms. The target of descent
needs only an additive commutative monoid structure; its module structure over
the scalar ring supplies the additive group used internally by the linear lift.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommGroup M] [Module R M]

/-- The specified coaction on the module quotient by an image-stable submodule.
The coefficient coalgebra remains `C`; no coaction on the subtype is chosen. -/
def quotient (X : RightComodule R C M) (U : Submodule R M) (hU : X.IsStable U) :
    RightComodule R C (M ⧸ U) := by
  have hzero : U ≤ LinearMap.ker ((U.mkQ.rTensor C) ∘ₗ X.coaction) := by
    intro m hm
    obtain ⟨t, ht⟩ := hU.coaction_mem_range m hm
    have hq : U.mkQ ∘ₗ U.subtype = 0 := by
      apply LinearMap.ext
      intro x
      change (Submodule.Quotient.mk (x : M) : M ⧸ U) = 0
      exact (Submodule.Quotient.mk_eq_zero U).2 x.property
    change U.mkQ.rTensor C (X.coaction m) = 0
    rw [← ht]
    change (U.mkQ.rTensor C ∘ₗ U.subtype.rTensor C) t = 0
    rw [← LinearMap.rTensor_comp, hq, LinearMap.rTensor_zero, LinearMap.zero_apply]
  let ρQ : (M ⧸ U) →ₗ[R] (M ⧸ U) ⊗[R] C :=
    U.liftQ ((U.mkQ.rTensor C) ∘ₗ X.coaction) hzero
  have hρQ : ρQ ∘ₗ U.mkQ = U.mkQ.rTensor C ∘ₗ X.coaction :=
    U.liftQ_mkQ _ hzero
  have hρT : ρQ.rTensor C ∘ₗ U.mkQ.rTensor C =
      (U.mkQ.rTensor C).rTensor C ∘ₗ X.coaction.rTensor C := by
    rw [← LinearMap.rTensor_comp, hρQ, LinearMap.rTensor_comp]
  have hassoc :
      TensorProduct.assoc R (M ⧸ U) C C ∘ₗ (U.mkQ.rTensor C).rTensor C =
        U.mkQ.rTensor (C ⊗[R] C) ∘ₗ TensorProduct.assoc R M C C := by
    simpa only [LinearMap.rTensor, TensorProduct.map_id] using
      (TensorProduct.map_map_comp_assoc_eq U.mkQ
        (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)).symm
  refine { coaction := ρQ, coassoc := ?_, counit_comp := ?_ }
  · apply U.linearMap_qext
    calc
      (TensorProduct.assoc R (M ⧸ U) C C ∘ₗ ρQ.rTensor C ∘ₗ ρQ) ∘ₗ U.mkQ =
          TensorProduct.assoc R (M ⧸ U) C C ∘ₗ
            (ρQ.rTensor C ∘ₗ U.mkQ.rTensor C) ∘ₗ X.coaction := by
        simp only [LinearMap.comp_assoc, hρQ]
      _ = TensorProduct.assoc R (M ⧸ U) C C ∘ₗ
            ((U.mkQ.rTensor C).rTensor C ∘ₗ X.coaction.rTensor C) ∘ₗ X.coaction := by
        rw [hρT]
      _ = U.mkQ.rTensor (C ⊗[R] C) ∘ₗ
            (TensorProduct.assoc R M C C ∘ₗ X.coaction.rTensor C ∘ₗ X.coaction) := by
        simp only [← LinearMap.comp_assoc, hassoc]
      _ = U.mkQ.rTensor (C ⊗[R] C) ∘ₗ
            ((comul (R := R) (A := C)).lTensor M ∘ₗ X.coaction) := by
        rw [X.coassoc]
      _ = (comul (R := R) (A := C)).lTensor (M ⧸ U) ∘ₗ
            (U.mkQ.rTensor C ∘ₗ X.coaction) := by
        simp only [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
          LinearMap.lTensor_comp_rTensor]
      _ = ((comul (R := R) (A := C)).lTensor (M ⧸ U) ∘ₗ ρQ) ∘ₗ U.mkQ := by
        simp only [LinearMap.comp_assoc, hρQ]
  · apply U.linearMap_qext
    calc
      ((counit (R := R) (A := C)).lTensor (M ⧸ U) ∘ₗ ρQ) ∘ₗ U.mkQ =
          (counit (R := R) (A := C)).lTensor (M ⧸ U) ∘ₗ
            (U.mkQ.rTensor C ∘ₗ X.coaction) := by
        simp only [LinearMap.comp_assoc, hρQ]
      _ = U.mkQ.rTensor R ∘ₗ
            ((counit (R := R) (A := C)).lTensor M ∘ₗ X.coaction) := by
        simp only [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
          LinearMap.lTensor_comp_rTensor]
      _ = U.mkQ.rTensor R ∘ₗ (TensorProduct.rid R M).symm.toLinearMap := by
        rw [X.counit_comp]
      _ = (TensorProduct.rid R (M ⧸ U)).symm.toLinearMap ∘ₗ U.mkQ := by
        ext m
        simp

/-- The quotient coaction on representatives. -/
@[simp] theorem quotient_coaction_mkQ (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) (m : M) :
    (X.quotient U hU).coaction (Submodule.Quotient.mk m) =
      U.mkQ.rTensor C (X.coaction m) := rfl

/-- The defining linear-map identity for the quotient coaction. -/
@[simp] theorem quotient_coaction_comp_mkQ (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) :
    (X.quotient U hU).coaction ∘ₗ U.mkQ = U.mkQ.rTensor C ∘ₗ X.coaction := by
  ext m
  rfl

/-- The canonical colinear map to the quotient by an image-stable submodule. -/
def mkQ (X : RightComodule R C M) (U : Submodule R M) (hU : X.IsStable U) :
    RightComoduleHom X (X.quotient U hU) where
  toLinearMap := U.mkQ
  colinear := X.quotient_coaction_comp_mkQ U hU

@[simp] theorem mkQ_toLinearMap (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) : (X.mkQ U hU).toLinearMap = U.mkQ := rfl

@[simp] theorem mkQ_apply (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) (m : M) : X.mkQ U hU m = U.mkQ m := rfl

/-- The canonical quotient morphism is surjective. -/
theorem mkQ_surjective (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) : Function.Surjective (X.mkQ U hU) := U.mkQ_surjective

/-- Any linear map on the module quotient satisfying the defining composite
identity is the quotient coaction. No coaction laws are assumed for `ρ'`. -/
theorem quotient_coaction_unique (X : RightComodule R C M) (U : Submodule R M)
    (hU : X.IsStable U) (ρ' : (M ⧸ U) →ₗ[R] (M ⧸ U) ⊗[R] C)
    (hρ' : ρ' ∘ₗ U.mkQ = U.mkQ.rTensor C ∘ₗ X.coaction) :
    ρ' = (X.quotient U hU).coaction := by
  apply U.linearMap_qext
  exact hρ'.trans (X.quotient_coaction_comp_mkQ U hU).symm

end RightComodule

namespace RightComoduleHom

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommGroup M] [Module R M]

section AddCommMonoid

variable [AddCommMonoid N] [Module R N]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

/-- Colinear descent to the quotient by an image-stable submodule contained in
the kernel. The additive group structure on the target is supplied internally
by its module structure over the ring `R`. -/
def liftQ (f : RightComoduleHom X Y) (U : Submodule R M) (hU : X.IsStable U)
    (hf : U ≤ LinearMap.ker f.toLinearMap) : RightComoduleHom (X.quotient U hU) Y := by
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let g : (M ⧸ U) →ₗ[R] N := U.liftQ f.toLinearMap hf
  have hg : g ∘ₗ U.mkQ = f.toLinearMap := U.liftQ_mkQ _ hf
  refine { toLinearMap := g, colinear := ?_ }
  apply U.linearMap_qext
  calc
    (Y.coaction ∘ₗ g) ∘ₗ U.mkQ = Y.coaction ∘ₗ f.toLinearMap := by
      rw [LinearMap.comp_assoc, hg]
    _ = f.toLinearMap.rTensor C ∘ₗ X.coaction := f.colinear
    _ = (g ∘ₗ U.mkQ).rTensor C ∘ₗ X.coaction := by rw [hg]
    _ = g.rTensor C ∘ₗ (U.mkQ.rTensor C ∘ₗ X.coaction) := by
      rw [LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (g.rTensor C ∘ₗ (X.quotient U hU).coaction) ∘ₗ U.mkQ := by
      rw [LinearMap.comp_assoc, X.quotient_coaction_comp_mkQ U hU]

/-- The descended morphism agrees with the original map on representatives. -/
@[simp] theorem liftQ_mkQ (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap) (m : M) :
    f.liftQ U hU hf (Submodule.Quotient.mk m) = f m := rfl

/-- The underlying linear map of descent factors the original linear map.
This identity needs no additive-group hypothesis on the target. -/
@[simp] theorem liftQ_toLinearMap_comp_mkQ (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap) :
    (f.liftQ U hU hf).toLinearMap ∘ₗ U.mkQ = f.toLinearMap := by
  ext m
  rfl

/-- Colinear descent composed with the canonical quotient morphism is the original morphism. -/
@[simp] theorem liftQ_comp_mkQ (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap) :
    (f.liftQ U hU hf).comp (X.mkQ U hU) = f := by
  apply RightComoduleHom.ext
  intro m
  rfl

/-- A morphism out of the quotient with the prescribed composite is the canonical descent. -/
theorem liftQ_unique (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap)
    (g : RightComoduleHom (X.quotient U hU) Y) (hg : g.comp (X.mkQ U hU) = f) :
    g = f.liftQ U hU hf := by
  apply RightComoduleHom.ext
  intro x
  obtain ⟨m, rfl⟩ := U.mkQ_surjective x
  change g (U.mkQ m) = f m
  exact congrArg (fun k : RightComoduleHom X Y => k m) hg

/-- Every colinear map vanishing on the stable submodule factors uniquely through
its specified quotient comodule. -/
theorem existsUnique_liftQ (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap) :
    ∃! g : RightComoduleHom (X.quotient U hU) Y, g.comp (X.mkQ U hU) = f := by
  refine ⟨f.liftQ U hU hf, f.liftQ_comp_mkQ U hU hf, ?_⟩
  intro g hg
  exact f.liftQ_unique U hU hf g hg

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup N] [Module R N]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

/-- With explicit additive-group data on the target, the underlying linear map
of colinear descent is Mathlib's ordinary quotient lift. The equality follows
on representatives, independently of the additive-group structure used internally. -/
@[simp] theorem liftQ_toLinearMap (f : RightComoduleHom X Y) (U : Submodule R M)
    (hU : X.IsStable U) (hf : U ≤ LinearMap.ker f.toLinearMap) :
    (f.liftQ U hU hf).toLinearMap = U.liftQ f.toLinearMap hf := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := U.mkQ_surjective x
  exact (f.liftQ_mkQ U hU hf m).trans
    (Submodule.liftQ_apply U f.toLinearMap (h := hf) m).symm

end AddCommGroup

end RightComoduleHom

end Coalgebra
