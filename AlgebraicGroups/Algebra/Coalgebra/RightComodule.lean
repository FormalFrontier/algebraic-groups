/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import AlgebraicGroups.Algebra.TensorProduct.Submodule
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Hom
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import Mathlib.RingTheory.Flat.Basic

/-!
# Projective-coalgebra finite containment and evaluation criteria

We use the canonical `TauCeti.Comodule`, `TauCeti.Comodule.Hom`, and
`TauCeti.Subcomodule` structures. The finite-containment results here require only
projectivity of the coefficient coalgebra. The algebra-valued stability criteria
require no flatness or finite-generation assumptions.

The constant-tensor construction allows a counit that acts as the identity on the
module without being equal to one in the scalar semiring.

The removed intertwining construction carried the following attribution, retained here:
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov, Edison Xie

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969.
* C. Kassel, *Quantum Groups*, §II.4.
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra

universe u v w z

namespace TauCeti.Comodule

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-- Coassociativity with the inverse associator. -/
@[simp] theorem coassoc_symm_apply (X : Comodule R C M) (m : M) :
    (TensorProduct.assoc R M C C).symm
        ((comul (R := R)).lTensor M (X.coact m)) =
      X.coact.rTensor C (X.coact m) := by
  rw [(TensorProduct.assoc R M C C).symm_apply_eq, (@Comodule.coassoc_apply R C M _ _ _ _ _ _ X)]

/-- Composing the right counit with the right unitor recovers the element. -/
theorem rid_counit_coact (X : Comodule R C M) (m : M) :
    TensorProduct.rid R M ((counit (R := R)).lTensor M (X.coact m)) = m := by
  simp only [(@Comodule.lTensor_counit_coact R C M _ _ _ _ _ _ X),
    TensorProduct.rid_tmul, one_smul]

/-- The coact is injective: applying the counit and right unitor cancels it. -/
theorem coact_injective (X : Comodule R C M) : Function.Injective X.coact := by
  intro m n h
  simpa only [X.rid_counit_coact] using
    congrArg (fun t : M ⊗[R] C ↦
      TensorProduct.rid R M ((counit (R := R)).lTensor M t)) h

/-- Equality of coacts is equality of elements. -/
@[simp] theorem coact_inj (X : Comodule R C M) {m n : M} :
    X.coact m = X.coact n ↔ m = n :=
  X.coact_injective.eq_iff

/-- A coact vanishes at an element exactly when that element is zero. -/
@[simp] theorem coact_eq_zero (X : Comodule R C M) {m : M} :
    X.coact m = 0 ↔ m = 0 :=
  X.coact.map_eq_zero_iff X.coact_injective

/-- Zero equals an element's coact exactly when zero equals that element. -/
@[simp] theorem zero_eq_coact (X : Comodule R C M) {m : M} :
    0 = X.coact m ↔ 0 = m := by
  rw [eq_comm, X.coact_eq_zero, eq_comm]

/-- The coact map is zero exactly when its underlying module is subsingleton. -/
@[simp] theorem coact_eq_zero_iff (X : Comodule R C M) :
    X.coact = 0 ↔ Subsingleton M := by
  constructor
  · intro h
    have hz (m : M) : m = 0 := X.coact_eq_zero.mp (LinearMap.congr_fun h m)
    exact ⟨fun m n ↦ (hz m).trans (hz n).symm⟩
  · intro h
    let := h
    ext m
    rw [Subsingleton.elim m 0]
    exact map_zero X.coact

/-- A constant-tensor coact. Counitality needs only that the counit of `e`
acts as the identity on `M`; it need not equal one in the scalar semiring. -/
@[instance_reducible] def ofTensor (e : C) (hcomul : comul (R := R) e = e ⊗ₜ[R] e)
    (hcounit : ∀ m : M, counit (R := R) e • m = m) : Comodule R C M where
  coact := (TensorProduct.mk R M C).flip e
  coassoc := by
    ext m
    simp [LinearMap.lTensor_tmul, hcomul]
  lTensor_counit_comp_coact := by
    ext m
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.lTensor_tmul, LinearMap.flip_apply, TensorProduct.mk_apply]
    calc
      m ⊗ₜ[R] counit (R := R) e = counit (R := R) e • (m ⊗ₜ[R] (1 : R)) := by
        rw [← TensorProduct.tmul_smul]
        simp
      _ = (counit (R := R) e • m) ⊗ₜ[R] (1 : R) := TensorProduct.smul_tmul' _ _ _
      _ = m ⊗ₜ[R] (1 : R) := by rw [hcounit]

@[simp] theorem ofTensor_coact (e : C) (hcomul hcounit) (m : M) :
    (ofTensor e hcomul hcounit : Comodule R C M).coact m = m ⊗ₜ[R] e := rfl

/-- Image stability of an existing submodule, without a chosen subtype coact. -/
def IsStable (X : Comodule R C M) (U : Submodule R M) : Prop :=
  ∀ m ∈ U, X.coact m ∈ LinearMap.range (U.subtype.rTensor C)

/-- The image-stability condition concerns every member of the submodule. -/
theorem isStable_iff (X : Comodule R C M) (U : Submodule R M) :
    X.IsStable U ↔ ∀ m ∈ U, X.coact m ∈ LinearMap.range (U.subtype.rTensor C) := Iff.rfl

/-- A stable submodule has a tensor-inclusion preimage for each member. -/
theorem IsStable.coact_mem_range {X : Comodule R C M} {U : Submodule R M}
    (h : X.IsStable U) (m : M) (hm : m ∈ U) :
    ∃ t : U ⊗[R] C, U.subtype.rTensor C t = X.coact m := h m hm

/-- Corestriction along the counit gives the scalar trivial coaction. -/
@[simp] theorem corestrict_counit [X : Comodule R C M] :
    Corestrict (M := M) (counitCoalgHom R C) = trivial (R := R) (C := R) (M := M) := by
  apply Comodule.ext
  rw [corestrict_coact, corestrictCoact_eq_lTensor, trivial_coact]
  exact X.lTensor_counit_comp_coact

/-- Every finite subset of a right comodule over a projective coalgebra is
contained in a module-finitely-generated submodule with a subtype coaction and
colinear inclusion. Stability holds for every member, not only for a chosen
generating set. This extends the
classical coefficient method for comodules from Sweedler's *Hopf Algebras*;
projectivity is imposed on the coalgebra, never on the ambient comodule. -/
theorem exists_fg_subcomodule_of_finite [Module.Projective R C]
    [X : Comodule R C M] {s : Set M} (hs : s.Finite) :
    ∃ U : Subcomodule R C M, s ⊆ (U : Set M) ∧ U.toSubmodule.FG := by
  obtain ⟨U, hsU, hfg, hstable⟩ :=
    exists_fg_submodule_coaction_right_closed_of_finite
      X.coact X.coassoc X.lTensor_counit_comp_coact hs
  refine ⟨{ carrier := U, coact_mem' := ?_ }, hsU, hfg⟩
  intro m hm
  simpa only [LinearMap.rTensor_def] using hstable m hm

variable [X : Comodule R C M]

/-- The underlying submodules of module-finite subcomodules are directed when
the coacting coalgebra is projective. -/
theorem directed_fg_toSubmodule [Module.Projective R C] :
    Directed (· ≤ ·)
      (fun U : {U : Subcomodule R C M // Module.Finite R U.toSubmodule} =>
        U.val.toSubmodule) := by
  intro U V
  have hfg : (U.val.toSubmodule ⊔ V.val.toSubmodule).FG :=
    (Module.Finite.iff_fg.mp U.property).sup (Module.Finite.iff_fg.mp V.property)
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  obtain ⟨W, hsW, hW⟩ := exists_fg_subcomodule_of_finite (R := R) (C := C) hs
  have hle : U.val.toSubmodule ⊔ V.val.toSubmodule ≤ W.toSubmodule := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsW
  exact ⟨⟨W, Module.Finite.iff_fg.mpr hW⟩,
    le_sup_left.trans hle, le_sup_right.trans hle⟩

/-- Every element lies in a module-finite subcomodule when the coacting
coalgebra is projective. -/
theorem iUnion_fg_eq_univ [Module.Projective R C] :
    (⋃ U : {U : Subcomodule R C M // Module.Finite R U.toSubmodule},
      (U.val : Set M)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro m
  obtain ⟨U, hmU, hU⟩ := exists_fg_subcomodule_of_finite (R := R) (C := C) (Set.finite_singleton m)
  exact ⟨⟨U, Module.Finite.iff_fg.mpr hU⟩, hmU (Set.mem_singleton m)⟩

end TauCeti.Comodule

/-! ## Algebra-valued evaluation and image stability -/

universe uR uC uM uA uB

namespace TauCeti.Comodule

variable {R₀ : Type uR} {C₀ : Type uC} {M₀ : Type uM}
variable [CommSemiring R₀] [CommSemiring C₀]
variable [Algebra R₀ C₀] [Coalgebra R₀ C₀]
variable [AddCommMonoid M₀] [Module R₀ M₀]

/-- Evaluation on a pure tensor uses the left scalar action: a coaction term
`mᵢ ⊗ cᵢ` contributes `(a * α cᵢ) ⊗ mᵢ`. -/
theorem evaluation_tmul
    (X : Comodule R₀ C₀ M₀)
    {A : Type uA} [CommSemiring A] [Algebra R₀ A]
    (α : C₀ →ₐ[R₀] A) (a : A) (m : M₀) :
    LinearMap.liftBaseChange A
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact))
        (a ⊗ₜ[R₀] m) =
      a • TensorProduct.map (AlgHom.toLinearMap α)
        (LinearMap.id : M₀ →ₗ[R₀] M₀)
        (TensorProduct.comm R₀ M₀ C₀ (X.coact m)) := by
  rw [LinearMap.liftBaseChange_tmul]
  rfl

/-- The identity one-tensor test recovers the commuted original coaction. -/
theorem id_evaluation_one_tmul
    (X : Comodule R₀ C₀ M₀) (m : M₀) :
    LinearMap.liftBaseChange C₀
        ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id R₀ C₀))
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact))
        (1 ⊗ₜ[R₀] m) =
      TensorProduct.comm R₀ M₀ C₀ (X.coact m) := by
  rw [LinearMap.liftBaseChange_one_tmul]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_id,
    TensorProduct.map_id, LinearMap.id_apply]
  rfl

/-- Evaluation is natural in its target algebra, as an equality of elements
of the target tensor product. The tensor transport is only `R₀`-linear. -/
theorem evaluation_naturality
    (X : Comodule R₀ C₀ M₀)
    {A : Type uA} {B : Type uB}
    [CommSemiring A] [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B]
    (α : C₀ →ₐ[R₀] A) (q : A →ₐ[R₀] B) (z : A ⊗[R₀] M₀) :
    TensorProduct.map (AlgHom.toLinearMap q)
        (LinearMap.id : M₀ →ₗ[R₀] M₀)
        (LinearMap.liftBaseChange A
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
            ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact)) z) =
      LinearMap.liftBaseChange B
        ((TensorProduct.map (AlgHom.toLinearMap (q.comp α))
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact))
        (TensorProduct.map (AlgHom.toLinearMap q)
          (LinearMap.id : M₀ →ₗ[R₀] M₀) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      have h (y : C₀ ⊗[R₀] M₀) :
          TensorProduct.map (AlgHom.toLinearMap q)
              (LinearMap.id : M₀ →ₗ[R₀] M₀)
              (a • TensorProduct.map (AlgHom.toLinearMap α)
                (LinearMap.id : M₀ →ₗ[R₀] M₀) y) =
            q a • TensorProduct.map (AlgHom.toLinearMap (q.comp α))
              (LinearMap.id : M₀ →ₗ[R₀] M₀) y := by
        induction y using TensorProduct.inductionOn with
        | tmul c n =>
            simp [TensorProduct.smul_tmul', smul_eq_mul]
        | add y y' hy hy' =>
            simpa only [map_add, smul_add] using
              congrArg₂ (fun x x' : B ⊗[R₀] M₀ => x + x') hy hy'
      simpa only [evaluation_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, LinearMap.id_apply] using
        h (TensorProduct.comm R₀ M₀ C₀ (X.coact m))
  | add z z' hz hz' =>
      simpa only [map_add] using
        congrArg₂ (fun x x' : B ⊗[R₀] M₀ => x + x') hz hz'

/-- Stability preserves the scalar-extension image under every one-algebra
evaluation, with the algebra universe independent of the coalgebra universe. -/
theorem IsStable.evaluation_mem_baseChange
    {X : Comodule R₀ C₀ M₀} {U : Submodule R₀ M₀}
    (hU : X.IsStable U)
    {A : Type uA} [CommSemiring A] [Algebra R₀ A]
    (α : C₀ →ₐ[R₀] A) (z : A ⊗[R₀] M₀) (hz : z ∈ U.baseChange A) :
    LinearMap.liftBaseChange A
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact)) z
      ∈ U.baseChange A := by
  have hmem (m : M₀) (hm : m ∈ U) :
      TensorProduct.map (AlgHom.toLinearMap α)
          (LinearMap.id : M₀ →ₗ[R₀] M₀)
          (TensorProduct.comm R₀ M₀ C₀ (X.coact m)) ∈ U.baseChange A := by
    exact U.map_mem_baseChange (AlgHom.toLinearMap α)
      ((TensorProduct.comm_mem_baseChange_iff U (X.coact m)).mpr
        (hU.coact_mem_range m hm))
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul a u =>
      rw [LinearMap.baseChange_tmul, evaluation_tmul]
      exact (U.baseChange A).smul_mem a (hmem (u : M₀) u.property)
  | add w w' hw hw' =>
      simpa only [map_add] using (U.baseChange A).add_mem hw hw'

/-- The identity-algebra evaluation criterion for image stability, with the
right-coaction convention of Sweedler, *Hopf Algebras*. No subtype coaction or
tensor-inclusion injectivity is required. -/
theorem isStable_iff_id_evaluation_mem_baseChange
    (X : Comodule R₀ C₀ M₀) (U : Submodule R₀ M₀) :
    X.IsStable U ↔
      ∀ z ∈ U.baseChange C₀,
        LinearMap.liftBaseChange C₀
          ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id R₀ C₀))
              (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
            ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact)) z
          ∈ U.baseChange C₀ := by
  constructor
  · intro hU z hz
    exact hU.evaluation_mem_baseChange (AlgHom.id R₀ C₀) z hz
  · intro h
    apply (X.isStable_iff U).2
    intro m hm
    apply (TensorProduct.comm_mem_baseChange_iff U (X.coact m)).mp
    rw [← X.id_evaluation_one_tmul m]
    exact h (1 ⊗ₜ[R₀] m) (Submodule.tmul_mem_baseChange_of_mem 1 hm)

/-- Image stability is detected by evaluations in all commutative algebras in
the compatible maximum universe, with the right-coaction convention of Sweedler,
*Hopf Algebras*. The lifted coefficient algebra supplies the detector without
restricting the independently universe-polymorphic forward implication. -/
theorem isStable_iff_forall_evaluation_mem_baseChange
    (X : Comodule R₀ C₀ M₀) (U : Submodule R₀ M₀) :
    X.IsStable U ↔
      ∀ (A : Type (max uC uA)) [CommSemiring A] [Algebra R₀ A]
          (α : C₀ →ₐ[R₀] A),
        ∀ z ∈ U.baseChange A,
          LinearMap.liftBaseChange A
            ((TensorProduct.map (AlgHom.toLinearMap α)
                (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
              ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coact)) z
            ∈ U.baseChange A := by
  constructor
  · intro hX A _ _ α z hz
    exact hX.evaluation_mem_baseChange (A := A) α z hz
  · intro h
    apply (X.isStable_iff U).2
    intro m hm
    let L : Type (max uC uA) := ULift.{uA} C₀
    let e : L ≃ₐ[R₀] C₀ := ULift.algEquiv (R := R₀) (A := C₀)
    let α : C₀ →ₐ[R₀] L := e.symm.toAlgHom
    let downM : L ⊗[R₀] M₀ →ₗ[R₀] C₀ ⊗[R₀] M₀ :=
      TensorProduct.map e.toLinearMap (LinearMap.id : M₀ →ₗ[R₀] M₀)
    have hcancel (y : C₀ ⊗[R₀] M₀) :
        downM (TensorProduct.map (AlgHom.toLinearMap α)
          (LinearMap.id : M₀ →ₗ[R₀] M₀) y) = y := by
      induction y using TensorProduct.inductionOn with
      | tmul c m' =>
          change e (e.symm c) ⊗ₜ[R₀] m' = c ⊗ₜ[R₀] m'
          rw [e.apply_symm_apply]
      | add x y hx hy =>
          simp only [map_add, hx, hy]
    have hz :=
      h L α ((1 : L) ⊗ₜ[R₀] m)
        (Submodule.tmul_mem_baseChange_of_mem (1 : L) hm)
    rw [LinearMap.liftBaseChange_one_tmul] at hz
    have hdown := U.map_mem_baseChange e.toLinearMap hz
    change downM (TensorProduct.map (AlgHom.toLinearMap α)
      (LinearMap.id : M₀ →ₗ[R₀] M₀)
      (TensorProduct.comm R₀ M₀ C₀ (X.coact m))) ∈ U.baseChange C₀ at hdown
    rw [hcancel] at hdown
    exact (TensorProduct.comm_mem_baseChange_iff U (X.coact m)).mp hdown

end TauCeti.Comodule

namespace TauCeti.Comodule.Hom

/-- The inverse of a linear equivalence intertwining two specified right coacts
intertwines those coacts in the opposite direction. -/
theorem colinear_symm {R : Type u} {C : Type v} {M : Type w} {N : Type z}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {X : Comodule R C M} {Y : Comodule R C N}
    (e : M ≃ₗ[R] N)
    (h : Y.coact ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coact) :
    X.coact ∘ₗ e.symm.toLinearMap = e.symm.toLinearMap.rTensor C ∘ₗ Y.coact := by
  rw [← LinearEquiv.coe_rTensor, ← LinearEquiv.symm_rTensor,
    LinearEquiv.eq_toLinearMap_symm_comp (e₁₂ := e.rTensor C),
    ← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq (e₁₂ := e),
    LinearEquiv.coe_rTensor]
  exact h.symm


variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Forget colinearity as a linear map on the module of comodule morphisms. -/
def toLinearMapₗ : Hom R C M N →ₗ[R] (M →ₗ[R] N) where
  toFun := toLinearMap
  map_add' := add_toLinearMap
  map_smul' := smul_toLinearMap

@[simp] theorem toLinearMapₗ_apply (f : Hom R C M N) :
    toLinearMapₗ f = f.toLinearMap := rfl

/-- The bundled linear forgetful map is injective. -/
theorem toLinearMapₗ_injective :
    Function.Injective (toLinearMapₗ (R := R) (C := C) (M := M) (N := N)) :=
  toLinearMap_injective

end TauCeti.Comodule.Hom
