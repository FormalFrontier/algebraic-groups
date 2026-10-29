/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual coactions on finite projective modules

For a specified right comodule, its dual coaction is obtained from the global
finite-projective tensor--Hom equivalence. The functional is contracted against
the original coaction before applying the antipode. No basis is part of the API.
-/

@[expose] public section

open Module TensorProduct

universe u v w x y

namespace Coalgebra.RightComodule

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

section Contraction

variable [AddCommMonoid C] [Module R C]

/-- Contract the first tensor factor against a functional. -/
def dualContraction : Module.Dual R V →ₗ[R] (V ⊗[R] C →ₗ[R] C) where
  toFun f := (_root_.TensorProduct.lid R C).toLinearMap ∘ₗ f.rTensor C
  map_add' f g := by
    ext v c
    simp
  map_smul' a f := by
    ext v c
    simp [smul_smul]

theorem dualContraction_apply (f : Module.Dual R V) (t : V ⊗[R] C) :
    dualContraction (C := C) f t = _root_.TensorProduct.lid R C (f.rTensor C t) := rfl

@[simp] theorem dualContraction_tmul (f : Module.Dual R V) (v : V) (c : C) :
    dualContraction (C := C) f (v ⊗ₜ[R] c) = f v • c := by
  simp [dualContraction]

/-- Contracting after pullback of a functional is the same as contracting after
the corresponding tensor map. -/
theorem dualContraction_dualMap {W : Type x} [AddCommMonoid W] [Module R W]
    (h : V →ₗ[R] W) (f : Module.Dual R W) :
    dualContraction (C := C) (h.dualMap f) =
      dualContraction (C := C) f ∘ₗ h.rTensor C := by
  ext v c
  simp [dualContraction]

end Contraction

variable [Semiring C] [HopfAlgebra R C]
variable [Module.Finite R V] [Module.Projective R V]

/-- The canonical raw dual coaction of a specified right comodule. -/
noncomputable def dualCoaction (X : Coalgebra.RightComodule R C V) :
    Module.Dual R V →ₗ[R] Module.Dual R V ⊗[R] C :=
  (dualTensorHomEquiv R V C).symm.toLinearMap ∘ₗ
    (HopfAlgebra.antipode R (A := C)).compRight R ∘ₗ
    X.coaction.lcomp R C ∘ₗ dualContraction

/-- The defining formula uses the inverse of the global tensor--Hom equivalence. -/
theorem dualCoaction_def (X : Coalgebra.RightComodule R C V) (f : Module.Dual R V) :
    dualCoaction X f = (dualTensorHomEquiv R V C).symm
      (HopfAlgebra.antipode R (A := C) ∘ₗ dualContraction f ∘ₗ X.coaction) := rfl

/-- The characteristic identity as an equality of linear maps. -/
@[simp] theorem dualTensorHom_dualCoaction (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) :
    dualTensorHom R V C (dualCoaction X f) =
      HopfAlgebra.antipode R (A := C) ∘ₗ dualContraction f ∘ₗ X.coaction := by
  rw [dualCoaction_def, dualTensorHom_dualTensorHomEquiv_symm]

/-- The characteristic identity, valid for every functional and every vector. -/
theorem dualCoaction_characteristic (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (v : V) :
    dualTensorHom R V C (dualCoaction X f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v)) := by
  rw [dualTensorHom_dualCoaction]
  rfl

/-- Pointwise contraction characterizes each tensor in the dual coaction. -/
theorem eq_dualCoaction_iff (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (t : Module.Dual R V ⊗[R] C) :
    t = dualCoaction X f ↔ ∀ v : V, dualTensorHom R V C t v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v)) := by
  constructor
  · rintro rfl v
    exact dualCoaction_characteristic X f v
  · intro h
    apply (dualTensorHomEquiv R V C).injective
    change dualTensorHom R V C t = dualTensorHom R V C (dualCoaction X f)
    ext v
    exact (h v).trans (dualCoaction_characteristic X f v).symm

/-- A linear map with the characteristic identity is the canonical dual coaction. -/
theorem dualCoaction_unique (X : Coalgebra.RightComodule R C V)
    (rho : Module.Dual R V →ₗ[R] Module.Dual R V ⊗[R] C)
    (h : ∀ (f : Module.Dual R V) (v : V), dualTensorHom R V C (rho f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v))) :
    rho = dualCoaction X := by
  ext f
  exact (eq_dualCoaction_iff X f (rho f)).2 (h f)

/-- A specified comodule satisfying the characteristic identity has this raw coaction. -/
theorem coaction_eq_dualCoaction (X : Coalgebra.RightComodule R C V)
    (Y : Coalgebra.RightComodule R C (Module.Dual R V))
    (h : ∀ (f : Module.Dual R V) (v : V), dualTensorHom R V C (Y.coaction f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v))) :
    Y.coaction = dualCoaction X :=
  dualCoaction_unique X Y.coaction h

/-- The characteristic identity determines a comodule structure uniquely. -/
theorem dual_structure_unique (X : Coalgebra.RightComodule R C V)
    (Y Z : Coalgebra.RightComodule R C (Module.Dual R V))
    (hY : ∀ (f : Module.Dual R V) (v : V), dualTensorHom R V C (Y.coaction f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v)))
    (hZ : ∀ (f : Module.Dual R V) (v : V), dualTensorHom R V C (Z.coaction f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v))) :
    Y = Z := by
  apply Coalgebra.RightComodule.ext
  exact (coaction_eq_dualCoaction X Y hY).trans (coaction_eq_dualCoaction X Z hZ).symm

/-- Any finite tensor presentation of the original coaction gives a dual normal form. -/
theorem dualCoaction_characteristic_of_eq_sum (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (v : V) {ι : Type*} (s : Finset ι)
    (a : ι → V) (c : ι → C) (h : X.coaction v = ∑ i ∈ s, a i ⊗ₜ[R] c i) :
    dualTensorHom R V C (dualCoaction X f) v =
      ∑ i ∈ s, f (a i) • HopfAlgebra.antipode R (A := C) (c i) := by
  rw [dualCoaction_characteristic, h]
  simp

/-- A pure tensor presentation of the original coaction gives the coefficient
of the dual coaction directly. -/
theorem dualCoaction_characteristic_of_eq_tmul (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (v w : V) (c : C) (h : X.coaction v = w ⊗ₜ[R] c) :
    dualTensorHom R V C (dualCoaction X f) v =
      f w • HopfAlgebra.antipode R (A := C) c := by
  rw [dualCoaction_characteristic, h]
  simp

/-- For a coaction with one fixed coefficient, the dual coefficient is its
antipode. This normal form does not choose a basis for the module. -/
theorem dualCoaction_eq_tmul_of_coaction_eq_tmul (X : Coalgebra.RightComodule R C V)
    (c : C) (h : ∀ v : V, X.coaction v = v ⊗ₜ[R] c) (f : Module.Dual R V) :
    dualCoaction X f = f ⊗ₜ[R] HopfAlgebra.antipode R (A := C) c := by
  symm
  apply (eq_dualCoaction_iff X f _).2
  intro v
  simp [h v]

omit [Module.Finite R V] [Module.Projective R V] in
private theorem dualTensorHom_assoc_tmul (t : Module.Dual R V ⊗[R] C)
    (c : C) (v : V) :
    dualTensorHom R V (C ⊗[R] C)
        (_root_.TensorProduct.assoc R (Module.Dual R V) C C (t ⊗ₜ[R] c)) v =
      dualTensorHom R V C t v ⊗ₜ[R] c := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul f a => simp [_root_.TensorProduct.smul_tmul']
  | add t t' ht ht' => simp [ht, ht', _root_.TensorProduct.add_tmul]

private theorem dualTensorHom_assoc_dualCoaction_rTensor
    (X : Coalgebra.RightComodule R C V) (t : Module.Dual R V ⊗[R] C) (v : V) :
    dualTensorHom R V (C ⊗[R] C)
        (_root_.TensorProduct.assoc R (Module.Dual R V) C C
          ((dualCoaction X).rTensor C t)) v =
      _root_.TensorProduct.comm R C C
        (_root_.TensorProduct.map (dualTensorHom R V C t)
          (HopfAlgebra.antipode R (A := C)) (X.coaction v)) := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul f c =>
    simp only [LinearMap.rTensor_tmul, dualTensorHom_assoc_tmul,
      dualCoaction_characteristic]
    induction X.coaction v using _root_.TensorProduct.inductionOn with
    | tmul w a => simp [_root_.TensorProduct.smul_tmul', _root_.TensorProduct.tmul_smul]
    | add z z' hz hz' => simp [hz, hz', _root_.TensorProduct.add_tmul]
  | add t t' ht ht' => simp [ht, ht', _root_.TensorProduct.map_add_left]

omit [Module.Finite R V] [Module.Projective R V] in
private theorem dualContraction_comul (f : Module.Dual R V) (z : V ⊗[R] C) :
    (dualContraction f).rTensor C
        ((_root_.TensorProduct.assoc R V C C).symm
          ((Coalgebra.comul (R := R) (A := C)).lTensor V z)) =
      Coalgebra.comul (R := R) (dualContraction f z) := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul w c =>
    simp only [LinearMap.lTensor_tmul, dualContraction_tmul, map_smul]
    generalize Coalgebra.comul (R := R) c = t
    induction t using _root_.TensorProduct.inductionOn with
    | tmul a b => simp [_root_.TensorProduct.smul_tmul']
    | add t t' ht ht' => simp [ht, ht', _root_.TensorProduct.tmul_add, smul_add]
  | add z z' hz hz' => simp [hz, hz']

omit [Module.Finite R V] [Module.Projective R V] in
/-- Comultiplication of a contracted coefficient, using the original coassociativity. -/
theorem comul_dualContraction_coaction (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (v : V) :
    Coalgebra.comul (R := R) (dualContraction f (X.coaction v)) =
      _root_.TensorProduct.map (dualContraction f ∘ₗ X.coaction) LinearMap.id (X.coaction v) := by
  calc
    _ = (dualContraction f).rTensor C
        ((_root_.TensorProduct.assoc R V C C).symm
          ((Coalgebra.comul (R := R) (A := C)).lTensor V (X.coaction v))) :=
      (dualContraction_comul f (X.coaction v)).symm
    _ = (dualContraction f).rTensor C (X.coaction.rTensor C (X.coaction v)) := by
      rw [X.coassoc_symm_apply]
    _ = _ := by
      induction X.coaction v using _root_.TensorProduct.inductionOn with
      | tmul w c => simp
      | add z z' hz hz' => simp [hz, hz']

/-- Coassociativity of the canonical raw dual coaction. The antipode reverses the
comultiplication factors; no cocommutativity or inverse antipode is used. -/
theorem dualCoaction_coassoc (X : Coalgebra.RightComodule R C V) :
    (_root_.TensorProduct.assoc R (Module.Dual R V) C C).toLinearMap ∘ₗ
        (dualCoaction X).rTensor C ∘ₗ dualCoaction X =
      (Coalgebra.comul (R := R) (A := C)).lTensor (Module.Dual R V) ∘ₗ
        dualCoaction X := by
  ext f
  apply (dualTensorHomEquiv R V (C ⊗[R] C)).injective
  ext v
  change dualTensorHom R V (C ⊗[R] C)
      (_root_.TensorProduct.assoc R (Module.Dual R V) C C
        ((dualCoaction X).rTensor C (dualCoaction X f))) v =
    dualTensorHom R V (C ⊗[R] C)
      ((Coalgebra.comul (R := R) (A := C)).lTensor (Module.Dual R V)
        (dualCoaction X f)) v
  rw [dualTensorHom_assoc_dualCoaction_rTensor, dualTensorHom_dualCoaction]
  have hflip (z : V ⊗[R] C) :
      _root_.TensorProduct.comm R C C
          (_root_.TensorProduct.map
            (HopfAlgebra.antipode R (A := C) ∘ₗ dualContraction f ∘ₗ X.coaction)
            (HopfAlgebra.antipode R (A := C)) z) =
        _root_.TensorProduct.map (HopfAlgebra.antipode R (A := C))
          (HopfAlgebra.antipode R (A := C))
          (_root_.TensorProduct.comm R C C
            (_root_.TensorProduct.map (dualContraction f ∘ₗ X.coaction) LinearMap.id z)) := by
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w c => simp
    | add z z' hz hz' => simp [hz, hz']
  rw [hflip, ← comul_dualContraction_coaction, ← HopfAlgebra.comul_antipode]
  have h := LinearMap.congr_fun
    (dualTensorHom_comp_lTensor (R := R) (M := V)
      (Coalgebra.comul (R := R) (A := C))) (dualCoaction X f)
  have hv := LinearMap.congr_fun h v
  simpa using hv.symm

omit [Module.Finite R V] [Module.Projective R V] in
/-- The counit of a contracted coaction is the value of the functional. -/
theorem counit_dualContraction_coaction (X : Coalgebra.RightComodule R C V)
    (f : Module.Dual R V) (v : V) :
    Coalgebra.counit (R := R) (dualContraction f (X.coaction v)) = f v := by
  have h (z : V ⊗[R] C) :
      Coalgebra.counit (R := R) (dualContraction f z) =
        dualContraction (C := R) f ((Coalgebra.counit (R := R) (A := C)).lTensor V z) := by
    induction z using _root_.TensorProduct.inductionOn with
    | tmul w c => simp
    | add z z' hz hz' => simp [hz, hz']
  rw [h, X.counit_coaction]
  simp

/-- Counitality of the canonical raw dual coaction. -/
theorem dualCoaction_counit (X : Coalgebra.RightComodule R C V) :
    (Coalgebra.counit (R := R) (A := C)).lTensor (Module.Dual R V) ∘ₗ dualCoaction X =
      (_root_.TensorProduct.rid R (Module.Dual R V)).symm.toLinearMap := by
  ext f
  apply (dualTensorHomEquiv R V R).injective
  ext v
  change dualTensorHom R V R
      ((Coalgebra.counit (R := R) (A := C)).lTensor (Module.Dual R V)
        (dualCoaction X f)) v =
    dualTensorHom R V R ((_root_.TensorProduct.rid R (Module.Dual R V)).symm f) v
  have h := LinearMap.congr_fun
    (dualTensorHom_comp_lTensor (R := R) (M := V)
      (Coalgebra.counit (R := R) (A := C))) (dualCoaction X f)
  have hv := LinearMap.congr_fun h v
  calc
    _ = Coalgebra.counit (R := R) (dualTensorHom R V C (dualCoaction X f) v) := hv
    _ = f v := by
      rw [dualCoaction_characteristic, HopfAlgebra.counit_antipode,
        counit_dualContraction_coaction]
    _ = _ := by simp

/-- The dual right comodule, on the stock module dual of a specified comodule. -/
noncomputable def dual (X : Coalgebra.RightComodule R C V) :
    Coalgebra.RightComodule R C (Module.Dual R V) where
  coaction := dualCoaction X
  coassoc := dualCoaction_coassoc X
  counit_comp := dualCoaction_counit X

@[simp] theorem dual_coaction (X : Coalgebra.RightComodule R C V) :
    (dual X).coaction = dualCoaction X := rfl

/-- The bundled dual is uniquely characterized by its contraction identity. -/
theorem eq_dual_of_characteristic (X : Coalgebra.RightComodule R C V)
    (Y : Coalgebra.RightComodule R C (Module.Dual R V))
    (h : ∀ (f : Module.Dual R V) (v : V), dualTensorHom R V C (Y.coaction f) v =
      HopfAlgebra.antipode R (A := C) (dualContraction f (X.coaction v))) :
    Y = dual X := by
  apply Coalgebra.RightComodule.ext
  exact coaction_eq_dualCoaction X Y h

end Coalgebra.RightComodule


namespace Coalgebra.RightComoduleHom

variable {R : Type u} {C : Type v} {V : Type w} {W : Type x} {U : Type y}
variable [CommSemiring R] [Semiring C] [HopfAlgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable [AddCommMonoid U] [Module R U]
variable [Module.Finite R V] [Module.Projective R V]
variable [Module.Finite R W] [Module.Projective R W]
variable {X : Coalgebra.RightComodule R C V} {Y : Coalgebra.RightComodule R C W}
variable {Z : Coalgebra.RightComodule R C U}

/-- Pullback of functionals is colinear for the canonical dual coactions. -/
noncomputable def dualMap (h : Coalgebra.RightComoduleHom X Y) :
    Coalgebra.RightComoduleHom (RightComodule.dual Y) (RightComodule.dual X) where
  toLinearMap := h.toLinearMap.dualMap
  colinear := by
    ext f
    apply (dualTensorHomEquiv R V C).injective
    ext v
    change dualTensorHom R V C
        (RightComodule.dualCoaction X (h.toLinearMap.dualMap f)) v =
      dualTensorHom R V C
        (h.toLinearMap.dualMap.rTensor C (RightComodule.dualCoaction Y f)) v
    rw [RightComodule.dualCoaction_characteristic]
    have hnat := LinearMap.congr_fun
      (dualTensorHom_comp_rTensor_dualMap (R := R) (P := C) h.toLinearMap)
      (RightComodule.dualCoaction Y f)
    have hv := LinearMap.congr_fun hnat v
    calc
      _ = HopfAlgebra.antipode R (A := C)
          (RightComodule.dualContraction f
            (h.toLinearMap.rTensor C (X.coaction v))) := by
        simp only [RightComodule.dualContraction_dualMap, LinearMap.comp_apply]
      _ = HopfAlgebra.antipode R (A := C)
          (RightComodule.dualContraction f (Y.coaction (h v))) := by
        rw [← h.colinear_apply]
      _ = dualTensorHom R W C (RightComodule.dualCoaction Y f) (h v) :=
        (RightComodule.dualCoaction_characteristic Y f (h v)).symm
      _ = _ := hv.symm

/-- The underlying linear map is exactly the stock dual map. -/
@[simp] theorem dualMap_toLinearMap (h : Coalgebra.RightComoduleHom X Y) :
    (dualMap h).toLinearMap = h.toLinearMap.dualMap := rfl

/-- The dual morphism is pullback of functionals. -/
@[simp] theorem dualMap_apply (h : Coalgebra.RightComoduleHom X Y)
    (f : Module.Dual R W) (v : V) :
    dualMap h f v = f (h v) := rfl

/-- The canonical dual morphism preserves identities. -/
@[simp] theorem dualMap_id (X : Coalgebra.RightComodule R C V) :
    dualMap (Coalgebra.RightComoduleHom.id X) =
      Coalgebra.RightComoduleHom.id (RightComodule.dual X) := by
  ext f v
  rfl

variable [Module.Finite R U] [Module.Projective R U]

/-- The canonical dual morphism reverses composition. -/
@[simp] theorem dualMap_comp (g : Coalgebra.RightComoduleHom Y Z)
    (h : Coalgebra.RightComoduleHom X Y) :
    dualMap (g.comp h) = (dualMap h).comp (dualMap g) := by
  ext f v
  rfl

end Coalgebra.RightComoduleHom
