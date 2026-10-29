/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RepresentationReconstruction
public import AlgebraicGroups.Algebra.Coalgebra.Evaluation.Action
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Intertwiners of natural point representations

A linear map intertwines two natural point representations if its scalar
extensions intertwine their operators at every point in the common category
of test algebras. This condition is equivalent to colinearity for the same
reconstructed right coactions. The reverse implication is detected by the
generic point over `ULift C`; it does not use a component at the base ring.

`PointRepresentation.PointHom` is the subtype of the existing linear-map
module cut out by these equations. The linear equivalence `pointHomEquiv`
identifies it with the existing right-comodule morphisms, preserving underlying
maps, identities and composition. At an independently sized coefficient algebra,
scalar extension gives Mathlib's `Representation.IntertwiningMap` between the
canonical evaluated actions of the same recovered coactions. Such an operator
is not an out-of-category component of the original natural transformation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c: representations
  and comodules, with right coactions and associated left point actions.
* Stepan Nesterov and Edison Xie, Mathlib, `RepresentationTheory/Intertwining`,
  for bundled intertwining maps; Mathlib's linear-map and scalar-extension APIs.
* The right-comodule evaluation and reconstruction APIs in this library.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u a v w z t r q

namespace AlgebraicGeometry.PointRepresentation

variable {K : Type u} {C : Type a} [CommRing K] [CommRing C] [HopfAlgebra K C]
variable {V : Type v} {W : Type w} {U : Type z}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup U] [Module K U]
variable (η : PointRepresentation.{u, a, v, t} K C V)
variable (θ : PointRepresentation.{u, a, w, t} K C W)
variable (ξ : PointRepresentation.{u, a, z, t} K C U)

/-- A linear map intertwines all genuine components in the common category
of test algebras. The scalar extension is the stock `LinearMap.baseChange`. -/
def IsPointIntertwining (f : V →ₗ[K] W) : Prop :=
  ∀ (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R),
    f.baseChange R ∘ₗ (η.operator R g).val =
      (θ.operator R g).val ∘ₗ f.baseChange R

/-- The point-intertwining equations evaluated on an arbitrary tensor. -/
theorem IsPointIntertwining.operator_apply {f : V →ₗ[K] W}
    (hf : IsPointIntertwining η θ f) (R : CommAlgCat.{max a t, u} K)
    (g : C →ₐ[K] R) (q : R ⊗[K] V) :
    f.baseChange R ((η.operator R g).val q) =
      (θ.operator R g).val (f.baseChange R q) :=
  LinearMap.congr_fun (hf R g) q

private theorem colinear_of_generic_intertwining (f : V →ₗ[K] W)
    (hf : f.baseChange (ULift.{t} C) ∘ₗ
        (η.operator (CommAlgCat.of K (ULift.{t} C))
          (ULift.algEquiv (R := K) : ULift.{t} C ≃ₐ[K] C).symm.toAlgHom).val =
      (θ.operator (CommAlgCat.of K (ULift.{t} C))
          (ULift.algEquiv (R := K) : ULift.{t} C ≃ₐ[K] C).symm.toAlgHom).val ∘ₗ
        f.baseChange (ULift.{t} C)) :
    θ.toRightComodule.coaction ∘ₗ f = f.rTensor C ∘ₗ η.toRightComodule.coaction := by
  let L := ULift.{t} C
  let e : L ≃ₐ[K] C := ULift.algEquiv
  let β : C →ₐ[K] L := e.symm.toAlgHom
  let R : CommAlgCat.{max a t, u} K := CommAlgCat.of K L
  change f.baseChange L ∘ₗ (η.operator R β).val =
    (θ.operator R β).val ∘ₗ f.baseChange L at hf
  have he : e.toLinearMap.comp β.toLinearMap = LinearMap.id := by
    ext c
    exact e.apply_symm_apply c
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hf (1 ⊗ₜ[K] x)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at hx
  rw [η.operator_one_tmul, θ.operator_one_tmul] at hx
  change TensorProduct.map (LinearMap.id : L →ₗ[K] L) f
      (TensorProduct.map β.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V C (η.recoveredCoaction x))) =
    TensorProduct.map β.toLinearMap (LinearMap.id : W →ₗ[K] W)
      (TensorProduct.comm K W C (θ.recoveredCoaction (f x))) at hx
  have hdown := congrArg
    (TensorProduct.map e.toLinearMap (LinearMap.id : W →ₗ[K] W)) hx
  simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id,
    he, TensorProduct.map_id, LinearMap.id_apply] at hdown
  change θ.recoveredCoaction (f x) = f.rTensor C (η.recoveredCoaction x)
  apply (TensorProduct.comm K W C).injective
  calc
    _ = TensorProduct.map (LinearMap.id : C →ₗ[K] C) f
        (TensorProduct.comm K V C (η.recoveredCoaction x)) := hdown.symm
    _ = _ := TensorProduct.map_comm (LinearMap.id : C →ₗ[K] C) f _

/-- Point intertwining is exactly colinearity for the same recovered coactions.
The generic test algebra has universe `max a t`, independently of the universes
of the base ring and of both modules. This is the morphism part of the
representation-comodule correspondence in Milne, *Algebraic Groups*, Ch. 4, §c. -/
theorem isPointIntertwining_iff_colinear (f : V →ₗ[K] W) :
    IsPointIntertwining η θ f ↔
      θ.toRightComodule.coaction ∘ₗ f = f.rTensor C ∘ₗ η.toRightComodule.coaction := by
  constructor
  · intro hf
    exact colinear_of_generic_intertwining η θ f
      (hf (CommAlgCat.of K (ULift.{t} C))
        (ULift.algEquiv (R := K) : ULift.{t} C ≃ₐ[K] C).symm.toAlgHom)
  · intro hf
    let l : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule :=
      { toLinearMap := f, colinear := hf }
    intro R g
    rw [η.operator_val, θ.operator_val]
    apply LinearMap.ext
    intro q
    exact l.baseChange_evaluate_apply g.toLinearMap q

/-- A single genuine generic component detects all point-intertwining equations. -/
theorem isPointIntertwining_iff_generic (f : V →ₗ[K] W) :
    IsPointIntertwining η θ f ↔
      f.baseChange (ULift.{t} C) ∘ₗ
          (η.operator (CommAlgCat.of K (ULift.{t} C))
            (ULift.algEquiv (R := K) : ULift.{t} C ≃ₐ[K] C).symm.toAlgHom).val =
        (θ.operator (CommAlgCat.of K (ULift.{t} C))
            (ULift.algEquiv (R := K) : ULift.{t} C ≃ₐ[K] C).symm.toAlgHom).val ∘ₗ
          f.baseChange (ULift.{t} C) := by
  constructor
  · intro hf
    exact hf _ _
  · intro hf
    exact (isPointIntertwining_iff_colinear η θ f).2
      (colinear_of_generic_intertwining η θ f hf)

/-- An in-category intertwiner intertwines canonical evaluation at each
independently sized coefficient algebra. Only the same recovered coactions
are evaluated; no component outside the original category is used. -/
theorem IsPointIntertwining.baseChange_comp_evaluate {f : V →ₗ[K] W}
    (hf : IsPointIntertwining η θ f) {R : Type r} [CommRing R] [Algebra K R]
    (g : C →ₐ[K] R) :
    f.baseChange R ∘ₗ η.evaluate g = θ.evaluate g ∘ₗ f.baseChange R := by
  let l : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule :=
    { toLinearMap := f, colinear := (isPointIntertwining_iff_colinear η θ f).1 hf }
  exact l.baseChange_comp_evaluate g.toLinearMap

/-- The arbitrary-algebra intertwining equation on an arbitrary tensor. -/
theorem IsPointIntertwining.baseChange_evaluate_apply {f : V →ₗ[K] W}
    (hf : IsPointIntertwining η θ f) {R : Type r} [CommRing R] [Algebra K R]
    (g : C →ₐ[K] R) (q : R ⊗[K] V) :
    f.baseChange R (η.evaluate g q) = θ.evaluate g (f.baseChange R q) :=
  LinearMap.congr_fun (IsPointIntertwining.baseChange_comp_evaluate η θ hf g) q

/-- The submodule of linear maps intertwining every point in the common
category of test algebras. -/
def pointIntertwiners : Submodule K (V →ₗ[K] W) where
  carrier := {f | IsPointIntertwining η θ f}
  zero_mem' := by
    intro R g
    simp
  add_mem' := by
    intro f h hf hh R g
    simp only [LinearMap.baseChange_add, LinearMap.add_comp, LinearMap.comp_add,
      hf R g, hh R g]
  smul_mem' := by
    intro k f hf R g
    simp only [LinearMap.baseChange_smul, LinearMap.smul_comp, LinearMap.comp_smul, hf R g]

/-- Membership is the original in-category point-intertwining condition. -/
@[simp] theorem mem_pointIntertwiners (f : V →ₗ[K] W) :
    f ∈ pointIntertwiners η θ ↔ IsPointIntertwining η θ f := Iff.rfl

/-- A point intertwiner is a member of the submodule of existing linear maps. -/
abbrev PointHom := ↥(pointIntertwiners η θ)

namespace PointHom

variable {η θ ξ}

/-- Forget the intertwining equations, retaining the given linear map. -/
def toLinearMap (f : PointHom η θ) : V →ₗ[K] W := f.val

@[simp] theorem toLinearMap_mk (f : V →ₗ[K] W) (hf : IsPointIntertwining η θ f) :
    PointHom.toLinearMap (⟨f, hf⟩ : PointHom η θ) = f := rfl

@[simp] theorem toLinearMap_zero : (0 : PointHom η θ).toLinearMap = 0 := rfl

@[simp] theorem toLinearMap_add (f h : PointHom η θ) :
    (f + h).toLinearMap = f.toLinearMap + h.toLinearMap := rfl

@[simp] theorem toLinearMap_smul (k : K) (f : PointHom η θ) :
    (k • f).toLinearMap = k • f.toLinearMap := rfl

/-- The underlying linear-map projection is injective. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : PointHom η θ → (V →ₗ[K] W)) :=
  fun _ _ h ↦ Subtype.ext h

/-- Point intertwiners are determined by their underlying maps' values. -/
@[ext] theorem ext {f h : PointHom η θ}
    (heq : ∀ x, f.toLinearMap x = h.toLinearMap x) : f = h :=
  toLinearMap_injective (LinearMap.ext heq)

/-- The original component square for a point intertwiner. -/
theorem operator_apply (f : PointHom η θ) (R : CommAlgCat.{max a t, u} K)
    (g : C →ₐ[K] R) (q : R ⊗[K] V) :
    f.toLinearMap.baseChange R ((η.operator R g).val q) =
      (θ.operator R g).val (f.toLinearMap.baseChange R q) :=
  IsPointIntertwining.operator_apply η θ f.property R g q

/-- Regard a point intertwiner as a colinear map of the same recovered comodules. -/
def toRightComoduleHom (f : PointHom η θ) :
    Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule where
  toLinearMap := f.toLinearMap
  colinear := (isPointIntertwining_iff_colinear η θ f.toLinearMap).1 f.property

@[simp] theorem toRightComoduleHom_toLinearMap (f : PointHom η θ) :
    f.toRightComoduleHom.toLinearMap = f.toLinearMap := rfl

@[simp] theorem toRightComoduleHom_apply (f : PointHom η θ) (x : V) :
    f.toRightComoduleHom x = f.toLinearMap x := rfl

/-- The recovered colinearity equation is for the original underlying map. -/
theorem colinear (f : PointHom η θ) :
    θ.toRightComodule.coaction ∘ₗ f.toLinearMap =
      f.toLinearMap.rTensor C ∘ₗ η.toRightComodule.coaction :=
  f.toRightComoduleHom.colinear

/-- A colinear map gives a point intertwiner without changing its linear data. -/
def ofRightComoduleHom
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    PointHom η θ :=
  ⟨f.toLinearMap, (isPointIntertwining_iff_colinear η θ f.toLinearMap).2 f.colinear⟩

@[simp] theorem ofRightComoduleHom_toLinearMap
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    (ofRightComoduleHom f).toLinearMap = f.toLinearMap := rfl

@[simp] theorem ofRightComoduleHom_toRightComoduleHom
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    (ofRightComoduleHom f).toRightComoduleHom = f := by
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

@[simp] theorem toRightComoduleHom_ofRightComoduleHom (f : PointHom η θ) :
    ofRightComoduleHom f.toRightComoduleHom = f := by
  apply toLinearMap_injective
  rfl

/-- The identity point intertwiner has the identity linear map. -/
def id (η : PointRepresentation.{u, a, v, t} K C V) : PointHom η η :=
  ofRightComoduleHom (Coalgebra.RightComoduleHom.id η.toRightComodule)

@[simp] theorem id_toLinearMap : (id η).toLinearMap = LinearMap.id := rfl

/-- Composition uses composition of the given underlying linear maps. -/
def comp (h : PointHom θ ξ) (f : PointHom η θ) : PointHom η ξ :=
  ofRightComoduleHom (h.toRightComoduleHom.comp f.toRightComoduleHom)

@[simp] theorem comp_toLinearMap (h : PointHom θ ξ) (f : PointHom η θ) :
    (h.comp f).toLinearMap = h.toLinearMap.comp f.toLinearMap := rfl

@[simp] theorem id_comp (f : PointHom η θ) : (id θ).comp f = f := by
  ext x
  rfl

@[simp] theorem comp_id (f : PointHom η θ) : f.comp (id η) = f := by
  ext x
  rfl

/-- Composition of point intertwiners is associative. -/
theorem comp_assoc {Q : Type q} [AddCommGroup Q] [Module K Q]
    {ζ : PointRepresentation.{u, a, q, t} K C Q}
    (k : PointHom ξ ζ) (h : PointHom θ ξ) (f : PointHom η θ) :
    (k.comp h).comp f = k.comp (h.comp f) := by
  ext x
  rfl

@[simp] theorem toRightComoduleHom_id :
    (id η).toRightComoduleHom = Coalgebra.RightComoduleHom.id η.toRightComodule := by
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

@[simp] theorem toRightComoduleHom_comp (h : PointHom θ ξ) (f : PointHom η θ) :
    (h.comp f).toRightComoduleHom = h.toRightComoduleHom.comp f.toRightComoduleHom := by
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

@[simp] theorem ofRightComoduleHom_id :
    ofRightComoduleHom (Coalgebra.RightComoduleHom.id η.toRightComodule) = id η := rfl

@[simp] theorem ofRightComoduleHom_comp
    (h : Coalgebra.RightComoduleHom θ.toRightComodule ξ.toRightComodule)
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    ofRightComoduleHom (h.comp f) = (ofRightComoduleHom h).comp (ofRightComoduleHom f) := by
  apply toLinearMap_injective
  rfl

/-- Every scalar extension intertwines canonical evaluation of the same coactions. -/
theorem baseChange_comp_evaluate (f : PointHom η θ)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R) :
    f.toLinearMap.baseChange R ∘ₗ η.evaluate g =
      θ.evaluate g ∘ₗ f.toLinearMap.baseChange R :=
  f.toRightComoduleHom.baseChange_comp_evaluate g.toLinearMap

/-- The arbitrary-algebra intertwining equation evaluated on a tensor. -/
theorem baseChange_evaluate_apply (f : PointHom η θ)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R) (q : R ⊗[K] V) :
    f.toLinearMap.baseChange R (η.evaluate g q) =
      θ.evaluate g (f.toLinearMap.baseChange R q) :=
  f.toRightComoduleHom.baseChange_evaluate_apply g.toLinearMap q

/-- Scalar extension as Mathlib's intertwining map between the existing
canonical evaluated representations, at any independently sized algebra. -/
def baseChangeIntertwiningMap (f : PointHom η θ)
    (R : Type r) [CommRing R] [Algebra K R] :
    Representation.IntertwiningMap
      (η.toRightComodule.evaluateAlgHomMonoidHom (A := R))
      (θ.toRightComodule.evaluateAlgHomMonoidHom (A := R)) where
  toLinearMap := f.toLinearMap.baseChange R
  isIntertwining' g := f.baseChange_comp_evaluate g.ofConv

@[simp] theorem baseChangeIntertwiningMap_toLinearMap (f : PointHom η θ)
    (R : Type r) [CommRing R] [Algebra K R] :
    (f.baseChangeIntertwiningMap R).toLinearMap = f.toLinearMap.baseChange R := rfl

@[simp] theorem baseChangeIntertwiningMap_apply (f : PointHom η θ)
    (R : Type r) [CommRing R] [Algebra K R] (q : R ⊗[K] V) :
    f.baseChangeIntertwiningMap R q = f.toLinearMap.baseChange R q := rfl

/-- The scalar-extension bridge preserves the stock identity intertwiner. -/
@[simp] theorem baseChangeIntertwiningMap_id
    (R : Type r) [CommRing R] [Algebra K R] :
    (id η).baseChangeIntertwiningMap R =
      Representation.IntertwiningMap.id
        (η.toRightComodule.evaluateAlgHomMonoidHom (A := R)) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.baseChange_id

/-- The scalar-extension bridge preserves stock intertwiner composition. -/
@[simp] theorem baseChangeIntertwiningMap_comp (h : PointHom θ ξ) (f : PointHom η θ)
    (R : Type r) [CommRing R] [Algebra K R] :
    (h.comp f).baseChangeIntertwiningMap R =
      (h.baseChangeIntertwiningMap R).comp (f.baseChangeIntertwiningMap R) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.baseChange_comp f.toLinearMap h.toLinearMap

end PointHom

/-- The linear equivalence between point intertwiners and morphisms of the same
reconstructed comodules. Both directions retain the underlying linear map. -/
def pointHomEquiv : PointHom η θ ≃ₗ[K]
    Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule where
  toFun := PointHom.toRightComoduleHom
  invFun := PointHom.ofRightComoduleHom
  left_inv := PointHom.toRightComoduleHom_ofRightComoduleHom
  right_inv := PointHom.ofRightComoduleHom_toRightComoduleHom
  map_add' _ _ := by
    apply Coalgebra.RightComoduleHom.toLinearMap_injective
    rfl
  map_smul' _ _ := by
    apply Coalgebra.RightComoduleHom.toLinearMap_injective
    rfl

@[simp] theorem pointHomEquiv_apply_toLinearMap (f : PointHom η θ) :
    (pointHomEquiv η θ f).toLinearMap = f.toLinearMap := rfl

@[simp] theorem pointHomEquiv_symm_apply_toLinearMap
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    ((pointHomEquiv η θ).symm f).toLinearMap = f.toLinearMap := rfl

/-- The correspondence takes the identity to the identity comodule morphism. -/
@[simp] theorem pointHomEquiv_id :
    pointHomEquiv η η (PointHom.id η) =
      Coalgebra.RightComoduleHom.id η.toRightComodule :=
  PointHom.toRightComoduleHom_id

/-- The correspondence takes composition to comodule-morphism composition. -/
@[simp] theorem pointHomEquiv_comp (h : PointHom θ ξ) (f : PointHom η θ) :
    pointHomEquiv η ξ (h.comp f) =
      (pointHomEquiv θ ξ h).comp (pointHomEquiv η θ f) :=
  PointHom.toRightComoduleHom_comp h f

/-- The inverse correspondence also preserves identity data. -/
@[simp] theorem pointHomEquiv_symm_id :
    (pointHomEquiv η η).symm (Coalgebra.RightComoduleHom.id η.toRightComodule) =
      PointHom.id η := rfl

/-- The inverse correspondence also preserves composition data. -/
@[simp] theorem pointHomEquiv_symm_comp
    (h : Coalgebra.RightComoduleHom θ.toRightComodule ξ.toRightComodule)
    (f : Coalgebra.RightComoduleHom η.toRightComodule θ.toRightComodule) :
    (pointHomEquiv η ξ).symm (h.comp f) =
      ((pointHomEquiv θ ξ).symm h).comp ((pointHomEquiv η θ).symm f) :=
  PointHom.ofRightComoduleHom_comp h f

end AlgebraicGeometry.PointRepresentation
