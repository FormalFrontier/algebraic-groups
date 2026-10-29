/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.PointGroup
public import AlgebraicGroups.Algebra.GeneralLinearBaseChange
public import AlgebraicGroups.Algebra.Coalgebra.Evaluation

/-!
# Reconstructing a right coaction from a natural point representation

A `PointRepresentation` is a natural transformation from the group functor of
points of a commutative Hopf algebra to the general linear functor of scalar
extensions of a module. The point groups are lifted to the general linear
groups' universe using `GrpCat.uliftFunctor`.

The lifted generic point determines a linear map `recoveredCoaction`. Component
naturality gives its characteristic evaluation formula. Counitality is obtained
using the endomorphism of the lifted coordinate algebra induced by the counit;
the base ring need not belong to the category of test algebras. Coassociativity
uses the two tensor-factor points over the tensor square of the lifted algebra.
These laws bundle the recovered map as a specified right comodule. Reconstruction
is injective, and its evaluation agrees with the original component operators.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c: representations and
  comodules, with right coactions and associated left point actions.
* Mathlib's convolution, universe-lift, tensor-product and scalar-extension
  formalizations; the general linear base-change functor and right-comodule
  evaluation API in this library.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

universe u a v t r s

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (A : Type a) [CommRing A] [HopfAlgebra K A]
  (V : Type v) [AddCommGroup V] [Module K V]

/-- A natural representation on the tensor-extension functor of `V`, tested on
algebras of size `max a t`. The point and module universes are independent. -/
abbrev PointRepresentation :=
  NatTrans
    ((pointGroupFunctor K A : CommAlgCat.{max a t, u} K ⥤ GrpCat.{max a t}) ⋙
      GrpCat.uliftFunctor.{v, max a t})
    (generalLinearModuleFunctor K V :
      CommAlgCat.{max a t, u} K ⥤ GrpCat.{max (max a t) v})

namespace PointRepresentation

variable {K A V}
variable (η : PointRepresentation.{u, a, v, t} K A V)

/-- The component automorphism at an algebra-valued point. The coefficient
algebra is an object of the representation's category of test algebras. -/
def operator (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    LinearMap.GeneralLinearGroup R (R ⊗[K] V) :=
  (η.app R).hom (ULift.up (toConv g))

/-- The counit point acts as the identity. -/
@[simp] theorem operator_one (R : CommAlgCat.{max a t, u} K) :
    η.operator R ((Algebra.ofId K R).comp (Bialgebra.counitAlgHom K A)) = 1 :=
  (η.app R).hom.map_one

/-- Component multiplication is multiplication in the composition group:
the second point acts first. -/
theorem operator_mul (R : CommAlgCat.{max a t, u} K) (g h : A →ₐ[K] R) :
    η.operator R
        (((toConv g : (pointGroupFunctor K A).obj R) * toConv h).ofConv) =
      η.operator R g * η.operator R h :=
  (η.app R).hom.map_mul (ULift.up (toConv g)) (ULift.up (toConv h))

/-- Naturality expressed using the existing general linear base-change map. -/
theorem operator_baseChange {R S : CommAlgCat.{max a t, u} K}
    (q : R →ₐ[K] S) (g : A →ₐ[K] R) :
    generalLinearModuleBaseChange K V R S q (η.operator R g) =
      η.operator S (q.comp g) := by
  have h := congrArg
    (fun f : ((pointGroupFunctor K A ⋙ GrpCat.uliftFunctor.{v, max a t}).obj R) ⟶
        (generalLinearModuleFunctor K V).obj S ↦
      f.hom (ULift.up (toConv g)))
    (η.naturality (CommAlgCat.ofHom q))
  exact h.symm

/-- Equality of all component automorphisms is equality of natural representations. -/
@[ext] theorem ext {η θ : PointRepresentation.{u, a, v, t} K A V}
    (h : ∀ (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R),
      η.operator R g = θ.operator R g) : η = θ := by
  apply NatTrans.ext
  funext R
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨g⟩
  exact h R g.ofConv

/-- The value of the lifted generic component on `1 ⊗ v`, as a `K`-linear map.
No comodule equation is required to construct this data. -/
def genericLinearMap : V →ₗ[K] ULift.{t} A ⊗[K] V :=
  (((η.operator (CommAlgCat.of K (ULift.{t} A))
    (ULift.algEquiv (R := K)).symm.toAlgHom).val).restrictScalars K).comp
      (TensorProduct.mk K (ULift.{t} A) V 1)

/-- Readback at the lifted generic point. -/
@[simp] theorem genericLinearMap_apply (x : V) :
    η.genericLinearMap x =
      (η.operator (CommAlgCat.of K (ULift.{t} A))
        (ULift.algEquiv (R := K)).symm.toAlgHom).val (1 ⊗ₜ[K] x) := rfl

/-- The right-coaction linear data recovered from the lifted generic point.
The coordinate algebra is transported down before commuting the factors. -/
def recoveredCoaction : V →ₗ[K] V ⊗[K] A :=
  (TensorProduct.comm K A V).toLinearMap.comp
    ((TensorProduct.map (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).toLinearMap
      (LinearMap.id : V →ₗ[K] V)).comp η.genericLinearMap)

/-- The coefficient-first form of the recovered linear map. -/
theorem comm_recoveredCoaction (x : V) :
    TensorProduct.comm K V A (η.recoveredCoaction x) =
      TensorProduct.map
        (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).toLinearMap
        (LinearMap.id : V →ₗ[K] V) (η.genericLinearMap x) := by
  change (TensorProduct.comm K A V).symm
    (TensorProduct.comm K A V _) = _
  exact (TensorProduct.comm K A V).symm_apply_apply _

/-- The generic-point linear data is recovered from the same right-coaction map. -/
theorem genericLinearMap_eq (x : V) :
    η.genericLinearMap x =
      TensorProduct.map
        (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).symm.toLinearMap
        (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) := by
  let e : ULift.{t} A ≃ₐ[K] A := ULift.algEquiv
  have h : (TensorProduct.map e.symm.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
      (TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V)) =
        LinearMap.id := by
    ext y z
    simp
  rw [comm_recoveredCoaction]
  exact (LinearMap.congr_fun h (η.genericLinearMap x)).symm

/-- Every in-category component is determined on one-tensors by the recovered
linear map, using naturality at `g ∘ e : ULift A → R`. -/
theorem operator_one_tmul (R : CommAlgCat.{max a t, u} K)
    (g : A →ₐ[K] R) (x : V) :
    (η.operator R g).val (1 ⊗ₜ[K] x) =
      TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) := by
  let e : ULift.{t} A ≃ₐ[K] A := ULift.algEquiv
  have hg : (g.comp e.toAlgHom).comp e.symm.toAlgHom = g := by
    ext y
    exact congrArg g (e.apply_symm_apply y)
  have h := congrArg (fun f ↦ f.val (1 ⊗ₜ[K] x))
    (η.operator_baseChange (R := CommAlgCat.of K (ULift.{t} A)) (S := R)
      (g.comp e.toAlgHom) e.symm.toAlgHom)
  rw [hg, generalLinearModuleBaseChange_tmul] at h
  change (1 : R) •
    (TensorProduct.map (g.toLinearMap.comp e.toLinearMap)
      (LinearMap.id : V →ₗ[K] V)) (η.genericLinearMap x) =
        (η.operator R g).val (1 ⊗ₜ[K] x) at h
  rw [one_smul] at h
  rw [comm_recoveredCoaction, TensorProduct.map_map, LinearMap.id_comp]
  exact h.symm

/-- The characteristic formula on all pure tensors follows from coefficient
linearity, without finite dimensionality of the module. -/
theorem operator_tmul (R : CommAlgCat.{max a t, u} K)
    (g : A →ₐ[K] R) (z : R) (x : V) :
    (η.operator R g).val (z ⊗ₜ[K] x) =
      z • TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) := by
  calc
    _ = (η.operator R g).val (z • (1 ⊗ₜ[K] x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = z • (η.operator R g).val (1 ⊗ₜ[K] x) := map_smul _ _ _
    _ = _ := by rw [operator_one_tmul]

/-- The counit-induced endomorphism of the lifted coordinate algebra. Both its
source and target belong to the category of test algebras. -/
def counitEnd : ULift.{t} A →ₐ[K] ULift.{t} A :=
  (Algebra.ofId K (ULift.{t} A)).comp
    ((Bialgebra.counitAlgHom K A).comp
      (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).toAlgHom)

/-- The internal counit endomorphism sends the generic point to the unit point. -/
@[simp] theorem counitEnd_comp_generic :
    (counitEnd.{u, a, t} (K := K) (A := A)).comp
        (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).symm.toAlgHom =
      (Algebra.ofId K (ULift.{t} A)).comp (Bialgebra.counitAlgHom K A) := by
  ext x
  rfl

/-- Naturality at the internal counit endomorphism and preservation of the group
unit give the generic one-tensor equation. No component at the base ring occurs. -/
theorem genericLinearMap_counitEnd (x : V) :
    TensorProduct.map (counitEnd.{u, a, t} (K := K) (A := A)).toLinearMap
        (LinearMap.id : V →ₗ[K] V) (η.genericLinearMap x) =
      1 ⊗ₜ[K] x := by
  have h := congrArg (fun f ↦ f.val (1 ⊗ₜ[K] x))
    (η.operator_baseChange (R := CommAlgCat.of K (ULift.{t} A))
      (S := CommAlgCat.of K (ULift.{t} A))
      (counitEnd.{u, a, t} (K := K) (A := A))
      (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).symm.toAlgHom)
  rw [counitEnd_comp_generic, operator_one, generalLinearModuleBaseChange_tmul] at h
  change (1 : ULift.{t} A) •
    (TensorProduct.map (counitEnd.{u, a, t} (K := K) (A := A)).toLinearMap
      (LinearMap.id : V →ₗ[K] V)) (η.genericLinearMap x) = 1 ⊗ₜ[K] x at h
  rwa [one_smul] at h

/-- Right counitality of the recovered linear map. The tensor map to `K ⊗ V`
is used only after the internal naturality argument. -/
theorem recoveredCoaction_counit :
    (Coalgebra.counit (R := K) (A := A)).lTensor V ∘ₗ η.recoveredCoaction =
      (TensorProduct.rid K V).symm.toLinearMap := by
  let e : ULift.{t} A ≃ₐ[K] A := ULift.algEquiv
  let ε : ULift.{t} A →ₐ[K] K := (Bialgebra.counitAlgHom K A).comp e.toAlgHom
  let τ : ULift.{t} A ⊗[K] V →ₗ[K] K ⊗[K] V :=
    TensorProduct.map ε.toLinearMap (LinearMap.id : V →ₗ[K] V)
  let Q : ULift.{t} A ⊗[K] V →ₗ[K] ULift.{t} A ⊗[K] V :=
    TensorProduct.map (counitEnd.{u, a, t} (K := K) (A := A)).toLinearMap
      (LinearMap.id : V →ₗ[K] V)
  have hτ : τ.comp Q = τ := by
    ext y x
    simp [τ, Q, ε, counitEnd, e]
  have hflip :
      (Coalgebra.counit (R := K) (A := A)).lTensor V ∘ₗ
          (TensorProduct.comm K A V).toLinearMap ∘ₗ
          TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V) =
        (TensorProduct.comm K K V).toLinearMap.comp τ := by
    ext y x
    rfl
  ext x
  have hx : τ (η.genericLinearMap x) = 1 ⊗ₜ[K] x := by
    calc
      _ = τ (Q (η.genericLinearMap x)) :=
        (LinearMap.congr_fun hτ (η.genericLinearMap x)).symm
      _ = τ (1 ⊗ₜ[K] x) := by rw [genericLinearMap_counitEnd]
      _ = _ := by simp [τ]
  change (Coalgebra.counit (R := K) (A := A)).lTensor V
    (TensorProduct.comm K A V
      (TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (η.genericLinearMap x))) = x ⊗ₜ[K] 1
  change ((Coalgebra.counit (R := K) (A := A)).lTensor V ∘ₗ
    (TensorProduct.comm K A V).toLinearMap ∘ₗ
      TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V))
        (η.genericLinearMap x) = _
  rw [hflip]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx,
    TensorProduct.comm_tmul]

/-- Coassociativity of the recovered linear map. The two tensor-factor points
and their convolution product are tested in `ULift A ⊗ ULift A`, in the same
category of coefficient algebras. No Hopf structure on `ULift A` is used. -/
theorem recoveredCoaction_coassoc :
    (TensorProduct.assoc K V A A).toLinearMap ∘ₗ
        η.recoveredCoaction.rTensor A ∘ₗ η.recoveredCoaction =
      (Coalgebra.comul (R := K) (A := A)).lTensor V ∘ₗ η.recoveredCoaction := by
  let L := ULift.{t} A
  let e : L ≃ₐ[K] A := ULift.algEquiv
  let β : A →ₐ[K] L := e.symm.toAlgHom
  let R : CommAlgCat.{max a t, u} K := CommAlgCat.of K (L ⊗[K] L)
  let i₁ : L →ₐ[K] R := Algebra.TensorProduct.includeLeft
  let i₂ : L →ₐ[K] R := Algebra.TensorProduct.includeRight
  let γ₁ : A →ₐ[K] R := i₁.comp β
  let γ₂ : A →ₐ[K] R := i₂.comp β
  let δ : L →ₐ[K] R := (Algebra.TensorProduct.map β β).comp
    ((Bialgebra.comulAlgHom K A).comp e.toAlgHom)
  have hpoints :
      (((toConv γ₁ : (pointGroupFunctor K A).obj R) * toConv γ₂).ofConv) =
        δ.comp β := by
    have hlift : Algebra.TensorProduct.lift γ₁ γ₂ (fun _ _ ↦ .all ..) =
        Algebra.TensorProduct.map β β := by
      apply Algebra.TensorProduct.ext'
      intro y z
      change (β y ⊗ₜ[K] (1 : L)) * ((1 : L) ⊗ₜ[K] β z) = β y ⊗ₜ[K] β z
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    ext y
    calc
      _ = Algebra.TensorProduct.lift γ₁ γ₂ (fun _ _ ↦ .all ..)
          (Coalgebra.comul y) := AlgHom.convMul_apply (toConv γ₁) (toConv γ₂) y
      _ = (Algebra.TensorProduct.map β β) (Coalgebra.comul y) := by rw [hlift]
      _ = _ := rfl
  let E : A ⊗[K] A ≃ₗ[K] L ⊗[K] L :=
    TensorProduct.congr e.symm.toLinearEquiv e.symm.toLinearEquiv
  let F : V ⊗[K] (A ⊗[K] A) ≃ₗ[K] R ⊗[K] V :=
    (TensorProduct.comm K V (A ⊗[K] A)).trans
      (TensorProduct.congr E (LinearEquiv.refl K V))
  have hshuffle (z : A) (q : V ⊗[K] A) :
      γ₂ z • TensorProduct.map γ₁.toLinearMap (LinearMap.id : V →ₗ[K] V)
          (TensorProduct.comm K V A q) =
        F (TensorProduct.assoc K V A A (q ⊗ₜ[K] z)) := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
      change γ₂ z • (γ₁ y ⊗ₜ[K] x) = E (y ⊗ₜ[K] z) ⊗ₜ[K] x
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      change (((1 : L) ⊗ₜ[K] β z) * (β y ⊗ₜ[K] (1 : L))) ⊗ₜ[K] x =
        (TensorProduct.congr e.symm.toLinearEquiv e.symm.toLinearEquiv)
          (y ⊗ₜ[K] z) ⊗ₜ[K] x
      rw [_root_.TensorProduct.congr_tmul]
      change (((1 : L) ⊗ₜ[K] β z) * (β y ⊗ₜ[K] (1 : L))) ⊗ₜ[K] x =
        (β y ⊗ₜ[K] β z) ⊗ₜ[K] x
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add q q' hq hq' =>
      simpa only [TensorProduct.add_tmul, map_add, smul_add] using
        congrArg₂ (· + ·) hq hq'
  have hleft :
      ((η.operator R γ₁).val.restrictScalars K).comp
          ((TensorProduct.map γ₂.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
            (TensorProduct.comm K V A).toLinearMap) =
        F.toLinearMap.comp
          ((TensorProduct.assoc K V A A).toLinearMap.comp
            (η.recoveredCoaction.rTensor A)) := by
    ext x z
    simpa only [TensorProduct.AlgebraTensorModule.curry_apply,
      _root_.TensorProduct.curry_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      LinearMap.rTensor_tmul, operator_tmul] using hshuffle z (η.recoveredCoaction x)
  have hright :
      (TensorProduct.map (δ.comp β).toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
          (TensorProduct.comm K V A).toLinearMap =
        F.toLinearMap.comp ((Coalgebra.comul (R := K) (A := A)).lTensor V) := by
    ext x z
    rfl
  ext x
  apply F.injective
  have hmul : (η.operator R (δ.comp β)).val (1 ⊗ₜ[K] x) =
      (η.operator R γ₁).val ((η.operator R γ₂).val (1 ⊗ₜ[K] x)) := by
    have h := congrArg (fun f ↦ f.val (1 ⊗ₜ[K] x)) (η.operator_mul R γ₁ γ₂)
    rw [hpoints] at h
    exact h
  change F (TensorProduct.assoc K V A A
      (η.recoveredCoaction.rTensor A (η.recoveredCoaction x))) =
    F ((Coalgebra.comul (R := K) (A := A)).lTensor V (η.recoveredCoaction x))
  calc
    _ = (η.operator R γ₁).val
        (TensorProduct.map γ₂.toLinearMap (LinearMap.id : V →ₗ[K] V)
          (TensorProduct.comm K V A (η.recoveredCoaction x))) :=
      (LinearMap.congr_fun hleft (η.recoveredCoaction x)).symm
    _ = (η.operator R (δ.comp β)).val (1 ⊗ₜ[K] x) := by
      rw [← η.operator_one_tmul R γ₂ x]
      exact hmul.symm
    _ = TensorProduct.map (δ.comp β).toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) :=
      η.operator_one_tmul R (δ.comp β) x
    _ = _ := LinearMap.congr_fun hright (η.recoveredCoaction x)

/-- The right comodule reconstructed from a natural point representation.
Its two laws are consequences of component naturality and multiplicativity. -/
def toRightComodule : Coalgebra.RightComodule K A V where
  coaction := η.recoveredCoaction
  coassoc := η.recoveredCoaction_coassoc
  counit_comp := η.recoveredCoaction_counit

/-- Reconstruction retains the recovered coaction as data. -/
@[simp] theorem toRightComodule_coaction :
    η.toRightComodule.coaction = η.recoveredCoaction := rfl

/-- The component endomorphism is evaluation of the same reconstructed coaction. -/
theorem operator_val (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (η.operator R g).val = η.toRightComodule.evaluate g.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  exact η.operator_tmul R g z x

/-- The canonical operator at an arbitrarily sized coefficient algebra is
defined by evaluation of the reconstructed coaction, not by an out-of-category
component of the natural transformation. -/
def evaluate {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) :
    Module.End R (R ⊗[K] V) :=
  η.toRightComodule.evaluate g.toLinearMap

/-- Characteristic pure-tensor formula for arbitrary coefficient algebras. -/
@[simp] theorem evaluate_tmul {R : Type r} [CommRing R] [Algebra K R]
    (g : A →ₐ[K] R) (z : R) (x : V) :
    η.evaluate g (z ⊗ₜ[K] x) =
      z • TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) := rfl

/-- Characteristic one-tensor formula for arbitrary coefficient algebras. -/
theorem evaluate_one_tmul {R : Type r} [CommRing R] [Algebra K R]
    (g : A →ₐ[K] R) (x : V) :
    η.evaluate g (1 ⊗ₜ[K] x) =
      TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (η.recoveredCoaction x)) :=
  η.toRightComodule.evaluate_one_tmul g.toLinearMap x

/-- In-category components agree with the canonical arbitrary-algebra operator. -/
theorem operator_val_eq_evaluate (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (η.operator R g).val = η.evaluate g := η.operator_val R g

/-- Evaluation commutes with every algebra map between independently sized
coefficient algebras. This is the existing right-comodule evaluation naturality. -/
theorem evaluate_naturality {R : Type r} [CommRing R] [Algebra K R]
    {S : Type s} [CommRing S] [Algebra K S] (q : R →ₐ[K] S) (g : A →ₐ[K] R) :
    (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
        ((η.evaluate g).restrictScalars K) =
      ((η.evaluate (q.comp g)).restrictScalars K).comp
        (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)) :=
  η.toRightComodule.evaluate_naturality g.toLinearMap q

/-- The recovered coaction determines the entire natural transformation. -/
theorem ext_of_recoveredCoaction {η θ : PointRepresentation.{u, a, v, t} K A V}
    (h : η.recoveredCoaction = θ.recoveredCoaction) : η = θ := by
  apply ext
  intro R g
  apply Units.ext
  rw [operator_val, operator_val]
  have hc : η.toRightComodule = θ.toRightComodule :=
    Coalgebra.RightComodule.ext h
  rw [hc]

/-- Reconstruction is injective as a map to specified right-comodule values. -/
theorem toRightComodule_injective :
    Function.Injective (toRightComodule : PointRepresentation.{u, a, v, t} K A V →
      Coalgebra.RightComodule K A V) := by
  intro η θ h
  apply ext_of_recoveredCoaction
  exact congrArg Coalgebra.RightComodule.coaction h

/-- Equality of the reconstructed comodule values detects equality of the
original natural transformations. -/
@[simp] theorem toRightComodule_inj {η θ : PointRepresentation.{u, a, v, t} K A V} :
    η.toRightComodule = θ.toRightComodule ↔ η = θ :=
  toRightComodule_injective.eq_iff

end PointRepresentation

end AlgebraicGeometry
