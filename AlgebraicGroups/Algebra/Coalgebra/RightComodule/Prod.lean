/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Products of specified right comodules

Two specified right comodules over the same coalgebra have a right comodule
structure on their product module. Its coaction is characterized by the two
tensorized coordinate projections. The coordinate projections and the pairing
of colinear maps give the binary-product universal property in the existing
`Coalgebra.RightComoduleHom` structure.

The construction uses `TensorProduct.prodLeft` and needs neither flatness nor
finiteness assumptions. All module structures are the canonical product ones.

## References

* Mathlib's `TensorProduct/Prod`, by Eric Wieser, supplies distribution of tensor
  products over binary products.
* Mathlib's coalgebra developments, including `Coalgebra/MonoidAlgebra` by
  Amelia Livingston, and the algebraic-groups right-comodule formalization.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for classical comodules.

-/

@[expose] public section

universe u v w z q t a b

open scoped TensorProduct

namespace Coalgebra

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace RightComodule

section TensorProjections

variable {T : Type t} [AddCommMonoid T] [Module R T]

private theorem prodLeft_apply (x : (M × N) ⊗[R] T) :
    TensorProduct.prodLeft R R M N T x =
      ((LinearMap.fst R M N).rTensor T x, (LinearMap.snd R M N).rTensor T x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p t => rcases p with ⟨m, n⟩; rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

private theorem tensor_ext {x y : (M × N) ⊗[R] T}
    (hfst : (LinearMap.fst R M N).rTensor T x = (LinearMap.fst R M N).rTensor T y)
    (hsnd : (LinearMap.snd R M N).rTensor T x = (LinearMap.snd R M N).rTensor T y) :
    x = y := by
  apply (TensorProduct.prodLeft R R M N T).injective
  simp only [prodLeft_apply, hfst, hsnd]

private theorem fst_prodLeft_symm (p : (M ⊗[R] T) × (N ⊗[R] T)) :
    (LinearMap.fst R M N).rTensor T ((TensorProduct.prodLeft R R M N T).symm p) =
      p.1 := by
  have h := congrArg Prod.fst ((TensorProduct.prodLeft R R M N T).apply_symm_apply p)
  rw [prodLeft_apply] at h
  exact h

private theorem snd_prodLeft_symm (p : (M ⊗[R] T) × (N ⊗[R] T)) :
    (LinearMap.snd R M N).rTensor T ((TensorProduct.prodLeft R R M N T).symm p) =
      p.2 := by
  have h := congrArg Prod.snd ((TensorProduct.prodLeft R R M N T).apply_symm_apply p)
  rw [prodLeft_apply] at h
  exact h

end TensorProjections

section Naturality

variable {A : Type a} {B : Type b}
variable [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]

private theorem rid_symm_naturality (f : A →ₗ[R] B) :
    f.rTensor R ∘ₗ (TensorProduct.rid R A).symm.toLinearMap =
      (TensorProduct.rid R B).symm.toLinearMap ∘ₗ f := by
  ext a
  simp

private theorem coassoc_coordinate (ρ : A →ₗ[R] A ⊗[R] C)
    (f : A →ₗ[R] B) (Z : RightComodule R C B)
    (h : f.rTensor C ∘ₗ ρ = Z.coaction ∘ₗ f) (a : A) :
    f.rTensor (C ⊗[R] C)
        (TensorProduct.assoc R A C C (ρ.rTensor C (ρ a))) =
      f.rTensor (C ⊗[R] C) ((comul (R := R) (A := C)).lTensor A (ρ a)) := by
  have ht := congrArg (fun k : A →ₗ[R] B ⊗[R] C => k.rTensor C) h
  simp only [LinearMap.rTensor_comp] at ht
  calc
    _ = TensorProduct.assoc R B C C
        ((f.rTensor C).rTensor C (ρ.rTensor C (ρ a))) :=
      by
        simpa only [LinearMap.rTensor, TensorProduct.map_id] using
          TensorProduct.map_map_assoc f (LinearMap.id : C →ₗ[R] C)
            (LinearMap.id : C →ₗ[R] C) (ρ.rTensor C (ρ a))
    _ = TensorProduct.assoc R B C C
        (Z.coaction.rTensor C (Z.coaction (f a))) := by
      rw [show (f.rTensor C).rTensor C (ρ.rTensor C (ρ a)) =
          Z.coaction.rTensor C (f.rTensor C (ρ a)) from LinearMap.congr_fun ht (ρ a)]
      rw [show f.rTensor C (ρ a) = Z.coaction (f a) from LinearMap.congr_fun h a]
    _ = (comul (R := R) (A := C)).lTensor B (Z.coaction (f a)) :=
      LinearMap.congr_fun Z.coassoc (f a)
    _ = (comul (R := R) (A := C)).lTensor B (f.rTensor C (ρ a)) := by
      rw [show f.rTensor C (ρ a) = Z.coaction (f a) from LinearMap.congr_fun h a]
    _ = _ := by
      change ((comul (R := R) (A := C)).lTensor B ∘ₗ f.rTensor C) (ρ a) =
        (f.rTensor (C ⊗[R] C) ∘ₗ (comul (R := R) (A := C)).lTensor A) (ρ a)
      rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

private theorem counit_coordinate (ρ : A →ₗ[R] A ⊗[R] C)
    (f : A →ₗ[R] B) (Z : RightComodule R C B)
    (h : f.rTensor C ∘ₗ ρ = Z.coaction ∘ₗ f) (a : A) :
    f.rTensor R ((counit (R := R) (A := C)).lTensor A (ρ a)) =
      f.rTensor R ((TensorProduct.rid R A).symm a) := by
  calc
    _ = (counit (R := R) (A := C)).lTensor B (f.rTensor C (ρ a)) :=
      by
        change (f.rTensor R ∘ₗ (counit (R := R) (A := C)).lTensor A) (ρ a) =
          ((counit (R := R) (A := C)).lTensor B ∘ₗ f.rTensor C) (ρ a)
        rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    _ = (counit (R := R) (A := C)).lTensor B (Z.coaction (f a)) := by
      rw [show f.rTensor C (ρ a) = Z.coaction (f a) from LinearMap.congr_fun h a]
    _ = (TensorProduct.rid R B).symm (f a) :=
      LinearMap.congr_fun Z.counit_comp (f a)
    _ = _ := (LinearMap.congr_fun (rid_symm_naturality f) a).symm

end Naturality

private theorem prodCoaction_fst (X : RightComodule R C M) (Y : RightComodule R C N) :
    (LinearMap.fst R M N).rTensor C ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction) =
      X.coaction ∘ₗ LinearMap.fst R M N := by
  apply LinearMap.ext
  intro p
  exact fst_prodLeft_symm (X.coaction p.1, Y.coaction p.2)

private theorem prodCoaction_snd (X : RightComodule R C M) (Y : RightComodule R C N) :
    (LinearMap.snd R M N).rTensor C ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction) =
      Y.coaction ∘ₗ LinearMap.snd R M N := by
  apply LinearMap.ext
  intro p
  exact snd_prodLeft_symm (X.coaction p.1, Y.coaction p.2)

private theorem prodCoaction_coassoc
    (X : RightComodule R C M) (Y : RightComodule R C N) :
    TensorProduct.assoc R (M × N) C C ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction).rTensor C ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction) =
      (comul (R := R) (A := C)).lTensor (M × N) ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction) := by
  apply LinearMap.ext
  intro p
  apply tensor_ext
  · exact coassoc_coordinate _ (LinearMap.fst R M N) X (prodCoaction_fst X Y) p
  · exact coassoc_coordinate _ (LinearMap.snd R M N) Y (prodCoaction_snd X Y) p

private theorem prodCoaction_counit
    (X : RightComodule R C M) (Y : RightComodule R C N) :
    (counit (R := R) (A := C)).lTensor (M × N) ∘ₗ
        ((TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
          X.coaction.prodMap Y.coaction) =
      (TensorProduct.rid R (M × N)).symm.toLinearMap := by
  apply LinearMap.ext
  intro p
  apply tensor_ext
  · exact counit_coordinate _ (LinearMap.fst R M N) X (prodCoaction_fst X Y) p
  · exact counit_coordinate _ (LinearMap.snd R M N) Y (prodCoaction_snd X Y) p

/-- The product right comodule over the same coalgebra, on the product module. -/
def prod (X : RightComodule R C M) (Y : RightComodule R C N) :
    RightComodule R C (M × N) where
  coaction := (TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
    X.coaction.prodMap Y.coaction
  coassoc := by exact prodCoaction_coassoc X Y
  counit_comp := by exact prodCoaction_counit X Y

/-- The product coaction is the inverse tensor distribution applied to the
coordinate coactions. -/
theorem coaction_prod (X : RightComodule R C M) (Y : RightComodule R C N) :
    (prod X Y).coaction =
      (TensorProduct.prodLeft R R M N C).symm.toLinearMap ∘ₗ
        X.coaction.prodMap Y.coaction := (rfl)

/-- The product coaction evaluated at a pair. -/
@[simp] theorem coaction_prod_apply
    (X : RightComodule R C M) (Y : RightComodule R C N) (p : M × N) :
    (prod X Y).coaction p =
      (TensorProduct.prodLeft R R M N C).symm (X.coaction p.1, Y.coaction p.2) := (rfl)

/-- Tensor distribution identifies the product coaction with its two coordinates. -/
theorem prodLeft_coaction_prod
    (X : RightComodule R C M) (Y : RightComodule R C N) (p : M × N) :
    TensorProduct.prodLeft R R M N C ((prod X Y).coaction p) =
      (X.coaction p.1, Y.coaction p.2) := by
  rw [coaction_prod_apply, LinearEquiv.apply_symm_apply]

/-- The tensorized first projection intertwines the product coaction. -/
@[simp] theorem rTensor_fst_coaction_prod
    (X : RightComodule R C M) (Y : RightComodule R C N) :
    (LinearMap.fst R M N).rTensor C ∘ₗ (prod X Y).coaction =
      X.coaction ∘ₗ LinearMap.fst R M N := by
  rw [coaction_prod]
  exact prodCoaction_fst X Y

/-- The tensorized second projection intertwines the product coaction. -/
@[simp] theorem rTensor_snd_coaction_prod
    (X : RightComodule R C M) (Y : RightComodule R C N) :
    (LinearMap.snd R M N).rTensor C ∘ₗ (prod X Y).coaction =
      Y.coaction ∘ₗ LinearMap.snd R M N := by
  rw [coaction_prod]
  exact prodCoaction_snd X Y

end RightComodule

namespace RightComoduleHom

/-- The first colinear projection from the product right comodule. -/
@[no_expose] def fst (X : RightComodule R C M) (Y : RightComodule R C N) :
    RightComoduleHom (RightComodule.prod X Y) X where
  toLinearMap := LinearMap.fst R M N
  colinear := (RightComodule.rTensor_fst_coaction_prod X Y).symm

/-- The second colinear projection from the product right comodule. -/
@[no_expose] def snd (X : RightComodule R C M) (Y : RightComodule R C N) :
    RightComoduleHom (RightComodule.prod X Y) Y where
  toLinearMap := LinearMap.snd R M N
  colinear := (RightComodule.rTensor_snd_coaction_prod X Y).symm

/-- The first colinear projection has the usual first linear projection. -/
@[simp] theorem fst_toLinearMap (X : RightComodule R C M) (Y : RightComodule R C N) :
    (fst X Y).toLinearMap = LinearMap.fst R M N := (rfl)

/-- The second colinear projection has the usual second linear projection. -/
@[simp] theorem snd_toLinearMap (X : RightComodule R C M) (Y : RightComodule R C N) :
    (snd X Y).toLinearMap = LinearMap.snd R M N := (rfl)

/-- The first colinear projection evaluated at a pair. -/
@[simp] theorem fst_apply (X : RightComodule R C M) (Y : RightComodule R C N)
    (p : M × N) : fst X Y p = p.1 := (rfl)

/-- The second colinear projection evaluated at a pair. -/
@[simp] theorem snd_apply (X : RightComodule R C M) (Y : RightComodule R C N)
    (p : M × N) : snd X Y p = p.2 := (rfl)


variable {P : Type q} [AddCommMonoid P] [Module R P]
variable {X : RightComodule R C M} {Y : RightComodule R C N}
variable {Z : RightComodule R C P}

/-- Pair two colinear maps with a common source into the product comodule. -/
def pair (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y) :
    RightComoduleHom Z (RightComodule.prod X Y) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  colinear := by
    apply LinearMap.ext
    intro p
    apply RightComodule.tensor_ext
    · calc
        _ = X.coaction (f p) :=
          LinearMap.congr_fun (RightComodule.rTensor_fst_coaction_prod X Y) _
        _ = f.toLinearMap.rTensor C (Z.coaction p) := f.colinear_apply p
        _ = _ := by
          change f.toLinearMap.rTensor C (Z.coaction p) =
            ((LinearMap.fst R M N).rTensor C ∘ₗ
              (f.toLinearMap.prod g.toLinearMap).rTensor C) (Z.coaction p)
          rw [← LinearMap.rTensor_comp, LinearMap.fst_prod]
    · calc
        _ = Y.coaction (g p) :=
          LinearMap.congr_fun (RightComodule.rTensor_snd_coaction_prod X Y) _
        _ = g.toLinearMap.rTensor C (Z.coaction p) := g.colinear_apply p
        _ = _ := by
          change g.toLinearMap.rTensor C (Z.coaction p) =
            ((LinearMap.snd R M N).rTensor C ∘ₗ
              (f.toLinearMap.prod g.toLinearMap).rTensor C) (Z.coaction p)
          rw [← LinearMap.rTensor_comp, LinearMap.snd_prod]

/-- The underlying linear map of a colinear pair is the usual linear pairing. -/
@[simp] theorem pair_toLinearMap (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y) :
    (pair f g).toLinearMap = f.toLinearMap.prod g.toLinearMap := rfl

/-- A colinear pair evaluated at an element. -/
@[simp] theorem pair_apply (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y) (p : P) :
    pair f g p = (f p, g p) := rfl

/-- The first projection recovers the first map of a pair. -/
@[simp] theorem fst_pair (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y) :
    (fst X Y).comp (pair f g) = f := by
  apply ext
  intro p
  rfl

/-- The second projection recovers the second map of a pair. -/
@[simp] theorem snd_pair (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y) :
    (snd X Y).comp (pair f g) = g := by
  apply ext
  intro p
  rfl

/-- Pairing the two coordinates of a map recovers that map. -/
@[simp] theorem pair_eta (h : RightComoduleHom Z (RightComodule.prod X Y)) :
    pair ((fst X Y).comp h) ((snd X Y).comp h) = h := by
  apply ext
  intro p
  exact Prod.ext rfl rfl

/-- The pair of the product projections is the identity map. -/
@[simp] theorem pair_fst_snd (X : RightComodule R C M) (Y : RightComodule R C N) :
    pair (fst X Y) (snd X Y) = id (RightComodule.prod X Y) := by
  apply ext
  intro p
  exact Prod.ext rfl rfl

/-- Maps into a product comodule are determined by their two projections. -/
@[ext] theorem prod_ext {h k : RightComoduleHom Z (RightComodule.prod X Y)}
    (hfst : (fst X Y).comp h = (fst X Y).comp k)
    (hsnd : (snd X Y).comp h = (snd X Y).comp k) : h = k := by
  apply ext
  intro p
  exact Prod.ext (DFunLike.congr_fun hfst p) (DFunLike.congr_fun hsnd p)

/-- A map into the product with prescribed projections is their pair. -/
theorem pair_unique (f : RightComoduleHom Z X) (g : RightComoduleHom Z Y)
    (h : RightComoduleHom Z (RightComodule.prod X Y))
    (hfst : (fst X Y).comp h = f) (hsnd : (snd X Y).comp h = g) : h = pair f g := by
  apply prod_ext
  · exact hfst.trans (fst_pair f g).symm
  · exact hsnd.trans (snd_pair f g).symm

/-- The binary-product universal property for specified right comodules. -/
def prodEquiv (X : RightComodule R C M) (Y : RightComodule R C N)
    (Z : RightComodule R C P) :
    (RightComoduleHom Z X × RightComoduleHom Z Y) ≃
      RightComoduleHom Z (RightComodule.prod X Y) where
  toFun fg := pair fg.1 fg.2
  invFun h := ((fst X Y).comp h, (snd X Y).comp h)
  left_inv fg := Prod.ext (fst_pair fg.1 fg.2) (snd_pair fg.1 fg.2)
  right_inv h := pair_eta h

/-- The product universal-property equivalence sends two maps to their pair. -/
@[simp] theorem prodEquiv_apply (X : RightComodule R C M) (Y : RightComodule R C N)
    (Z : RightComodule R C P) (fg : RightComoduleHom Z X × RightComoduleHom Z Y) :
    prodEquiv X Y Z fg = pair fg.1 fg.2 := rfl

/-- The inverse universal-property equivalence reads off the two projections. -/
@[simp] theorem prodEquiv_symm_apply (X : RightComodule R C M) (Y : RightComodule R C N)
    (Z : RightComodule R C P) (h : RightComoduleHom Z (RightComodule.prod X Y)) :
    (prodEquiv X Y Z).symm h = ((fst X Y).comp h, (snd X Y).comp h) := rfl

end RightComoduleHom

end Coalgebra
