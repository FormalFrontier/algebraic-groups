/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra
public import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Subcoalgebra inclusions and factorization

The inclusion `Subcoalgebra.subtype` is a coalgebra homomorphism for the restricted
coalgebra structure on a subcoalgebra. A coalgebra homomorphism whose values lie in a
subcoalgebra factors uniquely through this inclusion, using `CoalgHom.codRestrict`.
Restriction recovers the identity from the inclusion and commutes with precomposition.
The source coalgebra can lie in a universe independent of the ambient coalgebra.

## References

The bundled maps and their extensionality and composition API follow
`Mathlib.RingTheory.Coalgebra.Hom`. Codomain restriction uses `LinearMap.codRestrict` and
`LinearMap.subtype_comp_codRestrict` from `Mathlib.Algebra.Module.Submodule.LinearMap`.
The comultiplication compatibility follows from tensor-map composition in
`Mathlib.LinearAlgebra.TensorProduct.Map` and injectivity of tensor inclusions over a
field, as in `Mathlib.RingTheory.Flat.Basic`.
-/

@[expose] public section

universe u v w w₁

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The comultiplication of the subcoalgebra instance is the restricted comultiplication. -/
theorem coalgebra_comul_eq (D : Subcoalgebra K C) :
    Coalgebra.comul (R := K) (A := D) = D.comul :=
  rfl

/-- The counit of the subcoalgebra instance is the restricted counit. -/
theorem coalgebra_counit_eq (D : Subcoalgebra K C) :
    Coalgebra.counit (R := K) (A := D) = D.counit :=
  rfl

/-- Tensor inclusion intertwines the subcoalgebra instance's and ambient comultiplications. -/
@[simp]
theorem mapIncl_comp_coalgebra_comul (D : Subcoalgebra K C) :
    TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ
        Coalgebra.comul (R := K) (A := D) =
      Coalgebra.comul (R := K) (A := C) ∘ₗ D.toSubmodule.subtype :=
  D.mapIncl_comp_comul

/-- Comultiplication in the subcoalgebra maps to ambient comultiplication under inclusion. -/
@[simp]
theorem mapIncl_coalgebra_comul (D : Subcoalgebra K C) (x : D) :
    TensorProduct.mapIncl D.toSubmodule D.toSubmodule
        (Coalgebra.comul (R := K) (A := D) x) =
      Coalgebra.comul (R := K) (A := C) (x : C) :=
  LinearMap.congr_fun D.mapIncl_comp_coalgebra_comul x

/-- The ambient counit composed with inclusion is the counit of the subcoalgebra instance. -/
@[simp]
theorem coalgebra_counit_comp_subtype (D : Subcoalgebra K C) :
    Coalgebra.counit (R := K) (A := C) ∘ₗ D.toSubmodule.subtype =
      Coalgebra.counit (R := K) (A := D) :=
  D.counit_comp_subtype

/-- The counit of the subcoalgebra instance agrees with the ambient counit on members. -/
@[simp]
theorem coalgebra_counit_apply (D : Subcoalgebra K C) (x : D) :
    Coalgebra.counit (R := K) (A := D) x =
      Coalgebra.counit (R := K) (A := C) (x : C) :=
  D.counit_apply x

/-- The inclusion of a subcoalgebra into its ambient coalgebra. -/
noncomputable def subtype (D : Subcoalgebra K C) : D →ₗc[K] C where
  toLinearMap := D.toSubmodule.subtype
  counit_comp := D.coalgebra_counit_comp_subtype
  map_comp_comul := D.mapIncl_comp_coalgebra_comul

@[simp]
theorem subtype_toLinearMap (D : Subcoalgebra K C) :
    D.subtype.toLinearMap = D.toSubmodule.subtype :=
  rfl

@[simp]
theorem subtype_apply (D : Subcoalgebra K C) (x : D) : D.subtype x = (x : C) :=
  rfl

/-- The inclusion of a subcoalgebra is injective. -/
theorem subtype_injective (D : Subcoalgebra K C) : Function.Injective D.subtype :=
  coe_injective

variable {A : Type w} [AddCommGroup A] [Module K A] [Coalgebra K A]

/-- Coalgebra homomorphisms into a subcoalgebra are determined by their ambient values. -/
theorem coalgHom_ext {D : Subcoalgebra K C} {f g : A →ₗc[K] D}
    (h : ∀ x, (f x : C) = (g x : C)) : f = g :=
  CoalgHom.ext fun x => coe_injective (h x)

/-- Composition with the inclusion of a subcoalgebra is injective. -/
theorem subtype_comp_injective (D : Subcoalgebra K C) :
    Function.Injective (fun f : A →ₗc[K] D => D.subtype.comp f) := by
  intro f g h
  exact CoalgHom.ext fun x => D.subtype_injective (CoalgHom.congr_fun h x)

@[simp]
theorem subtype_comp_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] D} :
    D.subtype.comp f = D.subtype.comp g ↔ f = g :=
  D.subtype_comp_injective.eq_iff

end Subcoalgebra

namespace CoalgHom

variable {K : Type u} {C : Type v} {A : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup A] [Module K A] [Coalgebra K A]

/-- Restrict the codomain of a coalgebra homomorphism to a subcoalgebra containing its values. -/
noncomputable def codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : A →ₗc[K] D where
  toLinearMap := f.toLinearMap.codRestrict D.toSubmodule h
  counit_comp := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, D.coalgebra_counit_apply, LinearMap.codRestrict_apply]
    exact CoalgHomClass.counit_comp_apply f x
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    apply Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule
    simp only [LinearMap.comp_apply]
    calc
      TensorProduct.mapIncl D.toSubmodule D.toSubmodule
          (TensorProduct.map (f.toLinearMap.codRestrict D.toSubmodule h)
            (f.toLinearMap.codRestrict D.toSubmodule h)
            (Coalgebra.comul (R := K) (A := A) x)) =
          TensorProduct.map f.toLinearMap f.toLinearMap
            (Coalgebra.comul (R := K) (A := A) x) := by
        simp only [TensorProduct.mapIncl, TensorProduct.map_map,
          LinearMap.subtype_comp_codRestrict]
      _ = Coalgebra.comul (R := K) (A := C) (f x) :=
        CoalgHomClass.map_comp_comul_apply f x
      _ = TensorProduct.mapIncl D.toSubmodule D.toSubmodule
          (Coalgebra.comul (R := K) (A := D)
            (f.toLinearMap.codRestrict D.toSubmodule h x)) := by
        rw [D.mapIncl_coalgebra_comul, LinearMap.codRestrict_apply]
        rfl

@[simp]
theorem codRestrict_toLinearMap (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) :
    (f.codRestrict D h).toLinearMap = f.toLinearMap.codRestrict D.toSubmodule h :=
  rfl

/-- Codomain restriction sends an element to the same value, viewed as a subcoalgebra member. -/
theorem codRestrict_apply (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (x : A) : f.codRestrict D h x = ⟨f x, h x⟩ :=
  rfl

@[simp]
theorem coe_codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (x : A) : (f.codRestrict D h x : C) = f x :=
  rfl

/-- Inclusion after codomain restriction recovers the original homomorphism. -/
@[simp]
theorem subtype_comp_codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : D.subtype.comp (f.codRestrict D h) = f :=
  CoalgHom.ext fun _ => rfl

/-- Restricting a subcoalgebra's inclusion back to itself is the identity. -/
@[simp]
theorem codRestrict_subtype (D : Subcoalgebra K C) :
    D.subtype.codRestrict D (fun x => Subcoalgebra.coe_mem x) = CoalgHom.id K D :=
  CoalgHom.ext fun _ => Subtype.ext rfl

/-- Restricting the ambient form of a homomorphism into a subcoalgebra recovers that
homomorphism. -/
@[simp]
theorem codRestrict_subtype_comp (D : Subcoalgebra K C) (g : A →ₗc[K] D) :
    (D.subtype.comp g).codRestrict D
        (fun x => Subcoalgebra.coe_mem (g x)) = g :=
  CoalgHom.ext fun _ => Subtype.ext rfl

/-- A factorization through a subcoalgebra inclusion is its codomain restriction. -/
theorem codRestrict_unique (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (g : A →ₗc[K] D) (hg : D.subtype.comp g = f) :
    g = f.codRestrict D h := by
  apply D.subtype_comp_injective
  exact hg.trans (subtype_comp_codRestrict f D h).symm

/-- Two codomain restrictions are equal exactly when the original homomorphisms are equal. -/
@[simp]
theorem codRestrict_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] C}
    (hf : ∀ x, f x ∈ D) (hg : ∀ x, g x ∈ D) :
    f.codRestrict D hf = g.codRestrict D hg ↔ f = g := by
  constructor
  · intro h
    have h' := congrArg (fun k : A →ₗc[K] D => D.subtype.comp k) h
    simpa only [subtype_comp_codRestrict] using h'
  · intro h
    subst g
    exact CoalgHom.ext fun _ => Subtype.ext rfl

/-- A homomorphism factors uniquely through a subcoalgebra inclusion exactly when its values
belong to the subcoalgebra. -/
theorem existsUnique_subtype_comp_iff (f : A →ₗc[K] C) (D : Subcoalgebra K C) :
    (∃! g : A →ₗc[K] D, D.subtype.comp g = f) ↔ ∀ x, f x ∈ D := by
  constructor
  · rintro ⟨g, hg, _⟩ x
    rw [← hg]
    exact Subcoalgebra.coe_mem (g x)
  · intro h
    exact ⟨f.codRestrict D h, subtype_comp_codRestrict f D h,
      fun g hg => codRestrict_unique f D h g hg⟩

variable {B : Type w₁} [AddCommGroup B] [Module K B] [Coalgebra K B]

/-- Codomain restriction commutes with precomposition by a coalgebra homomorphism. -/
@[simp]
theorem codRestrict_comp (f : B →ₗc[K] C) (g : A →ₗc[K] B) (D : Subcoalgebra K C)
    (h : ∀ y, f y ∈ D) :
    (f.comp g).codRestrict D (fun x => h (g x)) = (f.codRestrict D h).comp g :=
  CoalgHom.ext fun _ => Subtype.ext rfl

end CoalgHom
