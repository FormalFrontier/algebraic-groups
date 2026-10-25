/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Map
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Subcoalgebra image isomorphisms and transport

A coalgebra homomorphism injective on a subcoalgebra identifies that subcoalgebra with
its image as a coalgebra. Only injectivity on the source subcoalgebra is required;
the homomorphism can fail to be injective on the ambient coalgebra. Finite generation
of the image is then equivalent to finite generation of the source. The corresponding
statement for the subcoalgebra subtypes uses `Module.Finite`.

An ambient coalgebra equivalence induces an equivalence between the types of
subcoalgebras, with forward map given by image and inverse given by image under the
inverse ambient equivalence. The source and target coalgebras may lie in independent
universes. These constructions concern subcoalgebras over a field, with additive
commutative groups and their module and coalgebra structures; no finiteness assumption
on the ambient coalgebras is imposed.

## References

Mathlib's `CoalgEquiv`, `CoalgEquiv.ofBijective`, `Submodule.equivMapOfInjective`,
`Module.Finite.equiv_iff`, and `Module.Finite.iff_fg` provide the equivalence and
finiteness constructions. `Subcoalgebra.Map` supplies the image carrier and its identity,
composition, membership, and finite-generation API. `Subcoalgebra.Hom` supplies the
inclusion and `CoalgHom.codRestrict` with its unique-factorization property.
-/

@[expose] public section

universe u v w w₁

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- A coalgebra homomorphism injective on a subcoalgebra gives a coalgebra equivalence
from that subcoalgebra to its image. Ambient injectivity is not required. -/
noncomputable def equivMapOfInjOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) : D ≃ₗc[K] map f D := by
  let g : D →ₗc[K] map f D :=
    (f.comp D.subtype).codRestrict (map f D)
      (fun x ↦ mem_map.mpr ⟨(x : C), x.property, rfl⟩)
  refine CoalgEquiv.ofBijective (f := g) ⟨?_, ?_⟩
  · exact LinearMap.submoduleMap_injective_of_injOn
      (f := f.toLinearMap) (p := D.toSubmodule) hf
  · intro y
    obtain ⟨x, hx, hxy⟩ := mem_map.mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The image equivalence sends a member to its ambient image. -/
@[simp]
theorem coe_equivMapOfInjOn_apply (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (x : D) :
    (equivMapOfInjOn f D hf x : C') = f (x : C) := by
  rfl

/-- The forward homomorphism is the codomain restriction of the ambient homomorphism
composed with the source inclusion. -/
theorem equivMapOfInjOn_toCoalgHom (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) :
    (equivMapOfInjOn f D hf).toCoalgHom =
      (f.comp D.subtype).codRestrict (map f D)
        (fun x ↦ mem_map.mpr ⟨(x : C), x.property, rfl⟩) := by
  rfl

/-- Inclusion after the image equivalence recovers the ambient homomorphism restricted
to the source subcoalgebra. -/
theorem subtype_comp_equivMapOfInjOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) :
    (map f D).subtype.comp (equivMapOfInjOn f D hf).toCoalgHom =
      f.comp D.subtype := by
  rw [equivMapOfInjOn_toCoalgHom, CoalgHom.subtype_comp_codRestrict]

/-- Inclusion after the canonically coerced image equivalence is the ambient
homomorphism restricted to the source subcoalgebra. -/
@[simp]
theorem subtype_comp_coe_equivMapOfInjOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) :
    (map f D).subtype.comp (equivMapOfInjOn f D hf : D →ₗc[K] map f D) =
      f.comp D.subtype := by
  simpa only [CoalgEquiv.toCoalgHom_eq_coe] using
    subtype_comp_equivMapOfInjOn f D hf

/-- Applying the ambient homomorphism to the inverse image recovers the image member. -/
@[simp]
theorem map_equivMapOfInjOn_symm_apply (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (y : map f D) :
    f ((equivMapOfInjOn f D hf).symm y : C) = (y : C') := by
  simpa only [coe_equivMapOfInjOn_apply] using
    congrArg (fun z : map f D ↦ (z : C'))
      ((equivMapOfInjOn f D hf).apply_symm_apply y)

/-- Every specified source member mapping to an image member is the member selected
by the inverse image equivalence. -/
theorem equivMapOfInjOn_symm_apply_eq (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (y : map f D) (x : D)
    (hxy : f (x : C) = (y : C')) :
    (equivMapOfInjOn f D hf).symm y = x := by
  apply Subtype.ext
  apply hf ((equivMapOfInjOn f D hf).symm y).property x.property
  exact (map_equivMapOfInjOn_symm_apply f D hf y).trans hxy.symm

/-- Under ambient injectivity, forgetting the coalgebra structure gives Mathlib's
linear equivalence between a submodule and its image. -/
theorem equivMapOfInjOn_toLinearEquiv (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Function.Injective f) :
    (equivMapOfInjOn f D hf.injOn).toLinearEquiv =
      Submodule.equivMapOfInjective f.toLinearMap hf D.toSubmodule := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact (coe_equivMapOfInjOn_apply f D hf.injOn x).trans
    (Submodule.coe_equivMapOfInjective_apply f.toLinearMap hf D.toSubmodule x).symm

/-- If a coalgebra homomorphism is injective on a subcoalgebra, its image is finitely
generated exactly when the source is finitely generated. -/
theorem fg_map_iff_of_injOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) :
    (map f D).toSubmodule.FG ↔ D.toSubmodule.FG := by
  exact (Module.Finite.iff_fg (N := (map f D).toSubmodule)).symm.trans
    ((Module.Finite.equiv_iff (equivMapOfInjOn f D hf).toLinearEquiv).symm.trans
      (Module.Finite.iff_fg (N := D.toSubmodule)))

/-- Under injectivity on the subcoalgebra, module-finiteness of the image subtype is
equivalent to module-finiteness of the source subtype. -/
theorem finite_map_iff_of_injOn (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) :
    Module.Finite K (map f D) ↔ Module.Finite K D := by
  exact (Module.Finite.equiv_iff (equivMapOfInjOn f D hf).toLinearEquiv).symm

/-- Taking images under an injective ambient homomorphism is injective on subcoalgebras. -/
theorem map_injective (f : C →ₗc[K] C') (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro D E h
  apply toSubmodule_injective
  apply Submodule.map_injective_of_injective (f := f.toLinearMap) hf
  simpa only [map_toSubmodule] using congrArg toSubmodule h

/-- Equality of images under an injective ambient homomorphism reflects equality of
subcoalgebras. -/
@[simp]
theorem map_inj (f : C →ₗc[K] C') (hf : Function.Injective f)
    {D E : Subcoalgebra K C} : map f D = map f E ↔ D = E := by
  exact (map_injective f hf).eq_iff

end Subcoalgebra

namespace CoalgEquiv

variable {K : Type u} {C : Type v} {C' : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- Transport subcoalgebras along an ambient coalgebra equivalence, by taking the image
under the equivalence and taking the image under its inverse for the inverse operation. -/
noncomputable def subcoalgebraCongr (e : C ≃ₗc[K] C') :
    Subcoalgebra K C ≃ Subcoalgebra K C' := by
  refine
    { toFun := Subcoalgebra.map e.toCoalgHom
      invFun := Subcoalgebra.map e.symm.toCoalgHom
      left_inv := ?_
      right_inv := ?_ }
  · intro D
    rw [← Subcoalgebra.map_comp]
    have h : e.symm.toCoalgHom.comp e.toCoalgHom = CoalgHom.id K C :=
      CoalgHom.ext fun x => e.symm_apply_apply x
    rw [h, Subcoalgebra.map_id]
  · intro D
    rw [← Subcoalgebra.map_comp]
    have h : e.toCoalgHom.comp e.symm.toCoalgHom = CoalgHom.id K C' :=
      CoalgHom.ext fun x => e.apply_symm_apply x
    rw [h, Subcoalgebra.map_id]

/-- Forward transport is the subcoalgebra image under the ambient equivalence. -/
theorem subcoalgebraCongr_apply (e : C ≃ₗc[K] C') (D : Subcoalgebra K C) :
    e.subcoalgebraCongr D = Subcoalgebra.map e.toCoalgHom D := by
  rfl

/-- Inverse transport is the image under the inverse ambient equivalence. -/
theorem subcoalgebraCongr_symm_apply (e : C ≃ₗc[K] C') (D : Subcoalgebra K C') :
    e.subcoalgebraCongr.symm D = Subcoalgebra.map e.symm.toCoalgHom D := by
  rfl

/-- The inverse of subcoalgebra transport is transport under the inverse equivalence. -/
@[simp]
theorem subcoalgebraCongr_symm (e : C ≃ₗc[K] C') :
    e.subcoalgebraCongr.symm = e.symm.subcoalgebraCongr := by
  exact Equiv.ext fun _ => rfl

/-- Membership in a transported subcoalgebra is membership of the inverse ambient image
in the source subcoalgebra. -/
@[simp]
theorem mem_subcoalgebraCongr (e : C ≃ₗc[K] C') (D : Subcoalgebra K C) (y : C') :
    y ∈ e.subcoalgebraCongr D ↔ e.symm y ∈ D := by
  rw [subcoalgebraCongr_apply, Subcoalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [toCoalgHom_eq_coe, coe_toCoalgHom, symm_apply_apply] using hx
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

/-- Transport under the identity coalgebra equivalence is the identity on subcoalgebras. -/
@[simp]
theorem subcoalgebraCongr_refl :
    (CoalgEquiv.refl K C).subcoalgebraCongr = Equiv.refl (Subcoalgebra K C) := by
  apply Equiv.ext
  intro D
  rw [subcoalgebraCongr_apply]
  exact Subcoalgebra.map_id D

variable {C'' : Type w₁} [AddCommGroup C''] [Module K C''] [Coalgebra K C'']

/-- Transport under a composite equivalence is successive transport. -/
theorem subcoalgebraCongr_trans (e : C ≃ₗc[K] C') (e' : C' ≃ₗc[K] C'') :
    (e.trans e').subcoalgebraCongr = e.subcoalgebraCongr.trans e'.subcoalgebraCongr := by
  apply Equiv.ext
  intro D
  simpa only [Equiv.trans_apply, subcoalgebraCongr_apply, toCoalgHom_eq_coe,
    trans_toCoalgHom] using
    (Subcoalgebra.map_comp e.toCoalgHom e'.toCoalgHom D)

/-- Ambient equivalences preserve and reflect module-finiteness of subcoalgebras. -/
theorem finite_subcoalgebraCongr_iff (e : C ≃ₗc[K] C') (D : Subcoalgebra K C) :
    Module.Finite K (e.subcoalgebraCongr D) ↔ Module.Finite K D := by
  change Module.Finite K (e.subcoalgebraCongr D).toSubmodule ↔
    Module.Finite K D.toSubmodule
  rw [Module.Finite.iff_fg, Module.Finite.iff_fg]
  constructor
  · intro h
    have h' := Subcoalgebra.fg_map e.symm.toCoalgHom h
    rwa [← subcoalgebraCongr_symm_apply e, Equiv.symm_apply_apply] at h'
  · intro h
    rw [subcoalgebraCongr_apply]
    exact Subcoalgebra.fg_map e.toCoalgHom h

end CoalgEquiv
