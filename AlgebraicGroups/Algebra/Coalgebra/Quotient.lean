/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Quotient

/-!
# Coalgebra morphisms on coideal quotients

A coalgebra homomorphism vanishing on a coideal descends uniquely through the
quotient projection by `Submodule.liftQCoalgHom`. A coalgebra homomorphism carrying
one coideal into another induces `Submodule.mapQCoalgHom` between their quotients.
The latter construction respects identity and composition.

These constructions use Mathlib's quotient coalgebra structure and linear quotient
maps. The scalars are a commutative ring, the modules are additive commutative
groups, and the scalar, source and target universes are independent. Preservation
of counit and comultiplication requires only `CoalgebraStruct`, not the coalgebra
laws. No algebra structure, field hypothesis, flatness or projectivity is required.

## References

- `Mathlib.RingTheory.Coalgebra.Quotient` supplies coideals, quotient structures
  and the bundled projection `Coalgebra.Quotient.mkQCoalgHom`.
- `Mathlib.RingTheory.Coalgebra.Hom` supplies bundled coalgebra homomorphisms,
  extensionality and composition.
- `Mathlib.LinearAlgebra.Quotient.Basic` supplies `Submodule.liftQ`,
  `Submodule.mapQ` and the linear quotient universal property.
- `Mathlib.LinearAlgebra.TensorProduct.Map` supplies tensor-map composition.
-/

@[expose] public section

universe u v w z

open Coalgebra

namespace Submodule

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type w} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]

/-- Descend a coalgebra homomorphism vanishing on a coideal through the quotient projection. -/
def liftQCoalgHom (I : Submodule R C) [I.IsCoideal] (f : C →ₗc[R] D)
    (h : I ≤ LinearMap.ker f.toLinearMap) : (C ⧸ I) →ₗc[R] D where
  toLinearMap := I.liftQ f.toLinearMap h
  counit_comp := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := I.mkQ_surjective x
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, mkQ_apply, liftQ_apply,
      Coalgebra.Quotient.counit_mk] using CoalgHomClass.counit_comp_apply f y
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := I.mkQ_surjective x
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, mkQ_apply, Coalgebra.Quotient.comul_mk,
      TensorProduct.map_map, liftQ_mkQ, liftQ_apply] using
      CoalgHomClass.map_comp_comul_apply f y

/-- The linear map underlying the descended homomorphism is the linear quotient lift. -/
@[simp]
theorem liftQCoalgHom_toLinearMap (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) :
    (I.liftQCoalgHom f h).toLinearMap = I.liftQ f.toLinearMap h :=
  rfl

/-- The descended homomorphism agrees with the original homomorphism on representatives. -/
@[simp]
theorem liftQCoalgHom_mk (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) (x : C) :
    I.liftQCoalgHom f h (Submodule.Quotient.mk (p := I) x) = f x :=
  rfl

/-- Composing the descended homomorphism with the quotient projection recovers the original. -/
theorem liftQCoalgHom_comp_mkQCoalgHom (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) :
    (I.liftQCoalgHom f h).comp (Coalgebra.Quotient.mkQCoalgHom I) = f :=
  CoalgHom.ext fun x => liftQCoalgHom_mk I f h x

/-- A coalgebra homomorphism factoring the original through the quotient is its unique lift. -/
theorem liftQCoalgHom_unique (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap)
    (g : (C ⧸ I) →ₗc[R] D) (hg : g.comp (Coalgebra.Quotient.mkQCoalgHom I) = f) :
    g = I.liftQCoalgHom f h := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  calc
    g (I.mkQ y) = f y := CoalgHom.congr_fun hg y
    _ = I.liftQCoalgHom f h (I.mkQ y) := (liftQCoalgHom_mk I f h y).symm

/-- A coalgebra homomorphism carrying a coideal into a coideal induces a homomorphism
between the quotients. -/
def mapQCoalgHom (I : Submodule R C) (J : Submodule R D) [I.IsCoideal] [J.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) : (C ⧸ I) →ₗc[R] (D ⧸ J) :=
  I.liftQCoalgHom ((Coalgebra.Quotient.mkQCoalgHom J).comp f)
    (by
      have hq : (Coalgebra.Quotient.mkQCoalgHom J : D →ₗ[R] (D ⧸ J)) = J.mkQ := by
        rw [← CoalgHom.toLinearMap_eq_coe]
        rfl
      simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.comp_toLinearMap, hq,
        LinearMap.ker_comp, ker_mkQ] using h)

/-- The linear map underlying the induced quotient homomorphism is the linear quotient map. -/
@[simp]
theorem mapQCoalgHom_toLinearMap (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) :
    (I.mapQCoalgHom J f h).toLinearMap = I.mapQ J f.toLinearMap h :=
  rfl

/-- The induced quotient homomorphism sends the class of `x` to the class of `f x`. -/
@[simp]
theorem mapQCoalgHom_mk (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) (x : C) :
    I.mapQCoalgHom J f h (Submodule.Quotient.mk (p := I) x) =
      Submodule.Quotient.mk (p := J) (f x) :=
  rfl

/-- The induced quotient homomorphism intertwines the two quotient projections. -/
theorem mapQCoalgHom_comp_mkQCoalgHom (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) :
    (I.mapQCoalgHom J f h).comp (Coalgebra.Quotient.mkQCoalgHom I) =
      (Coalgebra.Quotient.mkQCoalgHom J).comp f :=
  CoalgHom.ext fun x => mapQCoalgHom_mk I J f h x

/-- The quotient homomorphism induced by the identity is the identity. -/
@[simp]
theorem mapQCoalgHom_id (I : Submodule R C) [I.IsCoideal] :
    I.mapQCoalgHom I (CoalgHom.id R C) (Submodule.comap_id I).symm.le =
      CoalgHom.id R (C ⧸ I) := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  simpa only [mkQ_apply, CoalgHom.id_apply] using
    (mapQCoalgHom_mk I I (CoalgHom.id R C) (Submodule.comap_id I).symm.le y)

variable {E : Type z} [AddCommGroup E] [Module R E] [CoalgebraStruct R E]

/-- Inducing quotient homomorphisms commutes with composition. -/
theorem mapQCoalgHom_comp (I : Submodule R C) (J : Submodule R D)
    (L : Submodule R E) [I.IsCoideal] [J.IsCoideal] [L.IsCoideal]
    (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    (hf : I ≤ J.comap f.toLinearMap) (hg : J ≤ L.comap g.toLinearMap) :
    I.mapQCoalgHom L (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (J.mapQCoalgHom L g hg).comp (I.mapQCoalgHom J f hf) := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  simp only [mkQ_apply, mapQCoalgHom_mk, CoalgHom.comp_apply]

end Submodule
