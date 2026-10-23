/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Hom
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Images of subcoalgebras

The image of a subcoalgebra under a coalgebra homomorphism has underlying submodule
`Submodule.map f.toLinearMap D.toSubmodule`. Membership is characterized by a preimage
belonging to the source subcoalgebra. The image respects identity and composition, is
monotone for containment of underlying submodules, and preserves finite generation.
The image carrier is zero exactly when the source carrier is zero, without an injectivity
hypothesis on the homomorphism.

Containment in a target submodule is equivalent to every member of the source subcoalgebra
mapping into that submodule. The source, target, and a further composition target may lie
in independent universes. No finite-dimensionality assumption is imposed on the ambient
coalgebras.

## References

The carrier and its characteristic API follow Mathlib's `Submodule.map`, `Submodule.mem_map`,
`Submodule.map_id`, `Submodule.map_comp`, `Submodule.map_mono`, and `Submodule.FG.map`.
The subcoalgebra subtype and codomain restriction are supplied by
`AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom`. Zero reflection uses
`CoalgHom.toLinearMap_eq_zero_iff` from `AlgebraicGroups.Algebra.Coalgebra.Hom` and
Mathlib's linear-map range and submodule subsingleton criteria.
-/

@[expose] public section

universe u v w w₁

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- The image of a subcoalgebra under a coalgebra homomorphism. -/
def map (f : C →ₗc[K] C') (D : Subcoalgebra K C) : Subcoalgebra K C' where
  toSubmodule := Submodule.map f.toLinearMap D.toSubmodule
  comul_mem' := by
    intro y hy
    rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
    rcases D.comul_mem' hx with ⟨t, ht⟩
    let I : Submodule K C' := Submodule.map f.toLinearMap D.toSubmodule
    let j : D.toSubmodule →ₗ[K] I := f.toLinearMap.submoduleMap D.toSubmodule
    have hj : I.subtype.comp j = f.toLinearMap.comp D.toSubmodule.subtype :=
      LinearMap.ext fun z => LinearMap.submoduleMap_coe_apply f.toLinearMap z
    refine ⟨TensorProduct.map j j t, ?_⟩
    calc
      TensorProduct.mapIncl I I (TensorProduct.map j j t) =
          TensorProduct.map f.toLinearMap f.toLinearMap
            (TensorProduct.mapIncl D.toSubmodule D.toSubmodule t) := by
        simp only [TensorProduct.mapIncl, TensorProduct.map_map, hj]
      _ = TensorProduct.map f.toLinearMap f.toLinearMap
          (Coalgebra.comul (R := K) x) := by rw [ht]
      _ = Coalgebra.comul (R := K) (f x) :=
        CoalgHomClass.map_comp_comul_apply f x

/-- The underlying submodule of the image is the image of the underlying submodule. -/
@[simp]
theorem map_toSubmodule (f : C →ₗc[K] C') (D : Subcoalgebra K C) :
    (map f D).toSubmodule = Submodule.map f.toLinearMap D.toSubmodule :=
  rfl

/-- The carrier of the image is the set-theoretic image of the source subcoalgebra. -/
@[simp]
theorem coe_map (f : C →ₗc[K] C') (D : Subcoalgebra K C) :
    (map f D : Set C') = f '' (D : Set C) :=
  rfl

/-- An element belongs to the image exactly when it is the image of a member of the
source subcoalgebra. -/
@[simp]
theorem mem_map {f : C →ₗc[K] C'} {D : Subcoalgebra K C} {y : C'} :
    y ∈ map f D ↔ ∃ x ∈ D, f x = y := by
  rw [← SetLike.mem_coe, coe_map]
  rfl

/-- The image carrier of a subcoalgebra is zero exactly when its source carrier is zero.
No injectivity hypothesis on the coalgebra homomorphism is needed. -/
theorem map_toSubmodule_eq_bot_iff (f : C →ₗc[K] C') (D : Subcoalgebra K C) :
    (map f D).toSubmodule = ⊥ ↔ D.toSubmodule = ⊥ := by
  have hrange :
      LinearMap.range (f.comp D.subtype).toLinearMap = (map f D).toSubmodule := by
    calc
      LinearMap.range (f.comp D.subtype).toLinearMap =
          LinearMap.range (f.toLinearMap.comp D.subtype.toLinearMap) :=
        congrArg LinearMap.range (CoalgHom.comp_toLinearMap f D.subtype)
      _ = (map f D).toSubmodule := by
        rw [CoalgHom.toLinearMap_eq_coe D.subtype, subtype_toLinearMap, LinearMap.range_comp,
          Submodule.range_subtype, map_toSubmodule]
  rw [← hrange, LinearMap.range_eq_bot, CoalgHom.toLinearMap_eq_zero_iff]
  exact Submodule.subsingleton_iff_eq_bot

/-- The image of a subcoalgebra under the identity homomorphism is itself. -/
@[simp]
theorem map_id (D : Subcoalgebra K C) : map (CoalgHom.id K C) D = D := by
  apply toSubmodule_injective
  simpa only [map_toSubmodule, CoalgHom.toLinearMap_eq_coe, CoalgHom.id_toLinearMap] using
    (Submodule.map_id D.toSubmodule)

variable {C'' : Type w₁} [AddCommGroup C''] [Module K C''] [Coalgebra K C'']

/-- Taking the image under a composite homomorphism agrees with successive images. -/
theorem map_comp (f : C →ₗc[K] C') (g : C' →ₗc[K] C'') (D : Subcoalgebra K C) :
    map (g.comp f) D = map g (map f D) := by
  apply toSubmodule_injective
  simpa only [map_toSubmodule, CoalgHom.toLinearMap_eq_coe, CoalgHom.comp_toLinearMap] using
    (Submodule.map_comp f.toLinearMap g.toLinearMap D.toSubmodule)

/-- Containment of the image in a target submodule is equivalent to every member of the
source subcoalgebra mapping into that submodule. -/
theorem map_le_iff {f : C →ₗc[K] C'} {D : Subcoalgebra K C} {S : Submodule K C'} :
    (map f D).toSubmodule ≤ S ↔ ∀ x ∈ D, f x ∈ S := by
  constructor
  · intro h x hx
    exact h (mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact h x hx

/-- Taking images preserves containment of underlying submodules. -/
theorem map_mono {f : C →ₗc[K] C'} {D E : Subcoalgebra K C}
    (hDE : D.toSubmodule ≤ E.toSubmodule) :
    (map f D).toSubmodule ≤ (map f E).toSubmodule := by
  simpa only [map_toSubmodule] using (Submodule.map_mono (f := f.toLinearMap) hDE)

/-- The image of a subcoalgebra with finitely generated underlying submodule has finitely
generated underlying submodule. -/
theorem fg_map (f : C →ₗc[K] C') {D : Subcoalgebra K C} (hD : D.toSubmodule.FG) :
    (map f D).toSubmodule.FG := by
  simpa only [map_toSubmodule] using hD.map f.toLinearMap

end Subcoalgebra
