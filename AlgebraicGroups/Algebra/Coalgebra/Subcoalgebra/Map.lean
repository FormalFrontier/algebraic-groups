/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Hom
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
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

open TauCeti


universe u v w w₁

namespace TauCeti.Subcoalgebra

variable {K : Type u} {C : Type v} {C' : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

/-- The carrier of the image is the set-theoretic image of the source subcoalgebra. -/
@[simp]
theorem coe_map (f : C →ₗc[K] C') (D : Subcoalgebra K C) :
    (map f D : Set C') = f '' (D : Set C) :=
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
        rw [CoalgHom.toLinearMap_eq_ofClass D.subtype, subtype_toLinearMap, LinearMap.range_comp,
          Submodule.range_subtype, map_toSubmodule]
  rw [← hrange, LinearMap.range_eq_bot, CoalgHom.toLinearMap_eq_zero_iff]
  exact Submodule.subsingleton_iff_eq_bot

/-- Containment of the image in a target submodule is equivalent to every member of the
source subcoalgebra mapping into that submodule. -/
theorem map_toSubmodule_le_iff {f : C →ₗc[K] C'} {D : Subcoalgebra K C} {S : Submodule K C'} :
    (map f D).toSubmodule ≤ S ↔ ∀ x ∈ D, f x ∈ S := by
  constructor
  · intro h x hx
    exact h (mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact h x hx

/-- The image of a subcoalgebra with finitely generated underlying submodule has finitely
generated underlying submodule. -/
theorem fg_map (f : C →ₗc[K] C') {D : Subcoalgebra K C} (hD : D.toSubmodule.FG) :
    (map f D).toSubmodule.FG := by
  simpa only [map_toSubmodule] using hD.map f.toLinearMap

end TauCeti.Subcoalgebra
