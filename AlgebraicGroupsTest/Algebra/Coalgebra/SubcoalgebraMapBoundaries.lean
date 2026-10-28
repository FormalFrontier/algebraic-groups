/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Zero subcoalgebras and carrier images

The zero submodule of any coalgebra over a field is a subcoalgebra. Its canonical
restricted coalgebra has zero counit, which is not surjective onto the field. Its
inclusion is a coalgebra homomorphism whose underlying linear map is zero; this does not
supply a zero coalgebra homomorphism between arbitrary coalgebras.

Images of this subcoalgebra's carrier under arbitrary coalgebra homomorphisms remain
zero. Identity and composition are checked on these carriers, including the intermediate
image in a different ambient coalgebra. The source, target, and final ambient coalgebras
may lie in independent universes. The calculations use only submodule images and do not
require a bundled subcoalgebra image construction or its laws.

## References

The zero subcoalgebra uses `Subcoalgebra.ofSubmodule`, and its restricted coalgebra and inclusion
use `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom`. Carrier calculations reuse
`Submodule.map_bot`, `Submodule.map_id`, and `Submodule.map_comp` from
`Mathlib.Algebra.Module.Submodule.Map`. Finiteness of the zero subtype uses
`Submodule.fg_bot` and `Module.Finite.iff_fg` from `Mathlib.RingTheory.Finiteness.Basic`.
-/

@[expose] public section

open TauCeti


noncomputable section

universe u v w z

namespace TauCeti.Subcoalgebra

variable (K : Type u) (C : Type v)
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The zero submodule, equipped with its comultiplication closure proof. -/
private abbrev zeroSubcoalgebra : Subcoalgebra K C :=
  Subcoalgebra.ofSubmodule (⊥ : Submodule K C) <| by
    intro x hx
    rw [Submodule.mem_bot] at hx
    subst x
    rw [map_zero]
    exact (LinearMap.range _).zero_mem

private lemma zeroSubcoalgebra_toSubmodule :
    (zeroSubcoalgebra K C).toSubmodule = ⊥ :=
  Subcoalgebra.ofSubmodule_carrier _ _

private lemma mem_zeroSubcoalgebra (x : C) :
    x ∈ zeroSubcoalgebra K C ↔ x = 0 := by
  change x ∈ (zeroSubcoalgebra K C).toSubmodule ↔ x = 0
  rw [zeroSubcoalgebra_toSubmodule, Submodule.mem_bot]

private lemma coe_zeroSubcoalgebra (x : (zeroSubcoalgebra K C).toSubmodule) : (x : C) = 0 :=
  (mem_zeroSubcoalgebra K C (x : C)).mp x.property

private lemma zeroSubcoalgebra_subtype_toLinearMap :
    (zeroSubcoalgebra K C).subtype.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  exact (Subcoalgebra.subtype_apply (zeroSubcoalgebra K C) x).trans
    (coe_zeroSubcoalgebra K C x)

private lemma zeroSubcoalgebra_counit_eq_zero :
    Coalgebra.counit (R := K) (A := (zeroSubcoalgebra K C).toSubmodule) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [Subcoalgebra.counit_apply, coe_zeroSubcoalgebra, map_zero,
    LinearMap.zero_apply]

/-- Every coalgebra over a field has a finite zero subcoalgebra whose canonical counit
is not surjective. Its canonical inclusion has zero underlying linear map. -/
theorem exists_subcoalgebra_bot_counit_not_surjective :
    ∃ D : Subcoalgebra K C,
      D.toSubmodule = ⊥ ∧ Module.Finite K D.toSubmodule ∧ D.subtype.toLinearMap = 0 ∧
      Coalgebra.counit (R := K) (A := D.toSubmodule) = 0 ∧
      ¬ Function.Surjective (Coalgebra.counit (R := K) (A := D.toSubmodule)) := by
  refine ⟨zeroSubcoalgebra K C, zeroSubcoalgebra_toSubmodule K C, ?_,
    zeroSubcoalgebra_subtype_toLinearMap K C, zeroSubcoalgebra_counit_eq_zero K C, ?_⟩
  · have hfg : (zeroSubcoalgebra K C).toSubmodule.FG := by
      rw [zeroSubcoalgebra_toSubmodule]
      exact Submodule.fg_bot
    exact Module.Finite.iff_fg.mpr hfg
  · intro h
    obtain ⟨x, hx⟩ := h 1
    have h01 : (0 : K) = 1 := by
      simpa only [zeroSubcoalgebra_counit_eq_zero, LinearMap.zero_apply] using hx
    exact zero_ne_one h01

variable {E : Type w} {F : Type z}
variable [AddCommGroup E] [Module K E] [Coalgebra K E]
variable [AddCommGroup F] [Module K F] [Coalgebra K F]

private lemma zeroSubcoalgebra_carrier_map (f : C →ₗc[K] E) :
    Submodule.map f.toLinearMap (zeroSubcoalgebra K C).toSubmodule = ⊥ := by
  rw [zeroSubcoalgebra_toSubmodule, Submodule.map_bot]

/-- The zero subcoalgebra has zero carrier image under any coalgebra homomorphism.
Identity preserves both its carrier and its intermediate image, and composition gives
the same zero carrier as successive images, without an injectivity hypothesis. -/
theorem exists_subcoalgebra_bot_carrier_maps (f : C →ₗc[K] E) (g : E →ₗc[K] F) :
    ∃ D : Subcoalgebra K C,
      D.toSubmodule = ⊥ ∧
      Submodule.map f.toLinearMap D.toSubmodule = ⊥ ∧
      Submodule.map (CoalgHom.id K C).toLinearMap D.toSubmodule = D.toSubmodule ∧
      Submodule.map (CoalgHom.id K E).toLinearMap
          (Submodule.map f.toLinearMap D.toSubmodule) =
        Submodule.map f.toLinearMap D.toSubmodule ∧
      Submodule.map (g.comp f).toLinearMap D.toSubmodule =
        Submodule.map g.toLinearMap (Submodule.map f.toLinearMap D.toSubmodule) ∧
      Submodule.map g.toLinearMap (Submodule.map f.toLinearMap D.toSubmodule) = ⊥ := by
  refine ⟨zeroSubcoalgebra K C, zeroSubcoalgebra_toSubmodule K C,
    zeroSubcoalgebra_carrier_map K C f, ?_, ?_, ?_, ?_⟩
  · exact Submodule.map_id _
  · exact Submodule.map_id _
  · exact Submodule.map_comp f.toLinearMap g.toLinearMap _
  · rw [zeroSubcoalgebra_carrier_map K C f, Submodule.map_bot]

end TauCeti.Subcoalgebra
