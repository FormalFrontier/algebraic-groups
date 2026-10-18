/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupObject.KernelTorsor
import Mathlib.Algebra.Group.Prod
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# A proper symmetric-group inclusion and its unit fibre

The inclusion `S₃ → S₃ × C₂`, `x ↦ (x, 1)`, has a unit fibre and is injective
by the first projection, but is not surjective. We use Mathlib's functor from
ordinary groups to group objects in `Type`, without constructing group-object
structures separately. The pullback is proved directly from its universal property,
independently of the monomorphism criterion.

Addition `ℕ × ℕ → ℕ` gives the cheap boundary: a trivial zero fibre does not imply
injectivity for a monoid source.

## References

* Mathlib, `Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp`, for the functor
  from groups to group objects in `Type`.
* Mathlib, `Mathlib.CategoryTheory.Limits.Types.Pullbacks`, for the pullback criterion.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace CategoryTheory.GrpObj

private abbrev symmetricGroup : Grp (Type) :=
  GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of (Equiv.Perm (Fin 3)))

private abbrev symmetricProduct : Grp (Type) :=
  GrpTypeEquivalenceGrp.inverse.obj
    (GrpCat.of (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))

private abbrev symmetricInclusion : symmetricGroup.X ⟶ symmetricProduct.X :=
  (GrpTypeEquivalenceGrp.inverse.map
    (GrpCat.ofHom (MonoidHom.inl (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))).hom.hom

private theorem symmetric_inclusion_isPullback :
    IsPullback η[symmetricGroup.X] (toUnit (𝟙_ (Type))) symmetricInclusion
      η[symmetricProduct.X] := by
  let : Unique (𝟙_ (Type)) := Types.isTerminalEquivUnique _ isTerminalTensorUnit
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext x
    rfl
  · intro x y _
    exact Subsingleton.elim _ _
  · intro x u hx
    refine ⟨u, ?_, Subsingleton.elim _ _⟩
    exact (congrArg (fun y : symmetricProduct.X ↦ y.1) hx).symm

private theorem symmetric_inclusion_mono : Mono symmetricInclusion := by
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y h
  exact congrArg (fun z : symmetricProduct.X ↦ z.1) h

/-- The canonical unit-to-fibre lift for the proper inclusion `S₃ → S₃ × C₂` is an iso. -/
private theorem symmetric_inclusion_lift_isIso :
    IsIso (symmetric_inclusion_isPullback.lift η[symmetricGroup.X] (𝟙 (𝟙_ (Type)))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom symmetricInclusion)) :=
  (mono_iff_isIso_lift_one η[symmetricGroup.X] symmetricInclusion
    symmetric_inclusion_isPullback).mp symmetric_inclusion_mono

private theorem symmetric_inclusion_not_surjective :
    ¬ Function.Surjective symmetricInclusion := by
  intro h
  obtain ⟨x, hx⟩ := h (1, Multiplicative.ofAdd (1 : ZMod 2))
  exact zero_ne_one
    (congrArg (fun y : symmetricProduct.X ↦ Multiplicative.toAdd y.2) hx)

private theorem natSum_boundary :
    (∀ a b : ℕ, a + b = 0 ↔ a = 0 ∧ b = 0) ∧
      ¬ Function.Injective (fun p : ℕ × ℕ ↦ p.1 + p.2) := by
  refine ⟨fun _ _ ↦ Nat.add_eq_zero_iff, ?_⟩
  intro h
  have he : ((1, 0) : ℕ × ℕ) = (0, 1) := h (by rfl)
  exact Nat.one_ne_zero (congrArg (fun p : ℕ × ℕ ↦ p.1) he)

end CategoryTheory.GrpObj
