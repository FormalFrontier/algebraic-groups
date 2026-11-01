/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule

/-!
# Ranges of right-comodule morphisms

The linear range of a morphism between specified right `C`-comodules is
image-stable, without a flatness assumption. If `C` is flat over the commutative
semiring `R`, `Coalgebra.RightComoduleHom.range` equips that existing submodule
with its induced right coaction. Neither the source nor the target module needs
to be flat, and all their universes are independent.

`Coalgebra.RightComoduleHom.rangeRestrict` fixes its underlying linear map to
Mathlib's `LinearMap.rangeRestrict`; the existing subcomodule universal property
supplies colinearity. Inclusion after this bundled
comodule morphism is the original morphism. The restriction is surjective onto
its range, not necessarily onto the original target.

The inclusion, induced-coaction equations, extensionality and universal property
are those of the existing `Subcomodule` API. In particular, the universal property
of `range f` also applies to morphisms from any independently-universed source
whose values lie in this same range. No identification with the range of a
composite is needed. Right counitality uses the right unitor, with the coalgebra
factor on the right.

## References

This construction reuses the right-comodule and subcomodule formalization in
`AlgebraicGroups.Algebra.Coalgebra.RightComodule`, and Mathlib's linear-map range,
tensor-product and flatness APIs. The bibliographic background for right
comodules is recorded in that module.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra.RightComoduleHom

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

/-- The linear range of a right-comodule morphism is image-stable, without
flatness of the coacting coalgebra. -/
theorem range_isStable (f : RightComoduleHom X Y) :
    Y.IsStable (LinearMap.range f.toLinearMap) := by
  rintro n ⟨m, rfl⟩
  refine ⟨f.toLinearMap.rangeRestrict.rTensor C (X.coaction m), ?_⟩
  calc
    (LinearMap.range f.toLinearMap).subtype.rTensor C
        (f.toLinearMap.rangeRestrict.rTensor C (X.coaction m)) =
        f.toLinearMap.rTensor C (X.coaction m) := by
      rw [← LinearMap.rTensor_comp_apply, LinearMap.subtype_comp_rangeRestrict]
    _ = Y.coaction (f.toLinearMap m) := (f.colinear_apply m).symm

section Flat

variable [Module.Flat R C]

/-- The range subcomodule, with the induced coaction on the existing linear range. -/
noncomputable def range (f : RightComoduleHom X Y) : Y.Subcomodule :=
  RightComodule.Subcomodule.ofIsStable Y (LinearMap.range f.toLinearMap) (range_isStable f)

/-- Forgetting the induced coaction gives the original linear-map range. -/
@[simp] theorem range_toSubmodule (f : RightComoduleHom X Y) :
    (range f).toSubmodule = LinearMap.range f.toLinearMap := rfl

/-- A member of the range is precisely an image of an element of the source. -/
@[simp] theorem mem_range (f : RightComoduleHom X Y) (n : N) :
    n ∈ range f ↔ ∃ m, f m = n :=
  LinearMap.mem_range (f := f.toLinearMap)

/-- The canonical colinear factor through the induced range subcomodule,
with the ordinary linear range restriction as its underlying map. -/
noncomputable def rangeRestrict (f : RightComoduleHom X Y) :
    RightComoduleHom X (range f).comodule :=
  { toLinearMap := f.toLinearMap.rangeRestrict
    colinear := by
      obtain ⟨g, hg, _⟩ := (range f).existsUnique_factorization X f
        (fun m ↦ LinearMap.mem_range_self f.toLinearMap m)
      have hg_linear : g.toLinearMap = f.toLinearMap.rangeRestrict := by
        apply LinearMap.ext
        intro m
        apply Subtype.ext
        exact congrArg (fun h : RightComoduleHom X Y ↦ h m) hg
      rw [← hg_linear]
      exact g.colinear }

/-- Inclusion after range restriction recovers the original bundled morphism. -/
@[simp] theorem subtype_comp_rangeRestrict (f : RightComoduleHom X Y) :
    (range f).subtype.comp (rangeRestrict f) = f := by
  apply RightComoduleHom.ext
  intro m
  rfl

/-- The canonical comodule factor has the ordinary linear range restriction as its
underlying linear map, on the canonical subtype carrier. -/
@[simp] theorem rangeRestrict_toLinearMap (f : RightComoduleHom X Y) :
    (rangeRestrict f).toLinearMap = f.toLinearMap.rangeRestrict := rfl

/-- Range restriction sends an element to its image, viewed in the linear range. -/
@[simp] theorem rangeRestrict_apply (f : RightComoduleHom X Y) (m : M) :
    @DFunLike.coe _ _ _
        (@RightComoduleHom.instFunLike R C M (LinearMap.range f.toLinearMap)
          _ _ _ _ _ _ (range f).addCommMonoid (range f).module X (range f).comodule)
        (rangeRestrict f) m = ⟨f m, LinearMap.mem_range_self f.toLinearMap m⟩ :=
  rfl

/-- Range restriction is surjective onto the induced range comodule. -/
theorem surjective_rangeRestrict (f : RightComoduleHom X Y) :
    Function.Surjective (rangeRestrict f) := by
  change Function.Surjective (rangeRestrict f).toLinearMap
  rw [rangeRestrict_toLinearMap]
  exact LinearMap.surjective_rangeRestrict f.toLinearMap

/-- Every bundled factorization through the same range inclusion equals the
canonical range restriction, by the subcomodule universal property. -/
theorem rangeRestrict_unique (f : RightComoduleHom X Y)
    (g : RightComoduleHom X (range f).comodule)
    (hg : (range f).subtype.comp g = f) : g = rangeRestrict f :=
  (range f).subtype_comp_eq_iff.mp (hg.trans (subtype_comp_rangeRestrict f).symm)

end Flat

end Coalgebra.RightComoduleHom
