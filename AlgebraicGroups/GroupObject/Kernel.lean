/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Group objects on monoid kernels

A monoid object supplied as the pullback of a monoid morphism from a group object
along the target unit carries a group structure extending its given monoid.
The original projection is a morphism of group objects and preserves inverses.
Only the supplied pullback is required; the target need not be a group object.

The construction lifts inverses in every source Hom group through the pullback,
using the kernel subgroup of the induced monoid homomorphism. The monoid structure
of the resulting group object is definitionally the originally supplied structure.

## References

The construction reuses Mathlib's `GrpObj.ofInvertible`, `Grp.homMk`, `inv_hom`,
Hom monoid/group structures and stock `MonoidHom.ker` with its inverse-closure
theorem, at revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
The related AlgebraicGroups kernel-translation API at revision
`b77a1a7981230883749191029b8790b63e2cb327` consumes a supplied kernel square.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

namespace CategoryTheory.GrpObj

/-- Extend the given monoid object on a kernel pullback to a group object.

The source is a group object, the target only a monoid object, and the pullback
square is supplied on the original carrier and original monoid dictionaries.
The construction lifts inverses in the source Hom groups through the pullback. -/
@[instance_reducible]
noncomputable def ofIsPullback
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {G H N : C} [GrpObj G] [MonObj H] [mN : MonObj N]
    (f : G ⟶ H) (i : N ⟶ G) [IsMonHom f] [IsMonHom i]
    (hPB : IsPullback i (toUnit N) f η[H]) : GrpObj N :=
  GrpObj.ofInvertible N (by
    intro T a
    letI : Group (T ⟶ G) := Hom.group (X := T) (G := G)
    let φ : (T ⟶ G) →* (T ⟶ H) := IsMonHom.monoidHom f T
    have ha : a ≫ i ∈ φ.ker := by
      change (a ≫ i) ≫ f = toUnit T ≫ η[H]
      rw [Category.assoc, hPB.w, comp_toUnit_assoc]
    -- The kernel is a subgroup of the source Hom group; H needs no inverse.
    have hinv : (a ≫ i)⁻¹ ≫ f = toUnit T ≫ η[H] :=
      MonoidHom.mem_ker.mp (φ.ker.inv_mem ha)
    let b : T ⟶ N := hPB.lift (a ≫ i)⁻¹ (toUnit T) hinv
    have hb : b ≫ i = (a ≫ i)⁻¹ := hPB.lift_fst _ _ _
    refine ⟨b, ?_, ?_⟩
    · apply hPB.hom_ext
      · rw [MonObj.mul_comp, hb, MonObj.one_comp, inv_mul_cancel]
      · exact isTerminalTensorUnit.hom_ext _ _
    · apply hPB.hom_ext
      · rw [MonObj.mul_comp, hb, MonObj.one_comp, mul_inv_cancel]
      · exact isTerminalTensorUnit.hom_ext _ _)

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G H N : C} [GrpObj G] [MonObj H] [mN : MonObj N]
  (f : G ⟶ H) (i : N ⟶ G) [IsMonHom f] [IsMonHom i]
  (hPB : IsPullback i (toUnit N) f η[H])

/-- The extension retains exactly the supplied monoid structure. -/
@[simp]
theorem ofIsPullback_toMonObj : (ofIsPullback f i hPB).toMonObj = mN := rfl

/-- The original kernel projection, regarded as a morphism of group objects. -/
noncomputable def ofIsPullbackHom :
    Grp.mk (grp := ofIsPullback f i hPB) N ⟶ Grp.mk G := by
  -- Retain the witness for the supplied monoid before installing its extension.
  have hi : IsMonHom i := inferInstance
  letI := ofIsPullback f i hPB
  haveI : IsMonHom i := by
    simpa only [ofIsPullback_toMonObj] using hi
  exact Grp.homMk i

/-- The group-object morphism has the original projection as its underlying map. -/
@[simp]
theorem ofIsPullbackHom_hom : (ofIsPullbackHom f i hPB).hom.hom = i := rfl

/-- The kernel projection intertwines the extended inverse and the source inverse. -/
theorem ofIsPullback_inv_comp :
    (ofIsPullback f i hPB).inv ≫ i = i ≫ ι[G] := by
  have hi : IsMonHom i := inferInstance
  let := ofIsPullback f i hPB
  have : IsMonHom i := by
    simpa only [ofIsPullback_toMonObj] using hi
  exact GrpObj.inv_hom i

end CategoryTheory.GrpObj
