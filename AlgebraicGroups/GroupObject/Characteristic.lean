/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Characteristic subgroup objects

This file defines characteristic monomorphisms of group objects: every automorphism of the
ambient group object restricts to an automorphism of the subgroup object.
-/

public section

open CategoryTheory

universe v u

namespace CategoryTheory.IsMonHom

/-- A monic morphism of group objects is characteristic if every automorphism of the ambient
group object restricts to an automorphism of its source. -/
class Characteristic
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {H G : C} [GrpObj H] [GrpObj G]
    (i : H ⟶ G) [IsMonHom i] [Mono i] : Prop where
  lift (e : Grp.mk G ≅ Grp.mk G) :
    ∃ eH : Grp.mk H ≅ Grp.mk H,
      eH.hom.hom.hom ≫ i = i ≫ e.hom.hom.hom

namespace Characteristic

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H G : C} [GrpObj H] [GrpObj G]
variable (i : H ⟶ G) [IsMonHom i] [Mono i] [Characteristic i]

/-- The chosen restriction of an ambient automorphism along a characteristic monomorphism. -/
noncomputable def liftIso (e : Grp.mk G ≅ Grp.mk G) : Grp.mk H ≅ Grp.mk H :=
  (Characteristic.lift (i := i) e).choose

/-- The chosen restricted automorphism commutes with the characteristic monomorphism. -/
theorem liftIso_hom_comp (e : Grp.mk G ≅ Grp.mk G) :
    (liftIso i e).hom.hom.hom ≫ i = i ≫ e.hom.hom.hom :=
  (Characteristic.lift (i := i) e).choose_spec

/-- A restricted ambient automorphism is unique. -/
theorem liftIso_unique (e : Grp.mk G ≅ Grp.mk G) (eH : Grp.mk H ≅ Grp.mk H)
    (h : eH.hom.hom.hom ≫ i = i ≫ e.hom.hom.hom) :
    liftIso i e = eH := by
  apply Iso.ext
  ext
  apply (cancel_mono i).mp
  rw [liftIso_hom_comp, h]

/-- Restricting the identity automorphism gives the identity automorphism. -/
@[simp]
theorem liftIso_refl : liftIso i (Iso.refl (Grp.mk G)) = Iso.refl (Grp.mk H) := by
  apply liftIso_unique i
  simp

end Characteristic

end CategoryTheory.IsMonHom
