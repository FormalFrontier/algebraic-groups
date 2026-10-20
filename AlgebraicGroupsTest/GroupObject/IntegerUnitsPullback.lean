/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.PullbackMonoid
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Algebra.Group.Units.Defs

import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import Mathlib.Algebra.Group.Int.Units

/-!
# The first-coordinate unit pullback on integer units

The square with source `ℤˣ × ℤˣ`, target `ℤˣ`, apex `ℤˣ`, first-coordinate
map, inclusion `u ↦ (1, u)`, and the unique map to the tensor unit is a
pullback. Its lift sends a cone element to the second coordinate. The induced
monoid and group structures are stored on the supplied apex. The negative unit
is different from the induced identity, so this example is not a singleton.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace IntegerUnitsPullback

private abbrev U := ℤˣ
private abbrev G := U × U

private noncomputable instance sourceGroup : GrpObj G :=
  (GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of G)).grp

private noncomputable instance targetMonoid : MonObj U :=
  (MonTypeEquivalenceMon.inverse.obj (MonCat.of U)).mon

private def first : G ⟶ U := ↾Prod.fst
private def inclusion : U ⟶ G := ↾fun u => (1, u)
private def projection : U ⟶ 𝟙_ (Type) := toUnit U

private instance first_isMonHom : IsMonHom first where
  one_hom := by
    ext : 1
    rfl
  mul_hom := by
    ext : 1
    rfl

/-- The lift on a cone is its second coordinate. -/
private def coneLift (T : Type) (a : T ⟶ G) : T ⟶ U := ↾fun t => (a t).2

/-- Cone compatibility says that the first coordinate is one. -/
private theorem coneLift_inclusion (T : Type) (a : T ⟶ G)
    (b : T ⟶ 𝟙_ (Type)) (w : a ≫ first = b ≫ η[U]) :
    coneLift T a ≫ inclusion = a := by
  refine ConcreteCategory.hom_ext _ _ (fun t => ?_)
  have h : (a t).1 = 1 := by
    have h := ConcreteCategory.congr_hom w t
    simp only [ConcreteCategory.coe_comp] at h
    exact h
  exact Prod.ext h.symm rfl

/-- The other lift equation holds because the tensor unit is terminal. -/
private theorem coneLift_projection (T : Type) (a : T ⟶ G)
    (b : T ⟶ 𝟙_ (Type)) : coneLift T a ≫ projection = b := by
  exact Subsingleton.elim _ _

/-- The inclusion's second coordinate makes the lift unique. -/
private theorem coneLift_unique (T : Type) (a : T ⟶ G) (n : T ⟶ U)
    (hn : n ≫ inclusion = a) : n = coneLift T a := by
  refine ConcreteCategory.hom_ext _ _ (fun t => ?_)
  exact congrArg Prod.snd (ConcreteCategory.congr_hom hn t)

/-- The concrete square, with lift and uniqueness characterized above. -/
private theorem square : IsPullback inclusion projection first η[U] := by
  have w : inclusion ≫ first = projection ≫ η[U] := by
    ext : 1
    rfl
  exact IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk w
      (fun s => coneLift s.pt s.fst)
      (fun s => coneLift_inclusion s.pt s.fst s.snd s.condition)
      (fun s => coneLift_projection s.pt s.fst s.snd)
      (fun s n hn _ => coneLift_unique s.pt s.fst n hn))

/-- The monoid structure produced by the public construction on the original apex,
stored as a value rather than registered as an instance. -/
@[expose, instance_reducible]
private noncomputable def inducedMonoid : MonObj ℤˣ :=
  MonObj.ofUnitPullback first inclusion projection square

/-- The group structure produced by the composed public construction on the same apex,
stored as a value rather than registered as an instance. -/
@[expose, instance_reducible]
private noncomputable def inducedGroup : GrpObj ℤˣ :=
  GrpObj.ofUnitPullback first inclusion projection square

/-- The group construction has exactly the separately stored monoid structure. -/
private theorem inducedGroup_toMonObj : inducedGroup.toMonObj = inducedMonoid :=
  GrpObj.ofUnitPullback_toMonObj first inclusion projection square

/-- The induced identity is the ordinary positive integer unit. -/
private theorem inducedMonoid_one : inducedMonoid.one PUnit.unit = (1 : ℤˣ) := by
  have h : inclusion (inducedMonoid.one PUnit.unit) = (1 : G) :=
    ConcreteCategory.congr_hom
      (MonObj.ofUnitPullback_one_comp_i first inclusion projection square) PUnit.unit
  exact congrArg Prod.snd h

private def negativePoint : U := -1

/-- The original negative unit survives as a nonidentity point of the induced monoid. -/
private theorem negativePoint_ne_induced_one :
    (-1 : ℤˣ) ≠ inducedMonoid.one PUnit.unit := by
  change negativePoint ≠ inducedMonoid.one PUnit.unit
  rw [inducedMonoid_one]
  intro h
  have h' : (-1 : ℤ) = 1 := congrArg Units.val h
  cases h'

end IntegerUnitsPullback
