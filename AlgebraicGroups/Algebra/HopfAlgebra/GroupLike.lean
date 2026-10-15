/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.GroupLike
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Group-like elements in the units of a Hopf algebra

Mathlib's homomorphism `GroupLike.toUnits` sends a group-like element to the unit
whose inverse is its antipode. This module characterizes that homomorphism:
it is injective, and a unit belongs to its range exactly when its underlying
value is group-like. It is natural with respect to bialgebra morphisms between
Hopf algebras.

The base is a commutative semiring, and the Hopf algebras are possibly
noncommutative semirings in independent universes. No nontriviality, finiteness
or additive-inverse hypothesis is required.

## References

The group-like carrier, group structure, antipode identities and `GroupLike.toUnits`
are due to Yaël Dillies and Michał Mrugała in Mathlib's
`Mathlib.RingTheory.Coalgebra.GroupLike`, `Mathlib.RingTheory.Bialgebra.GroupLike`
and `Mathlib.RingTheory.HopfAlgebra.GroupLike`. This module uses those constructions
without replacing them. Naturality compares the induced group-like map with
`Units.map` from Johan Commelin, Chris Hughes and Kevin Buzzard's
`Mathlib.Algebra.Group.Units.Hom`.
-/

@[expose] public section

universe u v w

namespace GroupLike

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [HopfAlgebra R A] [HopfAlgebra R B]

/-- Distinct group-like elements determine distinct units. -/
theorem toUnits_injective : Function.Injective (GroupLike.toUnits R (A := A)) := by
  intro a b h
  apply GroupLike.ext
  exact congrArg Units.val h

/-- A unit lies in the image of the group-like homomorphism exactly when its
underlying value is group-like. -/
@[simp]
theorem mem_range_toUnits (u : Aˣ) :
    u ∈ Set.range (GroupLike.toUnits R (A := A)) ↔ IsGroupLikeElem R (u : A) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.isGroupLikeElem_val
  · intro hu
    exact ⟨⟨(u : A), hu⟩, Units.ext rfl⟩

/-- Forming the unit of a group-like element commutes with a bialgebra morphism. -/
@[simp]
theorem toUnits_groupLikeMap (f : A →ₐc[R] B) (g : GroupLike R A) :
    GroupLike.toUnits R (f.groupLikeMap g) =
      Units.map f.toAlgHom.toMonoidHom (GroupLike.toUnits R g) := by
  apply Units.ext
  exact BialgHom.groupLikeMap_val f g

/-- The group-like inclusion into units is natural as an equality of monoid
homomorphisms. -/
theorem toUnits_comp_groupLikeMap (f : A →ₐc[R] B) :
    (GroupLike.toUnits R (A := B)).comp f.groupLikeMap =
      (Units.map f.toAlgHom.toMonoidHom).comp (GroupLike.toUnits R (A := A)) := by
  apply MonoidHom.ext
  intro g
  exact toUnits_groupLikeMap f g

end GroupLike
