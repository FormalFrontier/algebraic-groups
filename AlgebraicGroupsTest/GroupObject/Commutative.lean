/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupObject.Commutative
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
import Mathlib.Logic.Equiv.Basic

/-!
# Commutative and noncommutative group objects in types

The additive integers, written multiplicatively, give a commutative group object via Mathlib's
conversion from `CommGrpCat`. Permutations of three elements give a group object via the
conversion from `GrpCat`; the overlapping swaps `(0 1)` and `(1 2)` witness both failure of
commutativity and failure of inversion to preserve multiplication. The one-element group `PUnit`
gives a commutative boundary case through the same conversion.

The structures and model proofs use the conversion functors and the defining equations of
`IsCommMonObj` and `IsMonHom`, independently of the inversion criterion.

## References

* Mathlib, `Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_` and
  `Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp`, for the conversion functors.
* Mathlib, `Mathlib.Algebra.Group.End` and `Mathlib.Logic.Equiv.Basic`, for permutation groups
  and swaps.
-/

namespace CategoryTheory

private noncomputable abbrev integerGroup : CommGrp (Type) :=
  CommGrpTypeEquivalenceCommGrp.inverse.obj (CommGrpCat.of (Multiplicative ℤ))

private noncomputable def integerGroupObj : GrpObj integerGroup.X := integerGroup.grp

private theorem integerGroup_comm : IsCommMonObj integerGroup.X := integerGroup.comm

-- This is the stock forward instance, not an application of the equivalence.
private theorem integerGroup_inv_isMonHom :
    IsMonHom (GrpObj.inv (X := integerGroup.X)) := inferInstance

private noncomputable abbrev permutationGroup : Grp (Type) :=
  GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of (Equiv.Perm (Fin 3)))

private noncomputable def permutationGroupObj : GrpObj permutationGroup.X :=
  permutationGroup.grp

private abbrev swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private abbrev swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private theorem swaps_not_commute : swap01 * swap12 ≠ swap12 * swap01 := by
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) h
  change (1 : Fin 3) = 2 at h0
  exact (by decide : (1 : Fin 3) ≠ 2) h0

private theorem permutationGroup_not_comm : ¬ IsCommMonObj permutationGroup.X := by
  intro h
  letI := h
  have hmul := ConcreteCategory.congr_hom (CC := fun X ↦ X)
    (IsCommMonObj.mul_comm permutationGroup.X) (swap01, swap12)
  change swap12 * swap01 = swap01 * swap12 at hmul
  exact swaps_not_commute hmul.symm

private theorem permutationGroup_inv_not_isMonHom :
    ¬ IsMonHom (GrpObj.inv (X := permutationGroup.X)) := by
  intro h
  letI := h
  have hmul := ConcreteCategory.congr_hom (CC := fun X ↦ X)
    (IsMonHom.mul_hom (GrpObj.inv (X := permutationGroup.X))) (swap01, swap12)
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) hmul
  change (2 : Fin 3) = 1 at h0
  exact (by decide : (2 : Fin 3) ≠ 1) h0

private noncomputable abbrev convertedCommGrp : CommGrp (Type) :=
  CommGrpTypeEquivalenceCommGrp.inverse.obj (CommGrpCat.of PUnit)

private theorem convertedCommGrp_comm : IsCommMonObj convertedCommGrp.X :=
  convertedCommGrp.comm

private theorem convertedCommGrp_inv_isMonHom :
    IsMonHom (GrpObj.inv (X := convertedCommGrp.X)) := inferInstance

-- The criterion recovers commutativity from the independently supplied stock inverse morphism.
private theorem integerGroup_comm_via_inv : IsCommMonObj integerGroup.X :=
  (isCommMonObj_iff_isMonHom_inv integerGroup.X).2 integerGroup_inv_isMonHom

end CategoryTheory
