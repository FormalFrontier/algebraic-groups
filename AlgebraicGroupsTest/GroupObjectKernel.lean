/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupObject.Kernel
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# An integer-product kernel with a monoid target

The first projection from a product of integer groups, followed by inclusion into
`WithZero`, has a proper nontrivial kernel and a target whose multiplication is
not cancellative. The original monoid dictionaries, morphisms and pullback are
supplied before applying the group-object constructor and its characteristic API.

The model uses Mathlib's Type/monoid/group equivalences and stock `MonoidHom.ker`
at revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

/-! The following single family is private. All premises precede uses of the
constructor. Only the inherited monoid on the kernel is converted to a
monoid object; the stock algebraic group is not converted to a group object. -/

namespace IntegerProduct

private abbrev A := Multiplicative ℤ
private abbrev G := A × A
private abbrev H := WithZero A

private def q : G →* H :=
  (WithZero.coeMonoidHom (α := A)).comp (MonoidHom.fst A A)

private abbrev N : Type := q.ker

private def a : A := Multiplicative.ofAdd (1 : ℤ)

private theorem a_ne_one : a ≠ 1 := by
  intro h
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrArg Multiplicative.toAdd h)

private theorem inside_mem : (1, a) ∈ q.ker := rfl

private theorem outside_not_mem : (a, 1) ∉ q.ker := by
  intro h
  apply a_ne_one
  exact WithZero.coe_inj.mp h

private theorem q_nonconstant : q (1, 1) ≠ q (a, 1) := by
  intro h
  exact outside_not_mem h.symm

private theorem kernel_ne_top : q.ker ≠ ⊤ := by
  intro h
  apply outside_not_mem
  rw [h]
  trivial

private def nPoint : N := ⟨(1, a), inside_mem⟩

private theorem nPoint_ne_one : nPoint ≠ 1 := by
  intro h
  exact a_ne_one (congrArg (fun n : N => n.val.2) h)

private theorem target_zero_ne_one : (0 : H) ≠ 1 := zero_ne_one

-- Cancellation fails for the ORIGINAL multiplication, so that multiplication
-- cannot be the multiplication of a group on H.
private theorem target_not_left_cancel :
    ¬ (∀ x y z : H, x * y = x * z → y = z) := by
  intro h
  exact target_zero_ne_one (h 0 0 1 (by rw [zero_mul, zero_mul]))

-- Freeze the bundled objects and maps before installing any internal instances,
-- so later instance search cannot choose a round-trip algebraic dictionary.
private noncomputable def gMon : Mon (Type) :=
  MonTypeEquivalenceMon.inverse.obj (MonCat.of G)

private noncomputable def gGrp : Grp (Type) :=
  GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of G)

private noncomputable def hMon : Mon (Type) :=
  MonTypeEquivalenceMon.inverse.obj (MonCat.of H)

private noncomputable def nMon : Mon (Type) :=
  MonTypeEquivalenceMon.inverse.obj (MonCat.of N)

private noncomputable def qMon : gMon ⟶ hMon :=
  MonTypeEquivalenceMon.inverse.map (MonCat.ofHom q)

private noncomputable def inclusionMon : nMon ⟶ gMon :=
  MonTypeEquivalenceMon.inverse.map (MonCat.ofHom q.ker.subtype)

private noncomputable instance gGrpObj : GrpObj G := gGrp.grp
private noncomputable instance hMonObj : MonObj H := hMon.mon
private noncomputable instance nMonObj : MonObj N := nMon.mon

-- These reductions record the original dictionary VALUES, not merely carriers.
private theorem gGrp_toMonObj : gGrpObj.toMonObj = gMon.mon := rfl

private theorem hMon_mul (x y : H) : μ[H] (x, y) = x * y := rfl

private theorem nMon_one (u : PUnit) : η[N] u = (1 : N) := rfl

private theorem nMon_mul (x y : N) : μ[N] (x, y) = x * y := rfl

private noncomputable def f : G ⟶ H := qMon.hom

private noncomputable def i : N ⟶ G := inclusionMon.hom

-- Both are the original monoid-hom witnesses from the inverse functor's maps.
private instance f_isMonHom : IsMonHom f := qMon.isMonHom_hom

private instance i_isMonHom : IsMonHom i := inclusionMon.isMonHom_hom

private theorem f_apply (x : G) : f x = q x := rfl

private theorem i_apply (n : N) : i n = n.val := rfl

-- Independent Type-pullback criterion: subtype membership gives existence,
-- subtype extensionality uniqueness, and the PUnit leg is unique.
-- This proof uses neither the headline constructor nor a GrpObj N premise.
private theorem kernel_isPullback : IsPullback i (toUnit N) f η[H] := by
  apply (Limits.Types.isPullback_iff (t := i) (l := toUnit N) (r := f) (b := η[H])).2
  refine ⟨?_, ?_, ?_⟩
  · ext n
    exact n.property
  · intro x y h
    exact Subtype.ext h.1
  · intro x u hx
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    exact ConcreteCategory.congr_hom
      (isTerminalTensorUnit.hom_ext (toUnit N) (TypeCat.ofHom fun _ : N => u)) ⟨x, hx⟩

-- Uses of the headline and each bridge follow the independent premises.
@[instance_reducible]
private noncomputable def kernelGrp : GrpObj N :=
  GrpObj.ofIsPullback f i kernel_isPullback

private theorem kernelGrp_toMonObj : kernelGrp.toMonObj = nMonObj :=
  GrpObj.ofIsPullback_toMonObj f i kernel_isPullback

private noncomputable def kernelHom :
    Grp.mk (grp := kernelGrp) N ⟶ Grp.mk G :=
  GrpObj.ofIsPullbackHom f i kernel_isPullback

private theorem kernelHom_hom : kernelHom.hom.hom = i :=
  GrpObj.ofIsPullbackHom_hom f i kernel_isPullback

private theorem kernelGrp_inv_comp : kernelGrp.inv ≫ i = i ≫ ι[G] :=
  GrpObj.ofIsPullback_inv_comp f i kernel_isPullback

end IntegerProduct
