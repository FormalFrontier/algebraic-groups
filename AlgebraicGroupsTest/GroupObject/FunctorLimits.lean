/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupObject.FunctorLimits
import AlgebraicGroups.GroupObject.CommutatorWord
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Group-object functoriality and global-section kernels

The identity functor on types commutes with forgetting internal groups to internal monoids,
and its induced functor on internal groups preserves binary products and zero morphisms.

For a group object over a scheme, contravariant global sections turn successive supplied-fan
commutator-word factorizations into antitone kernels of the original `appTop` maps. Only
positive-stage fans are limiting; the rank-zero fan and all supplied data remain unchanged.
No group structure on the underlying scheme or monoidality of the forgetful functor is used.

## References

* `AlgebraicGroups.GroupObject.CommutatorWord`, for supplied-fan word maps and range inclusion.
* Mathlib global sections, ring-homomorphism kernels and antitonicity from successive inclusions.
-/

open CategoryTheory

universe u v₁ v₂ u₁ u₂

example :
    (𝟭 (Type u)).mapGrp ⋙ Grp.forget₂Mon (Type u) =
      Grp.forget₂Mon (Type u) ⋙ (𝟭 (Type u)).mapMon :=
  Functor.mapGrp_comp_forget₂Mon (𝟭 (Type u))

example :
    Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (𝟭 (Type u)).mapGrp :=
  inferInstance

example {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] : F.mapGrp.PreservesZeroMorphisms := by
  infer_instance

example (G H : Grp (Type u)) :
    (𝟭 (Type u)).mapGrp.map (0 : G ⟶ H) = 0 := by
  apply Functor.PreservesZeroMorphisms.map_zero

section GlobalSectionKernels

open CategoryTheory.Limits AlgebraicGeometry CategoryTheory.GrpObj

example (S : Scheme.{u}) [CartesianMonoidalCategory (Over S)]
    (G : Over S) [GrpObj G]
    (P : (n : ℕ) → Fan (fun _ : Fin n × Fin 2 => G))
    (hP : ∀ n : ℕ, IsLimit (P (n + 1))) :
    Antitone (fun n : ℕ => RingHom.ker ((commutatorWord (P n)).left.appTop).hom) := by
  apply antitone_nat_of_succ_le
  intro n
  have hword : commutatorWord (P n) ∈
      Set.range (fun f : (P n).pt ⟶ (P n).pt => f ≫ commutatorWord (P n)) :=
    ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨e, he⟩ :=
    range_commutatorWord_subset (P n) (P (n + 1)) (hP n) (P n).pt hword
  have he' : e ≫ commutatorWord (P (n + 1)) = commutatorWord (P n) := he
  have hleft : e.left ≫ (commutatorWord (P (n + 1))).left =
      (commutatorWord (P n)).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left he'
  have hcomp : ((commutatorWord (P n)).left.appTop).hom =
      (e.left.appTop).hom.comp ((commutatorWord (P (n + 1))).left.appTop).hom := by
    rw [← hleft, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [hcomp, RingHom.comp_apply, hx, map_zero]

end GlobalSectionKernels
