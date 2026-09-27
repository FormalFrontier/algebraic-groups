/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.SplitKernelSemidirect
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.GroupTheory.Perm.Fin

public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGroupsTest.SplitKernelSemidirect

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {N G Q T : C} [GrpObj G] [GrpObj Q]
  (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q] (e : Q ⟶ G)
  (hN : IsPullback i (toUnit N) q η[Q]) (he : e ≫ q = 𝟙 Q)

example : splitKernelConj i q e hN he ≫ i = (e ⊗ₘ i) ≫ GrpObj.conj G :=
  splitKernelConj_comp_i i q e hN he

example (a : T ⟶ Q) (n : T ⟶ N) :
    (lift a n ≫ splitKernelConj i q e hN he) ≫ i =
      (a ≫ e) * (n ≫ i) * (a ≫ e)⁻¹ :=
  splitKernelConj_lift_comp_i i q e hN he a n

example [GrpObj N] [IsMonHom i] (a : T ⟶ Q) (n n' : T ⟶ N) :
    lift a (n * n') ≫ splitKernelConj i q e hN he =
      (lift a n ≫ splitKernelConj i q e hN he) *
        (lift a n' ≫ splitKernelConj i q e hN he) :=
  splitKernelConj_map_mul i q e hN he a n n'

example [GrpObj N] [IsMonHom i] (a : T ⟶ Q) (n : T ⟶ N) :
    lift a n⁻¹ ≫ splitKernelConj i q e hN he =
      (lift a n ≫ splitKernelConj i q e hN he)⁻¹ :=
  splitKernelConj_map_inv i q e hN he a n

example [IsMonHom e] (n : T ⟶ N) :
    lift (toUnit T ≫ η[Q]) n ≫ splitKernelConj i q e hN he = n :=
  splitKernelConj_one i q e hN he n

example [IsMonHom e] (a a' : T ⟶ Q) (n : T ⟶ N) :
    lift (a * a') n ≫ splitKernelConj i q e hN he =
      lift a (lift a' n ≫ splitKernelConj i q e hN he) ≫
        splitKernelConj i q e hN he :=
  splitKernelConj_mul i q e hN he a a' n

example [GrpObj N] [IsMonHom i] [IsMonHom e]
    (n n' : T ⟶ N) (a a' : T ⟶ Q) :
    lift ((lift (a'⁻¹) n ≫ splitKernelConj i q e hN he) * n') (a * a') ≫
        (splitKernelProductIso i q e hN he).hom =
      (lift n a ≫ (splitKernelProductIso i q e hN he).hom) *
        (lift n' a' ≫ (splitKernelProductIso i q e hN he).hom) :=
  splitKernelProductIso_mul_lift i q e hN he n n' a a'

example [GrpObj N] [IsMonHom i] [IsMonHom e] :
    splitKernelTwistedMul i q e hN he ≫
        (splitKernelProductIso i q e hN he).hom =
      ((splitKernelProductIso i q e hN he).hom ⊗ₘ
        (splitKernelProductIso i q e hN he).hom) ≫ μ[G] :=
  splitKernelTwistedMul_comp_hom i q e hN he

private abbrev H := Equiv.Perm (Fin 3)
private abbrev DoubleH := H × H

private noncomputable instance : GrpObj H :=
  (GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of H)).grp

private noncomputable instance : GrpObj DoubleH :=
  GrpObj.tensorObj.instTensorObj (G := H) (H := H)

private noncomputable def kernelIncl : H ⟶ DoubleH := lift (𝟙 H) (toUnit H ≫ η[H])
private def quotient : DoubleH ⟶ H := snd H H
private def diagonal : H ⟶ DoubleH := lift (𝟙 H) (𝟙 H)

private instance : IsMonHom kernelIncl := by
  unfold kernelIncl
  infer_instance

private instance : IsMonHom quotient := by
  unfold quotient
  infer_instance

private instance : IsMonHom diagonal := by
  unfold diagonal
  infer_instance

private theorem diagonal_section : diagonal ≫ quotient = 𝟙 H := by
  simp [diagonal, quotient]

private theorem kernelSquare :
    IsPullback kernelIncl (toUnit H) quotient η[H] := by
  apply (Limits.Types.isPullback_iff kernelIncl quotient (toUnit H) η[H]).2
  refine ⟨?_, ?_, ?_⟩
  · simp [kernelIncl, quotient]
  · intro first second h
    exact congrArg Prod.fst h.1
  · intro pair point h
    refine ⟨pair.1, ?_, ?_⟩
    · exact Prod.ext rfl (by change pair.2 = 1 at h; exact h.symm)
    · rfl

private def firstSwap : H := Equiv.swap (0 : Fin 3) 1
private def secondSwap : H := Equiv.swap (1 : Fin 3) 2

private theorem swaps_do_not_commute : firstSwap * secondSwap ≠ secondSwap * firstSwap := by
  decide

noncomputable example : H ⊗ H ≅ DoubleH :=
  splitKernelProductIso kernelIncl quotient diagonal kernelSquare diagonal_section

private theorem forward_value (n a : H) :
    (splitKernelProductIso kernelIncl quotient diagonal kernelSquare diagonal_section).hom
      (n, a) = (a * n, a) := by
  rw [splitKernelProductIso_hom]
  rfl

example :
    (splitKernelProductIso kernelIncl quotient diagonal kernelSquare diagonal_section).hom
        (firstSwap, secondSwap) ≠
      (splitKernelProductIso kernelIncl quotient diagonal kernelSquare diagonal_section).hom
          (firstSwap, 1) *
        (splitKernelProductIso kernelIncl quotient diagonal kernelSquare diagonal_section).hom
          (1, secondSwap) := by
  intro h
  have hfirst := congrArg Prod.fst h
  rw [forward_value, forward_value, forward_value] at hfirst
  change secondSwap * firstSwap = firstSwap * secondSwap at hfirst
  exact swaps_do_not_commute hfirst.symm

end AlgebraicGroupsTest.SplitKernelSemidirect
