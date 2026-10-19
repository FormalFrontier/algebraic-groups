/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.KernelTorsor
public import AlgebraicGroups.GroupObject.SplitKernelSemidirect
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Conjugation and twisted multiplication of a split kernel

Conjugation restricts to the kernel pullback even for a nonmultiplicative
section; at a fixed section value it preserves kernel multiplication and
inversion when the kernel inclusion is multiplicative. The action laws and
the section-first twisted multiplication additionally require a multiplicative
section. For `H = Equiv.Perm (Fin 3)`, the diagonal section of the second
projection `H × H ⟶ H` is multiplicative, yet the underlying isomorphism
`(n, a) ↦ (a * n, a)` does not preserve componentwise multiplication: two
noncommuting swaps detect the nontrivial conjugation. Its twisted product
instead uses conjugation by the inverse of the second section value.

The same projection also has a fibre over a nonidentity point obtained from its
kernel by right translation by an ordinary, nonmultiplicative point. Its pullback
property is checked directly in `Type`; the two swaps distinguish right translation
from left multiplication. Postcomposing this same projection with the canonical
map from permutations to `Function.End (Fin 3)` retains its kernel and chosen
point, and instantiates the monoid-target chosen-lift statement. The target is
the full composition monoid, not just its units: a constant transformation is
not a unit.

## References

* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` (group-object
  conjugation), `Mathlib.CategoryTheory.Limits.Types.Pullbacks` (pullbacks in
  `Type`), `Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp` (group objects
  in `Type`), `GrpObj.mulRight` (right translation), and
  `Mathlib.GroupTheory.Perm.Fin` (finite permutation groups),
  `Equiv.Perm.equivUnitsEnd` and `Units.coeHom` (the canonical map to the full
  transformation monoid), and `MonTypeEquivalenceMon.inverse` (monoid objects
  in `Type`).
-/

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

/-- The section-first product identifies twisted multiplication with multiplication in the group. -/
public theorem _root_.CategoryTheory.splitKernelProductIso_lift_mul
    [GrpObj N] [IsMonHom i] [IsMonHom e]
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

private def kernelFibrePoint : 𝟙_ (Type) ⟶ DoubleH :=
  ↾fun _ ↦ (firstSwap, secondSwap)

private theorem kernelFibre_mulRight_value (n : H) :
    (kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom) n =
      (n * firstSwap, secondSwap) := by
  change (n * firstSwap, (1 : H) * secondSwap) = _
  exact Prod.ext rfl (_root_.one_mul secondSwap)

private theorem kernelFibre_mulRight_square :
    IsPullback (kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom)
      (toUnit H) quotient (kernelFibrePoint ≫ quotient) := by
  apply (Limits.Types.isPullback_iff
    (kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom)
    quotient (toUnit H) (kernelFibrePoint ≫ quotient)).2
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro n
    change ((kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom) n).2 = secondSwap
    exact congrArg Prod.snd (kernelFibre_mulRight_value n)
  · intro first second h
    have hfirst := congrArg Prod.fst h.1
    rw [kernelFibre_mulRight_value, kernelFibre_mulRight_value] at hfirst
    exact mul_right_cancel hfirst
  · intro pair point h
    refine ⟨pair.1 * firstSwap⁻¹, ?_, ?_⟩
    · rw [kernelFibre_mulRight_value]
      change pair.2 = secondSwap at h
      exact Prod.ext (_root_.inv_mul_cancel_right pair.1 firstSwap) h.symm
    · rfl

private theorem kernelFibre_mulRight_order :
    ((kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom) secondSwap).1
        (0 : Fin 3) = 2 ∧
      (kernelFibrePoint PUnit.unit * kernelIncl secondSwap).1 (0 : Fin 3) = 1 := by
  rw [kernelFibre_mulRight_value]
  change (secondSwap * firstSwap) (0 : Fin 3) = 2 ∧
    (firstSwap * secondSwap) (0 : Fin 3) = 1
  decide

private theorem kernelFibrePoint_properties :
    (kernelFibrePoint ≫ quotient) PUnit.unit = secondSwap ∧
      kernelFibrePoint ≫ quotient ≠ η[H] ∧ ¬ IsMonHom kernelFibrePoint := by
  have hb : secondSwap ≠ (1 : H) := by decide
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    exact hb (ConcreteCategory.congr_hom h PUnit.unit)
  · intro hg
    have : IsMonHom kernelFibrePoint := hg
    have hunit : (firstSwap, secondSwap) = ((1 : H), (1 : H)) :=
      ConcreteCategory.congr_hom (IsMonHom.one_hom kernelFibrePoint) PUnit.unit
    exact hb (congrArg Prod.snd hunit)

example :
    IsPullback (i ≫ (GrpObj.mulRight η[G]).hom) (toUnit N) q (η[G] ≫ q) := by
  simpa only [GrpObj.mulRight_one, Iso.refl_hom, Category.comp_id,
    IsMonHom.one_hom] using hN

private theorem kernelFibre_isPullback :
    IsPullback (kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom)
      (toUnit H) quotient (kernelFibrePoint ≫ quotient) :=
  GrpObj.isPullback_kernel_mulRight kernelIncl quotient kernelSquare kernelFibrePoint

-- Capture the native composition dictionary before installing its internal monoid object.
private abbrev transformationMonCat : MonCat := MonCat.of (Function.End (Fin 3))

private noncomputable instance : MonObj (Function.End (Fin 3)) :=
  (MonTypeEquivalenceMon.inverse.obj transformationMonCat).mon

private noncomputable abbrev transformationQuotient : DoubleH ⟶ Function.End (Fin 3) :=
  quotient ≫
    (MonTypeEquivalenceMon.inverse.map
      (MonCat.ofHom ((Units.coeHom (Function.End (Fin 3))).comp
        Equiv.Perm.equivUnitsEnd.toMonoidHom))).hom

private instance : IsMonHom transformationQuotient := by
  -- Check the native arrow laws through the stored map's permutation applications.
  refine { one_hom := ?_, mul_hom := ?_ }
  · apply ConcreteCategory.hom_ext
    intro point
    funext j
    change (quotient (η[DoubleH] point)) j = j
    have h := ConcreteCategory.congr_hom (IsMonHom.one_hom quotient) point
    exact congrArg (fun p : H ↦ p j) h
  · apply ConcreteCategory.hom_ext
    intro pair
    funext j
    change (quotient (μ[DoubleH] pair)) j = (quotient pair.1) ((quotient pair.2) j)
    have h := ConcreteCategory.congr_hom (IsMonHom.mul_hom quotient) pair
    exact congrArg (fun p : H ↦ p j) h

private theorem transformationKernelSquare :
    IsPullback kernelIncl (toUnit H) transformationQuotient η[Function.End (Fin 3)] := by
  have hkernel :=
    (Limits.Types.isPullback_iff kernelIncl quotient (toUnit H) η[H]).1 kernelSquare
  apply (Limits.Types.isPullback_iff kernelIncl transformationQuotient
    (toUnit H) η[Function.End (Fin 3)]).2
  refine ⟨?_, hkernel.2.1, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro n
    rfl
  · intro pair point h
    apply hkernel.2.2 pair point
    apply Equiv.coe_fn_injective
    exact h

private theorem transformationFibrePoint_ne_unit :
    kernelFibrePoint ≫ transformationQuotient ≠ η[Function.End (Fin 3)] := by
  intro h
  apply kernelFibrePoint_properties.2.1
  apply ConcreteCategory.hom_ext
  intro point
  apply Equiv.coe_fn_injective
  exact ConcreteCategory.congr_hom h point

private theorem constant_transformation_not_isUnit :
    ¬ @IsUnit (Function.End (Fin 3)) transformationMonCat.str
      (fun _ : Fin 3 ↦ (0 : Fin 3)) := by
  rintro ⟨unit, hunit⟩
  have h := congrArg (fun f : Function.End (Fin 3) ↦ f 1) unit.val_inv
  change unit.val (unit.inv 1) = (1 : Fin 3) at h
  rw [hunit] at h
  exact (by decide : (0 : Fin 3) ≠ 1) h

private theorem transformationFibre_isPullback :
    IsPullback (kernelIncl ≫ (GrpObj.mulRight kernelFibrePoint).hom)
      (toUnit H) transformationQuotient (kernelFibrePoint ≫ transformationQuotient) :=
  GrpObj.isPullback_kernel_mulRight kernelIncl transformationQuotient
    transformationKernelSquare kernelFibrePoint

end AlgebraicGroupsTest.SplitKernelSemidirect
