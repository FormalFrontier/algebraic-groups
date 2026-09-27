/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.SplitKernelProduct
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGroupsTest.SplitKernelProduct

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {N G Q T : C} [GrpObj G] [GrpObj Q]
  (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q] (e : Q ⟶ G)
  (hN : IsPullback i (toUnit N) q η[Q]) (he : e ≫ q = 𝟙 Q)

example (f : T ⟶ N) (g : T ⟶ Q) :
    lift f g ≫ (splitKernelProductIso i q e hN he).hom =
      (g ≫ e) * (f ≫ i) := by
  simp [splitKernelProductIso_hom, MonObj.comp_mul]

example (f : T ⟶ G) :
    (f ≫ (splitKernelProductIso i q e hN he).inv ≫ fst N Q) ≫ i =
      (f ≫ q ≫ e)⁻¹ * f := by
  simp [Category.assoc, MonObj.comp_mul, GrpObj.comp_inv]

example (f : T ⟶ G) :
    f ≫ (splitKernelProductIso i q e hN he).inv ≫ snd N Q = f ≫ q := by
  simp

private noncomputable instance : GrpObj (Multiplicative ℤ) :=
  (GrpTypeEquivalenceGrp.inverse.obj (GrpCat.of (Multiplicative ℤ))).grp

private instance : GrpObj PUnit.{1} :=
  GrpObj.instTensorUnit (C := Type)

private def terminalSection : PUnit.{1} ⟶ Multiplicative ℤ :=
  ↾fun _ => Multiplicative.ofAdd (1 : ℤ)

private theorem terminalSection_section :
    terminalSection ≫ toUnit (Multiplicative ℤ) = 𝟙 PUnit.{1} := by
  ext

private theorem terminalSection_not_multiplicative : ¬ IsMonHom terminalSection := by
  intro h
  have : IsMonHom terminalSection := h
  have hOne := congrArg (fun f : PUnit.{1} ⟶ Multiplicative ℤ => f PUnit.unit)
    (IsMonHom.one_hom terminalSection)
  change Multiplicative.ofAdd (1 : ℤ) = Multiplicative.ofAdd (0 : ℤ) at hOne
  have hAbsurd : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd hOne
  omega

private theorem terminalKernelSquare :
    IsPullback (𝟙 (Multiplicative ℤ)) (toUnit (Multiplicative ℤ))
      (toUnit (Multiplicative ℤ)) η[PUnit.{1}] := by
  have hη : (η[PUnit.{1}] : PUnit.{1} ⟶ PUnit.{1}) = 𝟙 PUnit.{1} := by
    ext
  rw [hη]
  exact IsPullback.of_id_fst

noncomputable example : (Multiplicative ℤ) ⊗ PUnit.{1} ≅ Multiplicative ℤ :=
  splitKernelProductIso (𝟙 (Multiplicative ℤ)) (toUnit (Multiplicative ℤ))
    terminalSection terminalKernelSquare terminalSection_section

example : ¬ IsMonHom terminalSection := terminalSection_not_multiplicative

example (n : Multiplicative ℤ) :
    (splitKernelProductIso (𝟙 (Multiplicative ℤ)) (toUnit (Multiplicative ℤ))
      terminalSection terminalKernelSquare terminalSection_section).hom (n, PUnit.unit) =
        Multiplicative.ofAdd (1 : ℤ) * n := by
  rw [splitKernelProductIso_hom]
  rfl

end AlgebraicGroupsTest.SplitKernelProduct
